//! `air2lean`: prints the constraints a `rand_zkvm` chip enforces as Lean 4 definitions.
//!
//! The expressions are never restated by hand: each chip's `Air::eval` is run against Plonky3's
//! own symbolic builder (`p3_lookup::InteractionSymbolicBuilder`), and the recorded DAG is
//! translated node by node.
//!
//! * **Base constraints** become one `F` each, in the order `eval` asserted them.
//! * **Interactions** (global, then exclusive branches) become `Rand.Interaction` values.
//! * **Extension constraints** must be absent: `eval` of these chips asserts none (the LogUp
//!   gadget adds its own later, and those are the bus mechanism, covered by the bus-soundness
//!   assumption). Any present is an error.
//!
//! **Fail loudly.** Every leaf other than a current-row main column or a constant (next-row,
//! preprocessed, public, periodic, the row selectors), every bus the catalogue below does not
//! classify, every interaction shape the kind rules do not cover, and every local interaction is
//! an error naming the chip: a silently dropped term would make the Lean model weaker than the
//! AIR. Later chips extend the translator; they never get a default.
//!
//! **Sharing.** The DAG shares interior nodes through `Arc`s. A node referenced more than once
//! (counted over all roots of one Lean function) is emitted once as a `let`, keyed by its
//! `Arc` address; names are assigned in first-use post-order, so the output depends only on the
//! DAG's shape, never on the addresses. Leaves are printed inline.
//!
//! The output is deterministic: no timestamps, the header names only the circuits commit.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use p3_air::symbolic::{AirLayout, BaseEntry, BaseLeaf, SymbolicExpr, SymbolicExpression};
use p3_air::{Air, BaseAir};
use p3_field::extension::BinomialExtensionField;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_lookup::{InteractionSymbolicBuilder, LookupBus, PermutationCheckBus};
use p3_matrix::dense::RowMajorMatrix;
use rand_zkvm::asm::{ops::*, Assembler};
use rand_zkvm::emulator::execute;
use rand_zkvm::isa::{AluOp, BranchCond, Instr, Program};
use rand_zkvm::tables::{alu, bus, nibble, range, F};

/// The machine's challenge field (`rand_zkvm::machine::Challenge`).
type EF = BinomialExtensionField<F, 2>;
type Expr = SymbolicExpression<F>;
type Result<T> = std::result::Result<T, String>;

/// The circuits commit this exporter is built against, read from `SOURCES.toml` at compile time.
fn circuits_rev() -> Result<String> {
    const SOURCES: &str = include_str!("../../SOURCES.toml");
    let mut in_circuits = false;
    for line in SOURCES.lines() {
        let line = line.trim();
        if line.starts_with('[') {
            in_circuits = line == "[circuits]";
        } else if in_circuits && line.starts_with("rev") {
            let rev = line.split('"').nth(1).ok_or("SOURCES.toml: malformed circuits rev")?;
            return Ok(rev.to_string());
        }
    }
    Err("SOURCES.toml: no [circuits] rev".into())
}

/// Refuses to export from a checkout that is not at the pinned commit.
fn check_checkout(rev: &str) -> Result<()> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../third_party/zkp-circuits");
    let out = std::process::Command::new("git")
        .arg("-C").arg(&dir).args(["rev-parse", "HEAD"])
        .output().map_err(|e| format!("git rev-parse in {}: {e}", dir.display()))?;
    let head = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if head != rev {
        return Err(format!("{} is at {head:?}, SOURCES.toml pins {rev}; run scripts/fetch-sources.sh", dir.display()));
    }
    Ok(())
}

// ───────────────────────────────────────────────────────────── interaction kinds

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind { Lookup, Provide, Send, Receive }

impl Kind {
    fn lean(self) -> &'static str {
        match self { Kind::Lookup => ".lookup", Kind::Provide => ".provide", Kind::Send => ".send", Kind::Receive => ".receive" }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BusClass { Lookup, Permutation }

/// Every bus of `rand_zkvm::tables::bus`, classified by the type of its constant (so a bus that
/// changes type fails to compile here). A bus missing from this list is an export error.
fn bus_class(name: &str) -> Option<BusClass> {
    let lookups: [&LookupBus<'static>; 16] = [
        &bus::PROGRAM, &bus::PROGRAM_WORD, &bus::INPUT_DIGEST, &bus::INPUT_READ, &bus::PUBLIC_DIGEST,
        &bus::PUBLIC_READ, &bus::ALU, &bus::RANGE8, &bus::AND4, &bus::OR4, &bus::XOR4, &bus::POW2,
        &bus::POSEIDON2, &bus::KECCAK, &bus::SHA256, &bus::MODQ,
    ];
    let perms: [&PermutationCheckBus<'static>; 3] = [&bus::MEMORY, &bus::BLIND, &bus::MODQ_WIRE];
    if lookups.iter().any(|b| b.name() == name) { return Some(BusClass::Lookup); }
    if perms.iter().any(|b| b.name() == name) { return Some(BusClass::Permutation); }
    None
}

/// The symbolic builder records `(bus, fields, count, weight)` and not which bus method pushed
/// it, so the kind is recovered from what each method records (`p3-lookup-0.7.0/src/bus.rs`):
///
/// * `LookupBus::lookup_key(k, c)` pushes `c` with its declared weight (≥ 1 in this crate);
/// * `LookupBus::table_entry(k, n)` pushes `Count::provided(-n)`: weight 0, count `-n` — so the
///   count is a `Neg` node, or a folded constant when `n` is one;
/// * `PermutationCheckBus::send(f, c)` pushes `c`; `receive(f, c)` pushes `-c`.
///
/// On a permutation bus a `send` whose count is itself a negation is recorded identically to a
/// `receive`; the two are the same LogUp term, so reading it as a `receive` is exact.
/// Returns the kind and the count to emit (`provide`/`receive` carry the multiplicity, sign
/// removed).
fn classify(chip: &str, bus_name: &str, count: &Expr, weight: u32) -> Result<(Kind, Expr)> {
    let unneg = |e: &Expr| -> Option<Expr> {
        match e {
            SymbolicExpr::Neg { x, .. } => Some((**x).clone()),
            SymbolicExpr::Leaf(BaseLeaf::Constant(c)) => Some(SymbolicExpr::Leaf(BaseLeaf::Constant(-*c))),
            _ => None,
        }
    };
    match bus_class(bus_name) {
        None => Err(format!("{chip}: interaction on unknown bus {bus_name:?} (add it to bus_class)")),
        Some(BusClass::Lookup) if weight > 0 => Ok((Kind::Lookup, count.clone())),
        Some(BusClass::Lookup) => match unneg(count) {
            Some(n) => Ok((Kind::Provide, n)),
            None => Err(format!("{chip}: weight-0 interaction on lookup bus {bus_name:?} whose count is not a negation; not a table_entry")),
        },
        Some(BusClass::Permutation) => match count {
            SymbolicExpr::Neg { x, .. } => Ok((Kind::Receive, (**x).clone())),
            _ => Ok((Kind::Send, count.clone())),
        },
    }
}

// ───────────────────────────────────────────────────────────── symbolic capture

struct Interaction { bus: String, kind: Kind, tuple: Vec<Expr>, count: Expr }

struct Captured { width: usize, constraints: Vec<Expr>, interactions: Vec<Interaction> }

fn capture<A>(chip: &str, air: &A) -> Result<Captured>
where
    A: BaseAir<F> + Air<InteractionSymbolicBuilder<F, EF>>,
{
    let layout = AirLayout::from_air::<F>(air);
    let mut b = InteractionSymbolicBuilder::<F, EF>::new(layout);
    air.eval(&mut b);
    let ext = b.extension_constraints();
    if !ext.is_empty() {
        return Err(format!("{chip}: eval asserted {} extension constraint(s); not exported", ext.len()));
    }
    if !b.local_interactions().is_empty() {
        return Err(format!("{chip}: {} local interaction(s); the Lean model has no local bus", b.local_interactions().len()));
    }
    let mut interactions = Vec::new();
    for i in b.global_interactions() {
        let (kind, count) = classify(chip, &i.bus_name, &i.count, i.count_weight)?;
        interactions.push(Interaction { bus: i.bus_name.clone(), kind, tuple: i.fields.clone(), count });
    }
    // An exclusive group is one LogUp column whose numerator is Σ flag·count over its
    // branches; each branch is the interaction `(fields, flag·count)`.
    for g in b.exclusive_interactions() {
        for br in &g.branches {
            let gated = br.flag.clone() * br.count.clone();
            let (kind, count) = classify(chip, &g.bus_name, &gated, br.count_weight)?;
            interactions.push(Interaction { bus: g.bus_name.clone(), kind, tuple: br.fields.clone(), count });
        }
    }
    Ok(Captured { width: air.width(), constraints: b.base_constraints(), interactions })
}

// ───────────────────────────────────────────────────────────── Lean printing

/// Prints expressions of one Lean function, sharing interior nodes referenced more than once.
struct Printer<'a> {
    chip: &'a str,
    width: usize,
    refs: HashMap<*const Expr, usize>,
    names: HashMap<*const Expr, String>,
    lets: Vec<String>,
}

impl<'a> Printer<'a> {
    fn new(chip: &'a str, width: usize) -> Self {
        Self { chip, width, refs: HashMap::new(), names: HashMap::new(), lets: Vec::new() }
    }

    /// First pass: reference counts of every interior node reachable from `e`.
    fn count(&mut self, e: &Expr) {
        match e {
            SymbolicExpr::Leaf(_) => {}
            SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } | SymbolicExpr::Mul { x, y, .. } => {
                self.count_child(x);
                self.count_child(y);
            }
            SymbolicExpr::Neg { x, .. } => self.count_child(x),
        }
    }

    fn count_child(&mut self, a: &Arc<Expr>) {
        let n = self.refs.entry(Arc::as_ptr(a)).or_insert(0);
        *n += 1;
        if *n == 1 { self.count(a); }
    }

    fn leaf(&self, l: &BaseLeaf<F>) -> Result<String> {
        match l {
            BaseLeaf::Constant(c) => Ok(format!("({} : F)", c.as_canonical_u64())),
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset: 0 } if v.index < self.width => Ok(format!("m ⟨{}, by decide⟩", v.index)),
                _ => Err(format!("{}: untranslated leaf {:?} (entry {:?}, index {})", self.chip, l, v.entry, v.index)),
            },
            BaseLeaf::IsFirstRow | BaseLeaf::IsLastRow | BaseLeaf::IsTransition => {
                Err(format!("{}: untranslated leaf {:?} (row selector)", self.chip, l))
            }
        }
    }

    /// Second pass: the Lean term for `e`, pushing `let`s for shared children first.
    fn render(&mut self, e: &Expr) -> Result<String> {
        Ok(match e {
            SymbolicExpr::Leaf(l) => self.leaf(l)?,
            SymbolicExpr::Add { x, y, .. } => format!("({} + {})", self.child(x)?, self.child(y)?),
            SymbolicExpr::Sub { x, y, .. } => format!("({} - {})", self.child(x)?, self.child(y)?),
            SymbolicExpr::Mul { x, y, .. } => format!("({} * {})", self.child(x)?, self.child(y)?),
            SymbolicExpr::Neg { x, .. } => format!("(-{})", self.child(x)?),
        })
    }

    fn child(&mut self, a: &Arc<Expr>) -> Result<String> {
        if let SymbolicExpr::Leaf(l) = &**a { return self.leaf(l); }
        let k = Arc::as_ptr(a);
        if let Some(n) = self.names.get(&k) { return Ok(n.clone()); }
        let body = self.render(a)?;
        if self.refs.get(&k).copied().unwrap_or(0) < 2 { return Ok(body); }
        let name = format!("x{}", self.lets.len());
        self.lets.push(format!("  let {name} := {body}"));
        self.names.insert(k, name.clone());
        Ok(name)
    }
}

fn header(rev: &str) -> String {
    format!("-- GENERATED by exporter from zkp-circuits @{rev}. Do not edit.\n")
}

/// One Lean function `name (m : Fin width → F) : List ty := let …; [items]`.
fn lean_fn(out: &mut String, doc: &str, name: &str, ty: &str, width: usize, lets: &[String], items: &[String]) {
    writeln!(out, "/-- {doc} -/").unwrap();
    writeln!(out, "def {name} (m : Fin {width} → F) : List {ty} :=").unwrap();
    for l in lets { writeln!(out, "{l}").unwrap(); }
    if items.is_empty() {
        writeln!(out, "  []").unwrap();
    } else {
        for (i, it) in items.iter().enumerate() {
            let open = if i == 0 { "  [ " } else { "  , " };
            writeln!(out, "{open}{it}").unwrap();
        }
        writeln!(out, "  ]").unwrap();
    }
    out.push('\n');
}

/// The Lean module for one chip: `width`, `constraints`, `interactions`.
fn export_chip(rev: &str, chip: &str, namespace: &str, cap: &Captured) -> Result<String> {
    let mut out = header(rev);
    writeln!(out, "import Rand.Bus\n").unwrap();
    writeln!(out, "/-! The `{chip}` chip's base constraints and bus interactions, read off its `Air::eval`").unwrap();
    writeln!(out, "through Plonky3's symbolic builder: {} constraints, {} interactions. -/\n",
        cap.constraints.len(), cap.interactions.len()).unwrap();
    writeln!(out, "namespace {namespace}\n\nopen Rand\n").unwrap();
    writeln!(out, "/-- Main trace width. -/\ndef width : ℕ := {}\n", cap.width).unwrap();

    let mut p = Printer::new(chip, cap.width);
    for c in &cap.constraints { p.count(c); }
    let items = cap.constraints.iter().map(|c| p.render(c)).collect::<Result<Vec<_>>>()?;
    lean_fn(&mut out, "Every base constraint, in `eval` order; a row is accepted iff all are `0`.",
        "constraints", "F", cap.width, &p.lets, &items);

    let mut p = Printer::new(chip, cap.width);
    for i in &cap.interactions {
        for t in &i.tuple { p.count(t); }
        p.count(&i.count);
    }
    let mut items = Vec::new();
    for i in &cap.interactions {
        let tuple = i.tuple.iter().map(|t| p.render(t)).collect::<Result<Vec<_>>>()?;
        let count = p.render(&i.count)?;
        items.push(format!("{{ bus := {:?}, kind := {}, tuple := [{}], count := {} }}",
            i.bus, i.kind.lean(), tuple.join(", "), count));
    }
    lean_fn(&mut out, "Every bus interaction, in push order (global, then exclusive branches).",
        "interactions", "Interaction", cap.width, &p.lets, &items);
    writeln!(out, "end {namespace}").unwrap();
    Ok(out)
}

// ───────────────────────────────────────────────────────────── honest ALU rows

/// A small guest that runs every one of the 19 ALU ops, the M-extension on an ordinary pair and
/// on division by zero, and `Eq` through a `beq`.
fn alu_program() -> Program {
    let mut a = Assembler::new(0);
    type Op = fn(u32, u32, u32) -> Instr;
    let ops: [Op; 18] = [add, sub, and, or, xor, sll, srl, sra, slt, sltu, mul, mulh, mulhu, mulhsu, div, divu, rem, remu];
    for (x, y) in [(0x1234_5678, -7), (-7, 0)] {
        a.extend(li(5, x));
        a.extend(li(6, y));
        for f in ops { a.push(f(7, 5, 6)); }
    }
    a.branch(BranchCond::Eq, 5, 5, "eq");
    a.label("eq");
    a.extend(halt());
    a.assemble()
}

/// Rows of the real `alu_trace` for [`alu_program`]: every distinct real row in trace order,
/// then the first padding row. Checked here against the captured constraints before printing.
fn honest_rows(cap: &Captured) -> Result<Vec<Vec<u64>>> {
    let e = execute(&alu_program(), &[], &[], 10_000).map_err(|e| format!("alu program: {e:?}"))?;
    let n: usize = e.events.iter().map(|c| c.alu.len()).sum();
    let height = (n + 1).next_power_of_two();
    let mut rc = range::RangeCounts::default();
    let mut nc = nibble::NibbleCounts::default();
    let t: RowMajorMatrix<F> = alu::alu_trace(&e.events, height, &mut rc, &mut nc);
    let mut rows: Vec<Vec<u64>> = Vec::new();
    let mut padding = None;
    for r in t.values.chunks(alu::col::WIDTH) {
        let r: Vec<u64> = r.iter().map(|x| x.as_canonical_u64()).collect();
        if r[alu::col::IS_REAL] == 1 {
            if !rows.contains(&r) { rows.push(r); }
        } else if padding.is_none() {
            padding = Some(r);
        }
    }
    for op in AluOp::ALL {
        if !rows.iter().any(|r| r[alu::col::FLAG0 + op.code() as usize] == 1) {
            return Err(format!("alu program never runs {op:?}"));
        }
    }
    rows.push(padding.ok_or("alu trace has no padding row")?);
    for (k, r) in rows.iter().enumerate() {
        let vals: Vec<F> = r.iter().map(|&x| F::from_u64(x)).collect();
        for (j, c) in cap.constraints.iter().enumerate() {
            let v = eval(c, &vals, &mut HashMap::new());
            if v != F::ZERO { return Err(format!("honest row {k} fails constraint {j}")); }
        }
    }
    Ok(rows)
}

/// Evaluates a captured expression on one row (memoised by node, as the DAG is shared).
fn eval(e: &Expr, row: &[F], memo: &mut HashMap<*const Expr, F>) -> F {
    let child = |a: &Arc<Expr>, memo: &mut HashMap<*const Expr, F>| -> F {
        if let Some(v) = memo.get(&Arc::as_ptr(a)) { return *v; }
        let v = eval(a, row, memo);
        memo.insert(Arc::as_ptr(a), v);
        v
    };
    match e {
        SymbolicExpr::Leaf(BaseLeaf::Constant(c)) => *c,
        SymbolicExpr::Leaf(BaseLeaf::Variable(v)) => row[v.index],
        SymbolicExpr::Leaf(l) => panic!("eval: leaf {l:?}"),
        SymbolicExpr::Add { x, y, .. } => { let a = child(x, memo); a + child(y, memo) }
        SymbolicExpr::Sub { x, y, .. } => { let a = child(x, memo); a - child(y, memo) }
        SymbolicExpr::Mul { x, y, .. } => { let a = child(x, memo); a * child(y, memo) }
        SymbolicExpr::Neg { x, .. } => -child(x, memo),
    }
}

fn export_honest(rev: &str, cap: &Captured) -> Result<String> {
    let rows = honest_rows(cap)?;
    let mut out = header(rev);
    writeln!(out, "import Rand.Field\n").unwrap();
    writeln!(out, "/-! Rows of the real `alu_trace` on a small guest running all 19 ALU ops (every distinct").unwrap();
    writeln!(out, "real row in trace order, then one padding row): {} rows. -/\n", rows.len()).unwrap();
    writeln!(out, "namespace Rand.Generated.RV32.Alu\n\nopen Rand\n").unwrap();
    writeln!(out, "/-- A row from its 64 cells as canonical values. -/").unwrap();
    writeln!(out, "def row (l : List ℕ) : Fin {} → F := fun i => (l.getD i.val 0 : F)\n", alu::col::WIDTH).unwrap();
    writeln!(out, "/-- Honest rows produced by the Rust trace generator. -/").unwrap();
    writeln!(out, "def honestRows : List (Fin {} → F) :=", alu::col::WIDTH).unwrap();
    for (i, r) in rows.iter().enumerate() {
        let open = if i == 0 { "  [ " } else { "  , " };
        let cells: Vec<String> = r.iter().map(|x| x.to_string()).collect();
        writeln!(out, "{open}row [{}]", cells.join(", ")).unwrap();
    }
    writeln!(out, "  ]\n\nend Rand.Generated.RV32.Alu").unwrap();
    Ok(out)
}

// ───────────────────────────────────────────────────────────── fixed tables

fn canonical_rows(m: RowMajorMatrix<F>, width: usize, what: &str) -> Result<Vec<Vec<u64>>> {
    if m.width != width { return Err(format!("{what}: preprocessed width {} != {width}", m.width)); }
    Ok(m.values.chunks(width).map(|r| r.iter().map(|x| x.as_canonical_u64()).collect()).collect())
}

fn export_tables(rev: &str) -> Result<String> {
    use range::pre as rp;
    use nibble::pre as np;
    let r = <range::RangeAir as BaseAir<F>>::preprocessed_trace(&range::RangeAir).ok_or("range: no preprocessed trace")?;
    let r = canonical_rows(r, rp::WIDTH, "range")?;
    let n = <nibble::NibbleAir as BaseAir<F>>::preprocessed_trace(&nibble::NibbleAir).ok_or("nibble: no preprocessed trace")?;
    let n = canonical_rows(n, np::WIDTH, "nibble")?;
    let mut out = header(rev);
    writeln!(out, "import Mathlib.Data.Nat.Notation\n").unwrap();
    writeln!(out, "/-! The fixed tables' `preprocessed_trace`s, as canonical values. -/\n").unwrap();
    writeln!(out, "namespace Rand.Generated.RV32.Tables\n").unwrap();
    writeln!(out, "/-- `range.rs`: (A, POW2, IS_POW2) for each of the {} rows. -/", r.len()).unwrap();
    writeln!(out, "def range8Rows : List (ℕ × ℕ × ℕ) :=").unwrap();
    for (i, x) in r.iter().enumerate() {
        let open = if i == 0 { "  [ " } else { "  , " };
        writeln!(out, "{open}({}, {}, {})", x[rp::A], x[rp::POW2], x[rp::IS_POW2]).unwrap();
    }
    writeln!(out, "  ]\n").unwrap();
    writeln!(out, "/-- `nibble.rs`: (a, b, a AND b, a OR b, a XOR b) for each of the {} rows. -/", n.len()).unwrap();
    writeln!(out, "def nibbleRows : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=").unwrap();
    for (i, x) in n.iter().enumerate() {
        let open = if i == 0 { "  [ " } else { "  , " };
        writeln!(out, "{open}({}, {}, {}, {}, {})", x[np::A], x[np::B], x[np::AND], x[np::OR], x[np::XOR]).unwrap();
    }
    writeln!(out, "  ]\n\nend Rand.Generated.RV32.Tables").unwrap();
    Ok(out)
}

// ───────────────────────────────────────────────────────────── CLI

const USAGE: &str = "usage: air2lean <alu|alu-honest|tables> --out <file.lean>";

fn run(args: &[String]) -> Result<()> {
    let (cmd, out) = match args {
        [cmd, flag, out] if flag == "--out" => (cmd.as_str(), PathBuf::from(out)),
        _ => return Err(USAGE.into()),
    };
    let rev = circuits_rev()?;
    check_checkout(&rev)?;
    let text = match cmd {
        "alu" => export_chip(&rev, "alu", "Rand.Generated.RV32.Alu", &capture("alu", &alu::AluAir)?)?,
        "alu-honest" => export_honest(&rev, &capture("alu", &alu::AluAir)?)?,
        "tables" => export_tables(&rev)?,
        _ => return Err(USAGE.into()),
    };
    if let Some(dir) = out.parent() { std::fs::create_dir_all(dir).map_err(|e| e.to_string())?; }
    std::fs::write(&out, text).map_err(|e| format!("{}: {e}", out.display()))?;
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => { eprintln!("air2lean: {e}"); ExitCode::FAILURE }
    }
}

// ───────────────────────────────────────────────────────────── tests

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::{AirBuilder, WindowAccess};
    use p3_lookup::{Count, InteractionBuilder};

    /// A two-column toy AIR whose single constraint is selected by `MODE`.
    struct Toy<const MODE: u8>;
    impl<const MODE: u8, Fl> BaseAir<Fl> for Toy<MODE> { fn width(&self) -> usize { 2 } }
    impl<const MODE: u8, AB: AirBuilder + InteractionBuilder> Air<AB> for Toy<MODE> {
        fn eval(&self, b: &mut AB) {
            let m = b.main();
            let x: AB::Expr = m.current(0).unwrap().into();
            let y: AB::Expr = m.current(1).unwrap().into();
            match MODE {
                0 => { let n: AB::Expr = m.next(0).unwrap().into(); b.assert_zero(n - y); }
                1 => b.when_transition().assert_zero(x - y),
                2 => bus::RANGE8.lookup_key(b, [x], Count::bounded(y, 1)),
                3 => b.push_interaction("NOT_A_BUS", [x], Count::bounded(y, 1)),
                4 => b.push_interaction(bus::RANGE8.name(), [x], Count::bounded(y, 0)),
                5 => { bus::MEMORY.send(b, [x.clone()], Count::bounded(y.clone(), 1)); bus::MEMORY.receive(b, [x], Count::bounded(y, 1)); }
                6 => { bus::RANGE8.table_entry(b, [x.clone()], y); bus::RANGE8.table_entry(b, [x], AB::Expr::from_u32(3)); }
                _ => unreachable!(),
            }
        }
    }

    fn lean_of<const MODE: u8>() -> Result<String> {
        export_chip("REV", "toy", "Toy", &capture("toy", &Toy::<MODE>)?)
    }

    /// Review Focus 1: a next-row leaf is refused, never dropped.
    #[test]
    fn next_row_leaf_is_an_error() {
        let e = lean_of::<0>().unwrap_err();
        assert!(e.contains("toy") && e.contains("untranslated leaf") && e.contains("offset: 1"), "{e}");
    }

    #[test]
    fn transition_selector_is_an_error() {
        let e = lean_of::<1>().unwrap_err();
        assert!(e.contains("IsTransition"), "{e}");
    }

    #[test]
    fn unknown_bus_is_an_error() {
        assert!(lean_of::<3>().unwrap_err().contains("unknown bus"));
    }

    #[test]
    fn weight_zero_without_negation_is_an_error() {
        assert!(lean_of::<4>().unwrap_err().contains("not a table_entry"));
    }

    #[test]
    fn kinds_are_recovered() {
        assert!(lean_of::<2>().unwrap().contains(r#"{ bus := "RANGE8", kind := .lookup, tuple := [m ⟨0, by decide⟩], count := m ⟨1, by decide⟩ }"#));
        let s = lean_of::<5>().unwrap();
        assert!(s.contains(r#"kind := .send, tuple := [m ⟨0, by decide⟩], count := m ⟨1, by decide⟩"#), "{s}");
        assert!(s.contains(r#"kind := .receive, tuple := [m ⟨0, by decide⟩], count := m ⟨1, by decide⟩"#), "{s}");
        let s = lean_of::<6>().unwrap();
        assert!(s.contains(r#"kind := .provide, tuple := [m ⟨0, by decide⟩], count := m ⟨1, by decide⟩"#), "{s}");
        assert!(s.contains(r#"kind := .provide, tuple := [m ⟨0, by decide⟩], count := (3 : F)"#), "{s}");
    }

    /// The ALU exports with no extension constraints and its honest rows pass in Rust.
    #[test]
    fn alu_exports() {
        let cap = capture("alu", &alu::AluAir).unwrap();
        export_chip("REV", "alu", "A", &cap).unwrap();
        assert!(honest_rows(&cap).unwrap().len() > 19);
    }
}
