# M0 + M1: Scaffold and RV32 ALU Soundness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A public Lean 4 project whose first published theorem is: every row
the RV32 ALU chip's constraints accept (given its lookups hit valid table
rows) computes `AluOp.eval` exactly, for all 19 ops — with constraints
generated from the Rust, CI-checked for drift, and the fixed MULT-padding
forgery reproduced as a Lean witness.

**Architecture:** A Rust exporter (`exporter/`, in this repo) builds against
`zkp-circuits` at a pinned commit, runs Plonky3's `InteractionSymbolicBuilder`
over `AluAir`, and prints `Rand/Generated/RV32/Alu.lean` (constraints +
bus interactions as Lean functions of a row). Hand-written Lean gives the
field, the bus-contract semantics, the `AluOp.eval` spec, and the proofs.
CI rebuilds everything from public repos and audits axioms.

**Tech Stack:** Lean 4 + Mathlib (pinned), Lake; Rust 1.98.1 with
`rand_zkvm` (circuits `research/` crate) and Plonky3 0.7.0; GitHub Actions.

**Spec:** `docs/specs/2026-10-21-lean-verification-design.md` (§4.1, §4.3,
§4.4, §6, §7, §8 M0–M1).

## Global Constraints

- Repo: `https://github.com/randprotocol/lean.git`, local `~/Github/randprotocol/lean`, branch `main`.
- Push only as `dendisuhubdy`: `git -c credential.helper= -c 'credential.helper=!f(){ echo username=dendisuhubdy; echo password=$(gh auth token -u dendisuhubdy); }; f' push origin main`.
- Circuits source: public repo `https://github.com/randprotocol/zkp-circuits`, pinned commit `b3e21d9ea16225452bcd03a94317cb61e1705979`; crate `rand_zkvm` at `research/`; Rust `1.98.1`.
- Field: Goldilocks, `p = 18446744069414584321` (`2^64 − 2^32 + 1`), modelled as `ZMod p`.
- No `sorry`, `admit`, or project-local `axiom` anywhere under `Rand/`. Published theorems may depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Cryptographic/trust assumptions appear as named hypotheses (theorem arguments or structure fields), never `axiom`.
- Every hand-written definition that models Rust carries `-- models: <repo>/<path>:<line> @<commit>`.
- Generated files carry a header with the circuits commit and must not be edited by hand.
- Commit messages end with the two attribution lines (`Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and the `Claude-Session:` line).

## Review Focus

1. **Exporter silently drops something** (a constraint kind, a `when_transition`, a preprocessed/public leaf, a bus kind) → the Lean model is weaker than the AIR and the proof means less. Expect: exporter fails loudly on any leaf/interaction kind it does not translate. Test in Task 3.
2. **Bus contract stronger than the real table** (e.g. POW2 claimed for all `s` when the table has `s < 256` with `0` for `s ≥ 32`) → proof leans on a false assumption. Expect: each contract quoted from the table's `preprocessed_trace` and checked against generated table contents. Test in Task 2.
3. **Spec ≠ Rust `AluOp::eval`** on edge cases (div by zero, `MIN/−1`, shift by ≥ 32 masked to `b & 31`, `mulhsu` sign) → proof is of the wrong function. Expect: Lean spec agrees with Rust on exporter-generated vectors including every edge case. Test in Task 4.
4. **Count semantics wrong**: a lookup with count `g` is only binding when `g ≠ 0`; if the model assumed it always binds, gated-off lookups would be wrongly assumed. Expect: `lookupsHold` hypothesis only constrains interactions whose count evaluates nonzero. Test in Task 2 (a gated-off lookup with an out-of-table tuple still satisfies `lookupsHold`).
5. **Field-vs-integer slips** (`(a*b).val ≠ a.val*b.val` once it wraps) → unsound arithmetic steps. Expect: every `.val` of a product/sum goes through a lemma with an explicit `< p` bound. Enforced by Task 5's lemma interface.

---

## File Structure

```
lean/
  lean-toolchain, lakefile.toml, lake-manifest.json
  Rand.lean                          -- imports everything published
  Rand/Field.lean                    -- Goldilocks F := ZMod p, Fact p.Prime, val lemmas
  Rand/Bus.lean                      -- Interaction, BusId, Kind, lookupsHold, providesHold
  Rand/RV32/Contracts.lean           -- RANGE8/AND4/OR4/XOR4/POW2 contracts; ALU bus contract
  Rand/RV32/AluSpec.lean             -- AluOp (19), AluOp.eval over Nat (u32 semantics)
  Rand/RV32/Alu/Basic.lean           -- column names, decoding helpers, shared lemmas
  Rand/RV32/Alu/Adder.lean           -- add, sub, slt, sltu, eq
  Rand/RV32/Alu/Bitwise.lean         -- and, or, xor
  Rand/RV32/Alu/Shift.lean           -- sll, srl, sra
  Rand/RV32/Alu/Mul.lean             -- mul, mulh, mulhu, mulhsu
  Rand/RV32/Alu/Div.lean             -- div, divu, rem, remu
  Rand/RV32/Alu/Sound.lean           -- alu_row_sound, alu_padding_inert, alu_provides_contract
  Rand/RV32/Alu/Regression.lean      -- MULT-padding forgery witness
  Rand/Generated/RV32/Alu.lean       -- GENERATED constraints + interactions
  Rand/Generated/RV32/AluVectors.lean-- GENERATED (op, a, b, eval) test vectors
  Rand/Generated/RV32/Tables.lean    -- GENERATED range/nibble preprocessed contents (for contract checks)
  Audit.lean + scripts/audit.sh      -- axiom audit over the published list
  exporter/Cargo.toml, exporter/src/main.rs, exporter/rust-toolchain.toml
  scripts/fetch-sources.sh           -- clones zkp-circuits at SOURCES.toml pin into third_party/
  scripts/check-generated.sh         -- re-export and diff
  SOURCES.toml, README.md, ASSUMPTIONS.md, PROVEN.md, LICENSE
  .github/workflows/ci.yml
  .gitignore                         -- .lake/, third_party/, exporter/target/
```

---

### Task 1: Lake project, field, CI skeleton, public pages

**Files:**
- Create: `lean-toolchain`, `lakefile.toml`, `Rand.lean`, `Rand/Field.lean`, `SOURCES.toml`, `README.md`, `ASSUMPTIONS.md`, `PROVEN.md`, `LICENSE` (licence to be decided by the owner: fullnode and circuits are both GPL-3.0, so GPL-3.0 would match them; Apache-2.0 would not — check `../fullnode/LICENSE`), `.gitignore`, `.github/workflows/ci.yml`, `scripts/audit.sh`, `Audit.lean`
- Test: `RandTest/Field.lean`

**Interfaces:**
- Produces: `Rand.Goldilocks.p : ℕ := 18446744069414584321`, `abbrev Rand.F := ZMod p`, `instance : Fact p.Prime`, lemma `Rand.val_add_of_lt {a b : F} (h : a.val + b.val < p) : (a + b).val = a.val + b.val`, `Rand.val_mul_of_lt {a b : F} (h : a.val * b.val < p) : (a * b).val = a.val * b.val`, `Rand.val_natCast_of_lt {n : ℕ} (h : n < p) : (n : F).val = n`.
- Produces: `Audit.lean` holding `def published : List Name` (empty for now); `scripts/audit.sh` runs `lake env lean Audit.lean` which, for each name, collects axioms (`Lean.collectAxioms`) and fails if any is outside `{propext, Classical.choice, Quot.sound}`; also greps `Rand/` for `sorry|admit|^axiom` and fails on a hit.

- [ ] **Step 1:** Install elan (`curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none`), pick the newest Lean release that the latest tagged Mathlib supports, write both pins.
- [ ] **Step 2: Write the failing test** `RandTest/Field.lean`:
  ```lean
  example : Rand.Goldilocks.p = 2^64 - 2^32 + 1 := by norm_num [Rand.Goldilocks.p]
  example : ((2^32 - 1 : ℕ) : Rand.F) * ((2^32 - 1 : ℕ) : Rand.F) = (((2^32-1)*(2^32-1) : ℕ) : Rand.F) := by push_cast; ring
  example : ((2^32 - 1 : ℕ) : Rand.F).val = 2^32 - 1 := Rand.val_natCast_of_lt (by norm_num [Rand.Goldilocks.p])
  ```
- [ ] **Step 3:** `lake build RandTest` → FAIL (unknown identifier).
- [ ] **Step 4:** Implement `Rand/Field.lean`. Primality: `Fact (Nat.Prime p)` via `by norm_num` (Mathlib's `Nat.Prime` norm_num extension handles 64-bit; if it is too slow, use a Pratt certificate — builder's call).
- [ ] **Step 5:** `lake build RandTest` → PASS. `scripts/audit.sh` → exit 0.
- [ ] **Step 6:** CI workflow: job `lean` (checkout, elan, `lake exe cache get`, `lake build`, `lake build RandTest`, `scripts/audit.sh`). Job `generated` is added in Task 3.
- [ ] **Step 7:** `ASSUMPTIONS.md` — copy design §6 verbatim as the initial list, Poseidon2 dev-seed gap first and bold. `PROVEN.md` — table header (Theorem | Plain statement | Lean name | Models | Assumptions), no rows yet, plus a "Scope" paragraph: chain-21 genesis, circuits pin. `README.md`: what this is, how to build, links to both pages. `SOURCES.toml`:
  ```toml
  [circuits]
  repo = "https://github.com/randprotocol/zkp-circuits"
  rev  = "b3e21d9ea16225452bcd03a94317cb61e1705979"
  [fullnode]
  repo = "https://github.com/randprotocol/fullnode"
  rev  = "246cb5f97624e9f9d70a929941298b78511d5fe8"
  ```
- [ ] **Step 8:** Commit `build: Lake project, Goldilocks field, axiom audit, public pages`; push (Global Constraints recipe); confirm CI green on GitHub (`gh run list -R randprotocol/lean` with `GH_TOKEN=$(gh auth token -u dendisuhubdy)`).

### Task 2: Bus semantics and RV32 lookup contracts

**Files:**
- Create: `Rand/Bus.lean`, `Rand/RV32/Contracts.lean`
- Test: `RandTest/Bus.lean`

**Interfaces:**
- Produces (`Rand/Bus.lean`):
  ```lean
  inductive Kind | lookup | provide | send | receive
  structure Interaction where
    bus   : String
    kind  : Kind
    tuple : List F
    count : F
  /-- Bus soundness assumption, in usable form: every *lookup* whose count is
      nonzero hits a tuple satisfying the bus contract. -/
  def lookupsHold (contract : String → List F → Prop) (is : List Interaction) : Prop :=
    ∀ i ∈ is, i.kind = .lookup → i.count ≠ 0 → contract i.bus i.tuple
  ```
- Produces (`Rand/RV32/Contracts.lean`), `def rv32Contract : String → List F → Prop` with, by bus name:
  - `"RANGE8"`: `[x]` ↦ `x.val < 256`
  - `"AND4"`/`"OR4"`/`"XOR4"`: `[x, y, z]` ↦ `x.val < 16 ∧ y.val < 16 ∧ z.val = x.val &&& y.val` (resp. `|||`, `^^^`)
  - `"POW2"`: `[s, w]` ↦ `s.val < 256 ∧ w.val = if s.val < 32 then 2 ^ s.val else 0`
  - anything else ↦ `True` (no assumption claimed)
  - Bus name strings must equal the `LookupBus::new("…")` names in `research/src/tables/mod.rs`.
- Produces: `def aluContract : List F → Prop` — `[op, a, b, c]` ↦ `∃ o : AluOp, op = (o.code : F) ∧ a.val < 2^32 ∧ b.val < 2^32 ∧ c.val = o.eval a.val b.val` (uses Task 4's `AluOp`; place `aluContract` in `Rand/RV32/Alu/Sound.lean` if import order demands).

- [ ] **Step 1: Failing tests** `RandTest/Bus.lean`:
  - `lookupsHold rv32Contract [⟨"RANGE8", .lookup, [300], 0⟩]` is provable (gated-off lookup with out-of-table tuple — Review Focus 4).
  - `¬ lookupsHold rv32Contract [⟨"RANGE8", .lookup, [300], 1⟩]` is provable.
  - `rv32Contract "POW2" [40, 0]` and `rv32Contract "POW2" [5, 32]` provable; `¬ rv32Contract "POW2" [40, 2^40]`.
- [ ] **Step 2:** `lake build RandTest` → FAIL.
- [ ] **Step 3:** Implement both files.
- [ ] **Step 4:** PASS.
- [ ] **Step 5:** Contract-vs-table check — deferred to Task 3, Step 6 (needs the exporter).
- [ ] **Step 6:** Commit `bus: interaction semantics and RV32 lookup contracts`.

### Task 3: The exporter (`air2lean`) and generated ALU constraints

**Files:**
- Create: `exporter/Cargo.toml`, `exporter/rust-toolchain.toml` (`1.98.1`), `exporter/src/main.rs`, `scripts/fetch-sources.sh`, `scripts/check-generated.sh`
- Generated: `Rand/Generated/RV32/Alu.lean`, `Rand/Generated/RV32/Tables.lean`
- Modify: `.github/workflows/ci.yml` (add job `generated`)
- Test: `RandTest/GeneratedAlu.lean`

**Interfaces:**
- Consumes: `rand_zkvm::tables::alu::AluAir`, `rand_zkvm::tables::{range, nibble}` (preprocessed traces), `p3_lookup::InteractionSymbolicBuilder` (`base_constraints()`, `global_interactions()`, `local_interactions()`, `exclusive_interactions()`), `p3_air::symbolic::{SymbolicExpression, BaseLeaf}`.
- `exporter/Cargo.toml` depends on `rand_zkvm = { path = "../third_party/zkp-circuits/research" }` and the exact `p3-*` `=0.7.0` versions the circuits crate uses (copy from `research/Cargo.toml`; reuse its `[patch]`s if any).
- CLI: `air2lean alu --out Rand/Generated/RV32/Alu.lean`, `air2lean tables --out Rand/Generated/RV32/Tables.lean`, `air2lean alu-vectors --out Rand/Generated/RV32/AluVectors.lean` (Task 4).
- Produces (`Rand/Generated/RV32/Alu.lean`, namespace `Rand.Generated.RV32.Alu`):
  ```lean
  -- GENERATED by exporter from zkp-circuits @<rev>. Do not edit.
  def width : ℕ := 64
  def constraints (m : Fin 64 → F) : List F := [ … ]      -- exporter order, one per base constraint
  def interactions (m : Fin 64 → F) : List Interaction := [ … ]
  ```
  Shared DAG nodes become `let` bindings inside each function (same memoisation idea as `recursion/src/programs/constraints.rs`). Constants print as their canonical `u64`.
- Produces (`Rand/Generated/RV32/Tables.lean`): `def range8Rows : List (ℕ × ℕ × ℕ)` (A, POW2, IS_POW2 for 256 rows) and `def nibbleRows : List (ℕ × ℕ × ℕ × ℕ × ℕ)` (a, b, and, or, xor; 256 rows), read from the chips' `preprocessed_trace`.

- [ ] **Step 1:** `scripts/fetch-sources.sh`: reads `SOURCES.toml`, clones each repo into `third_party/<name>` at `rev` (shallow fetch of that commit), idempotent.
- [ ] **Step 2: Failing test** `RandTest/GeneratedAlu.lean`: `example : Rand.Generated.RV32.Alu.width = 64 := rfl`; and an honest row from Rust is accepted: the exporter also emits `def honestRows : List (Fin 64 → F)` (rows taken from `alu_trace` on a small program covering all 19 ops, plus one padding row) and the test is `example : ∀ r ∈ honestRows, ∀ c ∈ constraints r, c = 0 := by decide` (`native_decide` is **not** allowed — it adds the `Lean.ofReduceBool` axiom and would fail the audit — use `decide`/`norm_num`/`simp` with `ZMod` computation; if `decide` is too slow, prove per-row with `simp [constraints]; norm_num`).
- [ ] **Step 3:** Run → FAIL (no file).
- [ ] **Step 4:** Implement `main.rs`. Rules:
  - Leaves: `Variable` with entry `Main{offset: 0}` → `m ⟨i, by decide⟩`; `Constant` → numeral. **Any other leaf** (next-row offset, preprocessed, public, periodic, `IsFirstRow`/`IsLastRow`/`IsTransition`) → exit nonzero with the chip name and leaf (Review Focus 1). ALU uses none of them; later chips extend the exporter.
  - Interactions: emit every global/local/exclusive interaction with bus name, kind (`lookup_key`→`.lookup`, `table_entry`→`.provide`, `send`/`receive`), tuple, count. Any interaction kind not in that list → exit nonzero.
  - Extension constraints (LogUp gadget) are **not** exported: they are the bus mechanism, covered by the bus-soundness assumption. Assert the ALU yields zero extension constraints from `air.eval`, else exit nonzero.
  - Output deterministic (stable ordering, no timestamps; header holds only the rev).
- [ ] **Step 5:** Run exporter; `lake build RandTest` → PASS.
- [ ] **Step 6: Contract-vs-table check** (Review Focus 2): in `RandTest/Contracts.lean` prove
  `∀ r ∈ range8Rows, r.2.1 = if r.1 < 32 then 2^r.1 else 0` and `range8Rows.map (·.1) = List.range 256`, and for `nibbleRows`: `∀ (a,b,x,o,y) ∈ nibbleRows, a < 16 ∧ b < 16 ∧ x = a &&& b ∧ o = a ||| b ∧ y = a ^^^ b` and length 256 — by `decide`. Note in `ASSUMPTIONS.md` that the RANGE8/POW2/AND4… contracts are justified by these table contents plus bus soundness; M2 proves the table chips themselves.
- [ ] **Step 7:** `scripts/check-generated.sh`: fetch sources, rebuild exporter, regenerate all files into a temp dir, `diff -r` against `Rand/Generated/` → nonzero on any difference. CI job `generated` runs it with Rust 1.98.1 (cache `exporter/target`).
- [ ] **Step 8:** Exporter negative test: a `#[test]` in `exporter/src/main.rs` running the translator over a tiny local AIR that uses `next` and asserting it errors.
- [ ] **Step 9:** Commit `exporter: air2lean, generated RV32 ALU constraints and tables`; push; CI green.

### Task 4: `AluOp` spec and Rust-agreement vectors

**Files:**
- Create: `Rand/RV32/AluSpec.lean`; generated `Rand/Generated/RV32/AluVectors.lean`
- Modify: `exporter/src/main.rs` (subcommand `alu-vectors`)
- Test: `RandTest/AluVectors.lean`

**Interfaces:**
- Produces: `inductive AluOp` with the 19 constructors in Rust order (`add sub and or xor sll srl sra slt sltu eq mul mulh mulhu mulhsu div divu rem remu`), `AluOp.code : AluOp → ℕ` (0..18), `AluOp.all : List AluOp`, `AluOp.eval : AluOp → ℕ → ℕ → ℕ` taking and returning values `< 2^32` (u32 semantics; signed ops via `Int` two's-complement helpers `toSigned32 : ℕ → ℤ`, `ofSigned32 : ℤ → ℕ`), plus `AluOp.eval_lt : a < 2^32 → b < 2^32 → o.eval a b < 2^32`.
- Models: `research/src/isa.rs:94 @b3e21d9` — transcribe each arm exactly, including `s = b & 31`, `div` by 0 → `0xffffffff`, `MIN/−1` cases, `rem` by 0 → `a`.

- [ ] **Step 1:** Exporter `alu-vectors`: for each op, emit `(code, a, b, AluOp::eval(a,b))` for the edge set `{0, 1, 2, 31, 32, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff}²` plus 64 seeded-random pairs (fixed seed), as `def aluVectors : List (ℕ × ℕ × ℕ × ℕ)`.
- [ ] **Step 2: Failing test:** `example : aluVectors.all (fun (c,a,b,r) => (AluOp.ofCode c).eval a b = r) = true := by decide` (builder may split by op if `decide` is slow; `native_decide` not allowed).
- [ ] **Step 3:** FAIL. **Step 4:** implement `AluSpec.lean`. **Step 5:** PASS.
- [ ] **Step 6:** Commit `spec: AluOp.eval matching rand_zkvm isa.rs, with Rust vectors`.

### Task 5: Shared ALU lemmas and adder ops (add, sub, slt, sltu, eq)

**Files:**
- Create: `Rand/RV32/Alu/Basic.lean`, `Rand/RV32/Alu/Adder.lean`

**Interfaces:**
- Consumes: Task 1 field lemmas, Task 2 `lookupsHold`/`rv32Contract`, Task 3 generated `constraints`/`interactions`, Task 4 `AluOp`.
- Produces (`Basic.lean`): column abbreviations matching `research/src/tables/alu.rs` `col` (`FLAG0=0`, `A=19`, `B=20`, `C=21`, `A0=22`, `B0=26`, `C0=30`, `Q0=34`, `S0=38`, `T0=42`, `SA=46`, `SB=47`, `SHH=48`, `PW=49`, `CARRY0=50`, `INV=54`, `IS_REAL=55`, `MULT=56`, `AH3=57`, `BH_N=58`, `QH3=59`, `DIVZ=60`, `INVB=61`, `DB2=62`, `DB3=63`); the hypothesis bundle
  ```lean
  structure AluRowOk (m : Fin 64 → F) : Prop where
    cons : ∀ c ∈ Generated.RV32.Alu.constraints m, c = 0
    look : lookupsHold rv32Contract (Generated.RV32.Alu.interactions m)
  ```
  and lemmas: `flags_onehot : AluRowOk m → m IS_REAL = 1 → ∃! o : AluOp, m (flag o) = 1 ∧ ∀ o' ≠ o, m (flag o') = 0`; `word_val : bytes < 256 → (word m base).val = Σ limb·256^i` ; `a_lt / b_lt : AluRowOk m → m IS_REAL = 1 → (m A).val < 2^32` (bitwise rows via nibble lookups, others via RANGE8).
- Produces (`Adder.lean`): `theorem alu_add_sound (h : AluRowOk m) (hf : m (flag .add) = 1) : (m C).val = AluOp.add.eval (m A).val (m B).val`, and the same shape for `sub slt sltu eq`.

- [ ] **Step 1: Failing statements:** write all five theorem statements with proofs `by sorry` in a scratch file outside `Rand/` (never committed) and confirm they elaborate; this is the "test" for a proof task.
- [ ] **Step 2:** Prove `Basic.lean` lemmas; move statements into `Adder.lean`; prove. Strategy note: lift each constraint to `ℕ` with `val_add_of_lt`/`val_mul_of_lt` and byte bounds, then `omega`. Carries `CARRY0..3` are boolean by constraint.
- [ ] **Step 3:** `lake build && scripts/audit.sh` → PASS, no sorry.
- [ ] **Step 4:** Commit `alu: adder-family soundness (add sub slt sltu eq)`.

### Task 6: Bitwise ops (and, or, xor)

**Files:** Create `Rand/RV32/Alu/Bitwise.lean`
**Interfaces:** Produces `alu_and_sound`, `alu_or_sound`, `alu_xor_sound`, same shape as Task 5. Key lemma: `bitwise_high_nibble` — for `lo < 16` (looked up) and `(byte − lo)·16⁻¹` with value `< 16` (looked up), `byte.val < 256` and `byte.val = lo.val + 16·hi.val` (`research/src/tables/alu.rs:139–155`; `INV16 = 17293822565076172801`).
- [ ] **Step 1:** Statements elaborate (scratch). **Step 2:** prove; byte-wise `Nat.land` composition lemma `land_bytes : (Σ aᵢ 256^i) &&& (Σ bᵢ 256^i) = Σ (aᵢ &&& bᵢ) 256^i` for bytes `< 256` (and nibble version). **Step 3:** build + audit PASS. **Step 4:** Commit `alu: bitwise soundness`.

### Task 7: Shifts (sll, srl, sra)

**Files:** Create `Rand/RV32/Alu/Shift.lean`
**Interfaces:** Produces `alu_sll_sound`, `alu_srl_sound`, `alu_sra_sound`. Uses POW2 contract (`PW = 2^(b & 31)`), `BH_N`/`SHH` shift-amount high bit, `Q0`/`S0`/`T0` quotient/remainder limbs, `AH3`/`SA` sign for `sra`.
- [ ] Steps as Task 6. Commit `alu: shift soundness`.

### Task 8: Multiplication (mul, mulh, mulhu, mulhsu)

**Files:** Create `Rand/RV32/Alu/Mul.lean`
**Interfaces:** Produces `alu_mul_sound`, `alu_mulh_sound`, `alu_mulhu_sound`, `alu_mulhsu_sound`. The argument is the one in `research/src/tables/alu.rs:8–45`: `T0,T1,T2` forced; `CARRY < 2^24` by its 3 RANGE8 bytes; `LO`'s limbs `T0..3` RANGE8-checked on every mul-family row pin `CARRY` to the honest value (injectivity of `CARRY ↦ LO mod p` on an interval shorter than `p`); single borrow bit for signed correction.
- [ ] Steps as Task 6. Commit `alu: multiplication soundness`.

### Task 9: Division (div, divu, rem, remu)

**Files:** Create `Rand/RV32/Alu/Div.lean`
**Interfaces:** Produces `alu_div_sound`, `alu_divu_sound`, `alu_rem_sound`, `alu_remu_sound`. Argument per `research/src/tables/alu.rs:47–72`: `|A| = Q·|B| + R` exact in `ℕ` (< p), `R < |B|` via `DB0..3` bytes when `B ≠ 0`, two-constraint is-zero gadget for `DIVZ`, `QH3` is-zero gate on negation, `MIN/−1` needs no special case, unsigned variants force `SA = SB = 0`.
- [ ] Steps as Task 6. Commit `alu: division soundness`.

### Task 10: Whole-chip theorems, regression witness, publication

**Files:**
- Create: `Rand/RV32/Alu/Sound.lean`, `Rand/RV32/Alu/Regression.lean`
- Modify: `Audit.lean` (`published` list), `PROVEN.md`, `ASSUMPTIONS.md`, `README.md`, `Rand.lean`

**Interfaces:**
- Produces:
  ```lean
  theorem alu_row_sound (h : AluRowOk m) (hr : m IS_REAL = 1) :
    ∃ o : AluOp, aluOpField m = (o.code : F) ∧ (m A).val < 2^32 ∧ (m B).val < 2^32
      ∧ (m C).val = o.eval (m A).val (m B).val
  theorem alu_padding_inert (h : AluRowOk m) (hr : m IS_REAL ≠ 1) : m IS_REAL = 0 ∧ m MULT = 0
  /-- Every tuple the ALU provides with nonzero multiplicity satisfies the ALU bus contract. -/
  theorem alu_provides_contract (h : AluRowOk m) :
    ∀ i ∈ Generated.RV32.Alu.interactions m, i.bus = "ALU" → i.kind = .provide → i.count ≠ 0 → aluContract i.tuple
  ```
  `aluOpField m = Σ m(flag i)·i` (the `op` expression at `alu.rs:431–433`).
- Regression (`Regression.lean`, design §4.4): define `constraintsPreFix m := (constraints m).eraseIdx k` where `k` is the index of `(1 − IS_REAL)·MULT` in the generated list (assert by `rfl` that entry `k` is that expression). Prove `∃ m, (∀ c ∈ constraintsPreFix m, c = 0) ∧ lookupsHold rv32Contract (interactions m) ∧ m MULT ≠ 0 ∧ ¬ aluContract [aluOpField m, m A, m B, m C]` with a concrete padding row (all flags 0, `IS_REAL = 0`, `MULT = 1`, `A = 9`, `B = 1`, `C = 999`, limbs set so `word = A/B/C`) — and, as its pair, that `alu_padding_inert` rules it out under the real constraints.

- [ ] **Step 1:** Statements elaborate (scratch). **Step 2:** prove `alu_row_sound` by case split on `flags_onehot` into Tasks 5–9. **Step 3:** prove padding + provides + regression. **Step 4:** add the four names to `Audit.lean`'s `published`; `scripts/audit.sh` → PASS and prints exactly `propext, Classical.choice, Quot.sound` (or a subset) per theorem; commit that output as `docs/audit/axioms.txt`.
- [ ] **Step 5:** `PROVEN.md` rows for each theorem: plain English (e.g. "Every real row of the RV32 ALU table that its constraints and lookups accept computes the RISC-V result of its opcode, for all 19 opcodes"), Lean name, `models: research/src/tables/alu.rs @b3e21d9`, assumptions ("lookup buses sound: a nonzero-count lookup hits a table row"; "RANGE8/nibble table contents as checked in `RandTest/Contracts.lean`"). Regression row phrased as "the constraint set without the padding-row MULT pin (`alu.rs:186–195`) admitted the `fib(10)=999` forgery row; the current one does not". `README.md`: one-paragraph status "M1: RV32 ALU — proven".
- [ ] **Step 6:** Full CI locally: `lake build && lake build RandTest && scripts/audit.sh && scripts/check-generated.sh`. Commit `alu: whole-chip soundness, padding inertness, MULT-forgery regression; publish`. Push; CI green; report the run URL.
