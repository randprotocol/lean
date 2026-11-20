import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Rand.RV32.Contracts
import Rand.RV32.AluSpec
import Rand.Generated.RV32.Alu

/-!
# Shared infrastructure for the RV32 ALU soundness proofs

* Column names of `research/src/tables/alu.rs` (`col`), as reducible `Fin 64` constants that
  unfold to exactly the `⟨k, _⟩` literals the generated file uses, so `rw`/`simp`/`ring` see
  `m A0` and the generated `m ⟨22, _⟩` as the same atom.
* `AluRowOk`: one row satisfying every generated constraint and every lookup contract.
* Extraction: `cons_at h.cons k as ck` puts the `k`-th generated constraint into context as
  `<expr> = 0`; `alu_look h k as lk` puts the `k`-th interaction in as
  `<count> ≠ 0 → <contract>`. Both read the expression off the generated `List` literal
  (no hand copy), and the proof term is checked against `(constraints m)[k]` by `defeq`, so
  a regenerated file is picked up automatically.
* `alu_flags h hf`: from one flag equal to `1`, every flag and `IS_REAL` as concrete hypotheses.
* Field-to-`ℕ` lifting: `nat_eq_of_cast` and the `lift_eq` tactic; every `.val` of a sum or
  product goes through an explicit `< p` bound.
* `flags_onehot`, `a_lt`, `b_lt`.
-/

namespace Rand.RV32.Alu

open Rand Rand.Goldilocks Rand.Generated.RV32.Alu

/-! ## Columns -/

-- models: zkp-circuits/research/src/tables/alu.rs:80 @b3e21d9
abbrev FLAG0 : Fin 64 := ⟨0, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:81 @b3e21d9
abbrev A : Fin 64 := ⟨19, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:81 @b3e21d9
abbrev B : Fin 64 := ⟨20, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:81 @b3e21d9
abbrev C : Fin 64 := ⟨21, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:82 @b3e21d9 (A0 + i)
abbrev A0 : Fin 64 := ⟨22, by decide⟩
abbrev A1 : Fin 64 := ⟨23, by decide⟩
abbrev A2 : Fin 64 := ⟨24, by decide⟩
abbrev A3 : Fin 64 := ⟨25, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:82 @b3e21d9 (B0 + i)
abbrev B0 : Fin 64 := ⟨26, by decide⟩
abbrev B1 : Fin 64 := ⟨27, by decide⟩
abbrev B2 : Fin 64 := ⟨28, by decide⟩
abbrev B3 : Fin 64 := ⟨29, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:82 @b3e21d9 (C0 + i)
abbrev C0 : Fin 64 := ⟨30, by decide⟩
abbrev C1 : Fin 64 := ⟨31, by decide⟩
abbrev C2 : Fin 64 := ⟨32, by decide⟩
abbrev C3 : Fin 64 := ⟨33, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:87 @b3e21d9 (Q0 + i)
abbrev Q0 : Fin 64 := ⟨34, by decide⟩
abbrev Q1 : Fin 64 := ⟨35, by decide⟩
abbrev Q2 : Fin 64 := ⟨36, by decide⟩
abbrev Q3 : Fin 64 := ⟨37, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:91 @b3e21d9 (S0 + i)
abbrev S0 : Fin 64 := ⟨38, by decide⟩
abbrev S1 : Fin 64 := ⟨39, by decide⟩
abbrev S2 : Fin 64 := ⟨40, by decide⟩
abbrev S3 : Fin 64 := ⟨41, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:98 @b3e21d9 (T0 + i)
abbrev T0 : Fin 64 := ⟨42, by decide⟩
abbrev T1 : Fin 64 := ⟨43, by decide⟩
abbrev T2 : Fin 64 := ⟨44, by decide⟩
abbrev T3 : Fin 64 := ⟨45, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:99 @b3e21d9
abbrev SA : Fin 64 := ⟨46, by decide⟩
abbrev SB : Fin 64 := ⟨47, by decide⟩
abbrev SHH : Fin 64 := ⟨48, by decide⟩
abbrev PW : Fin 64 := ⟨49, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:102 @b3e21d9 (CARRY0 + i)
abbrev CARRY0 : Fin 64 := ⟨50, by decide⟩
abbrev CARRY1 : Fin 64 := ⟨51, by decide⟩
abbrev CARRY2 : Fin 64 := ⟨52, by decide⟩
abbrev CARRY3 : Fin 64 := ⟨53, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:103 @b3e21d9
abbrev INV : Fin 64 := ⟨54, by decide⟩
abbrev IS_REAL : Fin 64 := ⟨55, by decide⟩
abbrev MULT : Fin 64 := ⟨56, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:106 @b3e21d9
abbrev AH3 : Fin 64 := ⟨57, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:109 @b3e21d9
abbrev BH_N : Fin 64 := ⟨58, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:113 @b3e21d9
abbrev QH3 : Fin 64 := ⟨59, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:115 @b3e21d9
abbrev DIVZ : Fin 64 := ⟨60, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:118 @b3e21d9
abbrev INVB : Fin 64 := ⟨61, by decide⟩
-- models: zkp-circuits/research/src/tables/alu.rs:122 @b3e21d9
abbrev DB2 : Fin 64 := ⟨62, by decide⟩
abbrev DB3 : Fin 64 := ⟨63, by decide⟩

theorem AluOp.code_lt (o : AluOp) : o.code < 19 := by cases o <;> decide

/-- The selector column of an operation: `FLAG0 + o.code`. -/
-- models: zkp-circuits/research/src/tables/alu.rs:178 @b3e21d9 (`f(op) = v(FLAG0 + op.code())`)
def flag (o : AluOp) : Fin 64 := ⟨o.code, by have := AluOp.code_lt o; omega⟩

@[simp] theorem flag_add : flag .add = ⟨0, by decide⟩ := rfl
@[simp] theorem flag_sub : flag .sub = ⟨1, by decide⟩ := rfl
@[simp] theorem flag_and : flag .and = ⟨2, by decide⟩ := rfl
@[simp] theorem flag_or : flag .or = ⟨3, by decide⟩ := rfl
@[simp] theorem flag_xor : flag .xor = ⟨4, by decide⟩ := rfl
@[simp] theorem flag_sll : flag .sll = ⟨5, by decide⟩ := rfl
@[simp] theorem flag_srl : flag .srl = ⟨6, by decide⟩ := rfl
@[simp] theorem flag_sra : flag .sra = ⟨7, by decide⟩ := rfl
@[simp] theorem flag_slt : flag .slt = ⟨8, by decide⟩ := rfl
@[simp] theorem flag_sltu : flag .sltu = ⟨9, by decide⟩ := rfl
@[simp] theorem flag_eq : flag .eq = ⟨10, by decide⟩ := rfl
@[simp] theorem flag_mul : flag .mul = ⟨11, by decide⟩ := rfl
@[simp] theorem flag_mulh : flag .mulh = ⟨12, by decide⟩ := rfl
@[simp] theorem flag_mulhu : flag .mulhu = ⟨13, by decide⟩ := rfl
@[simp] theorem flag_mulhsu : flag .mulhsu = ⟨14, by decide⟩ := rfl
@[simp] theorem flag_div : flag .div = ⟨15, by decide⟩ := rfl
@[simp] theorem flag_divu : flag .divu = ⟨16, by decide⟩ := rfl
@[simp] theorem flag_rem : flag .rem = ⟨17, by decide⟩ := rfl
@[simp] theorem flag_remu : flag .remu = ⟨18, by decide⟩ := rfl

/-- The opcode field the row provides on the `ALU` bus: `Σ flag(o) · code(o)`. -/
-- models: zkp-circuits/research/src/tables/alu.rs:433 @b3e21d9
def aluOpField (m : Fin 64 → F) : F :=
  (AluOp.all.map fun o => m (flag o) * (o.code : F)).sum

/-- A little-endian word of four byte limbs, in the generated file's association order. -/
-- models: zkp-circuits/research/src/tables/alu.rs:201 @b3e21d9
abbrev word4 (x0 x1 x2 x3 : F) : F := x0 + x1 * 256 + x2 * 65536 + x3 * 16777216

/-- `word m base` = limbs `base .. base+3` of row `m` recomposed (`word(base)` in `alu.rs`). -/
-- models: zkp-circuits/research/src/tables/alu.rs:201 @b3e21d9
def word (m : Fin 64 → F) (base : ℕ) (hb : base + 3 < 64 := by decide) : F :=
  word4 (m ⟨base, by omega⟩) (m ⟨base + 1, by omega⟩) (m ⟨base + 2, by omega⟩)
    (m ⟨base + 3, by omega⟩)

/-- `alu_unfold` unfolds the column names to the generated `⟨k, _⟩` literals everywhere.
`omega` compares atoms syntactically, so hypotheses read off the generated file
(`m ⟨22, _⟩`) and statements written with names (`m A0`) must be put in one form first. -/
macro "alu_unfold" : tactic => `(tactic| try simp only [FLAG0, A, B, C, A0, A1, A2, A3, B0, B1, B2, B3, C0, C1, C2, C3, Q0, Q1, Q2, Q3, S0, S1, S2, S3, T0, T1, T2, T3, SA, SB, SHH, PW, CARRY0, CARRY1, CARRY2, CARRY3, INV, IS_REAL, MULT, AH3, BH_N, QH3, DIVZ, INVB, DB2, DB3] at *)

/-- `alu_omega`: `omega` after `alu_unfold`. `omega` uses every hypothesis in context and gets
slow on the long carry chains with all their byte bounds; prefer `alu_linarith` for linear
steps there and `omega` only after clearing (`clear * - …`). -/
macro "alu_omega" : tactic => `(tactic| (alu_unfold; omega))

/-- `alu_linarith`: `linarith` after `alu_unfold`. -/
macro "alu_linarith" : tactic => `(tactic| (alu_unfold; linarith))

/-! ## The row hypothesis -/

/-- One ALU row accepted by the chip: every generated base constraint vanishes and every
active lookup hits its table (`rv32Contract`). -/
structure AluRowOk (m : Fin 64 → F) : Prop where
  cons : ∀ c ∈ Generated.RV32.Alu.constraints m, c = 0
  look : lookupsHold rv32Contract (Generated.RV32.Alu.interactions m)

/-! ## Extraction of one constraint / interaction from the generated lists -/

theorem cons_nth {L : List F} (h : ∀ c ∈ L, c = 0) (i : ℕ) (hi : i < L.length) : L[i] = 0 :=
  h _ (List.getElem_mem hi)

theorem look_nth {c : String → List F → Prop} {L : List Interaction} (h : lookupsHold c L)
    (i : ℕ) (hi : i < L.length) (hk : L[i].kind = .lookup) :
    L[i].count ≠ 0 → c L[i].bus L[i].tuple :=
  h _ (List.getElem_mem hi) hk

open Lean Meta Elab Tactic in
/-- The `i`-th element of a list term that reduces (by unfolding and `let`-zeta) to a literal. -/
partial def listLitNth (l : Expr) (i : Nat) : MetaM Expr := do
  let l ← whnfD l
  match l.getAppFnArgs with
  | (``List.cons, #[_, hd, tl]) => if i = 0 then return hd else listLitNth tl (i - 1)
  | _ => throwError "listLitNth: not a list literal (or index out of range): {l}"

open Lean Meta Elab Tactic in
/-- The list `L` of a hypothesis `∀ c ∈ L, _` or `lookupsHold _ L`. -/
def listOfHyp (ty : Expr) : MetaM Expr := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``lookupsHold 2 then return ty.appArg!
  forallTelescopeReducing ty fun xs _ => do
    unless xs.size ≥ 2 do throwError "expected `∀ c ∈ L, _`, got {ty}"
    let memTy ← inferType xs[1]!
    unless memTy.isAppOfArity ``Membership.mem 5 do throwError "expected `∀ c ∈ L, _`, got {ty}"
    return memTy.getAppArgs[3]!

open Lean Meta Elab Tactic in
/-- `cons_at h k as ck`, for `h : ∀ c ∈ L, c = 0` with `L` a generated constraint list: adds
`ck : e = 0`, where `e` is the `k`-th element of `L` read off the generated literal (lets
inlined). The proof is `cons_nth h k _`, checked against `e = 0` by `defeq`. -/
elab "cons_at " h:term:max k:num " as " n:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let L ← listOfHyp (← inferType hE)
  let i := k.getNat
  let e ← listLitNth L i
  let hi ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[L]])
  let pf ← mkAppM ``cons_nth #[hE, mkNatLit i, hi]
  let some (_, _, rhs) := (← inferType pf).eq? | throwError "cons_at: unexpected type"
  let ty ← mkEq e rhs
  unless ← isDefEq (← inferType pf) ty do throwError "cons_at: element {i} does not match"
  liftMetaTactic fun g => do
    let (_, g) ← (← g.assert n.getId ty pf).intro1P
    return [g]

open Lean Meta Elab Tactic in
/-- `look_at h k as lk`, for `h : lookupsHold c L`: adds `lk : count ≠ 0 → c bus tuple` for
the `k`-th interaction of `L` (which must be a lookup). -/
elab "look_at " h:term:max k:num " as " n:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let L ← listOfHyp (← inferType hE)
  let i := k.getNat
  let e ← whnfD (← listLitNth L i)
  unless e.isAppOfArity ``Interaction.mk 4 do throwError "look_at: not an interaction literal {e}"
  let args := e.getAppArgs
  let (bus, kind, tuple, count) := (args[0]!, args[1]!, args[2]!, args[3]!)
  unless kind.isConstOf ``Kind.lookup do throwError "look_at: interaction {i} is not a lookup"
  let hi ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[L]])
  let hk ← mkEqRefl (mkConst ``Kind.lookup)
  let pf ← mkAppOptM ``look_nth #[none, none, hE, mkNatLit i, hi, hk]
  let cE := (← instantiateMVars (← inferType hE)).appFn!.appArg!
  let ty ← mkArrow (← mkAppM ``Ne #[count, ← mkAppOptM ``OfNat.ofNat
    #[← inferType count, mkRawNatLit 0, none]]) (mkAppN cE #[bus, tuple])
  unless ← isDefEq (← inferType pf) ty do throwError "look_at: interaction {i} does not match"
  liftMetaTactic fun g => do
    let (_, g) ← (← g.assert n.getId ty pf).intro1P
    return [g]

/-- `alu_look h k as lk` for `h : AluRowOk m`: `look_at h.look k as lk` with the RV32 contract
unfolded (e.g. `lk : count ≠ 0 → (m ⟨22, _⟩).val < 256`). -/
macro "alu_look " h:term:max k:num " as " n:ident : tactic =>
  `(tactic| (look_at ($h).look $k as $n; simp only [rv32Contract] at $n:ident))

/-! ## Field facts -/

theorem p_lit : p = 18446744069414584321 := rfl

theorem val_lt_p (x : F) : x.val < 18446744069414584321 := ZMod.val_lt x

/-- Injectivity of `ℕ → F` below `p`: the one way equalities leave the field. -/
theorem nat_eq_of_cast {a b : ℕ} (ha : a < 18446744069414584321) (hb : b < 18446744069414584321)
    (h : (a : F) = (b : F)) : a = b := by
  rw [← val_natCast_of_lt ha, ← val_natCast_of_lt hb, h]

/-- `lift_eq c₁ c₂ …` closes a `ℕ` goal `lhs = rhs` (in `.val`s of row cells) whose cast to `F`
follows linearly from the field hypotheses `cᵢ`; the two `< p` side goals go to `omega`
(with the `val_lt_p` bound as a fallback). -/
syntax "lift_eq" (ppSpace colGt term:max)? : tactic
macro_rules
  | `(tactic| lift_eq) => `(tactic|
      (refine nat_eq_of_cast (by first | exact val_lt_p _ | alu_linarith)
          (by first | exact val_lt_p _ | alu_linarith) ?_
       push_cast [ZMod.natCast_zmod_val]
       ring))
  | `(tactic| lift_eq $c) => `(tactic|
      (refine nat_eq_of_cast (by first | exact val_lt_p _ | alu_linarith)
          (by first | exact val_lt_p _ | alu_linarith) ?_
       push_cast [ZMod.natCast_zmod_val]
       first | linear_combination $c:term | linear_combination -$c:term))

theorem bool_cases {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

instance : Fact (1 < p) := ⟨p_prime.one_lt⟩

theorem val_zero' : (0 : F).val = 0 := ZMod.val_zero
theorem val_one' : (1 : F).val = 1 := ZMod.val_one _

theorem val_le_one_of_bool {x : F} (h : x * (x - 1) = 0) : x.val ≤ 1 := by
  rcases bool_cases h with rfl | rfl
  · rw [val_zero']; omega
  · rw [val_one']

/-- `16⁻¹` in Goldilocks, the constant `INV16` of `alu.rs`. -/
theorem sixteen_mul_inv16 : (16 : F) * 17293822565076172801 = 1 := by decide

/-- A byte from two looked-up nibbles: if `lo < 16` and the *derived* high nibble
`(byte - lo) * 16⁻¹` is `< 16`, then `byte < 256` (`bitwise_high_nibble` in `alu.rs`). -/
-- models: zkp-circuits/research/src/tables/alu.rs:164 @b3e21d9
theorem byte_lt_of_nibbles {byte lo : F} (hlo : lo.val < 16)
    (hhi : ((byte - lo) * 17293822565076172801).val < 16) :
    byte.val < 256 ∧ byte.val = lo.val + 16 * ((byte - lo) * 17293822565076172801).val := by
  have e : byte.val = lo.val + 16 * ((byte - lo) * 17293822565076172801).val := by
    lift_eq ((lo - byte) * sixteen_mul_inv16)
  omega

/-- Word recomposition does not wrap: `(word4 x₀ x₁ x₂ x₃).val = Σ xᵢ.val · 256^i`. -/
theorem word4_val {x0 x1 x2 x3 : F} (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256)
    (h3 : x3.val < 256) :
    (word4 x0 x1 x2 x3).val = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
  lift_eq

theorem word_val (m : Fin 64 → F) (base : ℕ) (hb : base + 3 < 64)
    (h : ∀ i : Fin 4, (m ⟨base + i, by omega⟩).val < 256) :
    (word m base hb).val = ∑ i : Fin 4, (m ⟨base + i, by omega⟩).val * 256 ^ (i : ℕ) := by
  have h0 : (m ⟨base, by omega⟩).val < 256 := h 0
  have h1 : (m ⟨base + 1, by omega⟩).val < 256 := h 1
  have h2 : (m ⟨base + 2, by omega⟩).val < 256 := h 2
  have h3 : (m ⟨base + 3, by omega⟩).val < 256 := h 3
  rw [word, word4_val h0 h1 h2 h3, Fin.sum_univ_four]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, pow_zero,
    mul_one, pow_one]
  rfl

/-! ## Flags -/

instance : Fintype AluOp :=
  ⟨⟨AluOp.all, by decide⟩, fun o => by cases o <;> decide⟩

theorem sum_univ_eq_all {M : Type*} [AddCommMonoid M] (f : AluOp → M) :
    ∑ o, f o = (AluOp.all.map f).sum := rfl

theorem constraints_length (m : Fin 64 → F) : (constraints m).length = 72 := rfl

theorem interactions_length (m : Fin 64 → F) : (interactions m).length = 77 := rfl

variable {m : Fin 64 → F}

/-- `IS_REAL` is boolean (constraint 0). -/
-- models: zkp-circuits/research/src/tables/alu.rs:185 @b3e21d9
theorem real_bool (h : AluRowOk m) : m IS_REAL * (m IS_REAL - 1) = 0 := by
  cons_at h.cons 0 as c
  exact c

/-- Every flag is boolean (constraints 2..20). -/
-- models: zkp-circuits/research/src/tables/alu.rs:197 @b3e21d9
theorem flag_bool (h : AluRowOk m) (o : AluOp) : m (flag o) * (m (flag o) - 1) = 0 := by
  have c := cons_nth h.cons (o.code + 2)
    (by rw [constraints_length]; have := AluOp.code_lt o; omega)
  cases o <;> exact c

/-- The flags sum to `IS_REAL` (constraint 21), read in `ℕ`. -/
-- models: zkp-circuits/research/src/tables/alu.rs:198 @b3e21d9
theorem flag_sum_cast (h : AluRowOk m) : ((∑ o, (m (flag o)).val : ℕ) : F) = m IS_REAL := by
  cons_at h.cons 21 as c
  rw [sum_univ_eq_all]
  simp only [AluOp.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_add,
    Nat.cast_zero, ZMod.natCast_zmod_val, flag_add, flag_sub, flag_and, flag_or, flag_xor,
    flag_sll, flag_srl, flag_sra, flag_slt, flag_sltu, flag_eq, flag_mul, flag_mulh, flag_mulhu,
    flag_mulhsu, flag_div, flag_divu, flag_rem, flag_remu]
  linear_combination c

theorem flag_val_le (h : AluRowOk m) (o : AluOp) : (m (flag o)).val ≤ 1 :=
  val_le_one_of_bool (flag_bool h o)

theorem flag_sum_le (h : AluRowOk m) : ∑ o, (m (flag o)).val ≤ 19 := by
  calc ∑ o, (m (flag o)).val ≤ ∑ _o : AluOp, 1 := Finset.sum_le_sum fun o _ => flag_val_le h o
    _ = 19 := rfl

theorem val_eq_one_iff {x : F} : x.val = 1 ↔ x = 1 := by
  constructor
  · intro hx; exact ZMod.val_injective _ (hx.trans val_one'.symm)
  · rintro rfl; exact val_one'

/-- One flag set forces a real row and every other flag off. -/
theorem flag_others (h : AluRowOk m) {o : AluOp} (hf : m (flag o) = 1) :
    m IS_REAL = 1 ∧ ∀ o' ≠ o, m (flag o') = 0 := by
  have hS := flag_sum_cast h
  have hle := flag_sum_le h
  have hvo : (m (flag o)).val = 1 := val_eq_one_iff.2 hf
  have hge : (m (flag o)).val ≤ ∑ o, (m (flag o)).val :=
    Finset.single_le_sum (f := fun o => (m (flag o)).val) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ o)
  have hreal : m IS_REAL = 1 := by
    rcases bool_cases (real_bool h) with h0 | h1
    · exfalso
      rw [h0] at hS
      have : (∑ o, (m (flag o)).val) = 0 := nat_eq_of_cast (by omega) (by omega) (by rw [Nat.cast_zero]; exact hS)
      omega
    · exact h1
  refine ⟨hreal, fun o' hne => ?_⟩
  have hS1 : (∑ o, (m (flag o)).val) = 1 :=
    nat_eq_of_cast (by omega) (by omega) (by rw [hS, hreal, Nat.cast_one])
  have hpair : (m (flag o)).val + (m (flag o')).val ≤ ∑ o, (m (flag o)).val := by
    rw [← Finset.sum_pair (f := fun o => (m (flag o)).val) hne.symm]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have : (m (flag o')).val = 0 := by omega
  exact (ZMod.val_eq_zero _).1 this

/-- Every flag's value, given the one that is set. -/
theorem flag_val (h : AluRowOk m) {o : AluOp} (hf : m (flag o) = 1) (o' : AluOp) :
    m (flag o') = if o' = o then 1 else 0 := by
  split_ifs with he
  · rw [he]; exact hf
  · exact (flag_others h hf).2 o' he

/-- On a real row exactly one operation flag is set. -/
theorem flags_onehot (h : AluRowOk m) (hr : m IS_REAL = 1) :
    ∃! o : AluOp, m (flag o) = 1 ∧ ∀ o' ≠ o, m (flag o') = 0 := by
  have hS := flag_sum_cast h
  have hle := flag_sum_le h
  have hS1 : (∑ o, (m (flag o)).val) = 1 :=
    nat_eq_of_cast (by omega) (by omega) (by rw [hS, hr, Nat.cast_one])
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun o => (m (flag o)).val) (by omega)
  have hf : m (flag o) = 1 := val_eq_one_iff.1 (by have := flag_val_le h o; omega)
  refine ⟨o, ⟨hf, (flag_others h hf).2⟩, fun o' ⟨hf', _⟩ => ?_⟩
  by_contra hne
  have := (flag_others h hf).2 o' hne
  rw [hf'] at this
  exact one_ne_zero this

set_option hygiene false in
/-- `alu_flags h hf` (with `h : AluRowOk m`, `hf : m (flag o) = 1` for a concrete `o`) adds
`hreal : m IS_REAL = 1` and `f0 … f18 : m ⟨k, _⟩ = 1 / 0`, the value of every flag column. -/
macro "alu_flags " h:term:max hf:term:max : tactic => `(tactic| (
  have hreal := (flag_others $h $hf).1
  have f0 := flag_val $h $hf .add
  have f1 := flag_val $h $hf .sub
  have f2 := flag_val $h $hf .and
  have f3 := flag_val $h $hf .or
  have f4 := flag_val $h $hf .xor
  have f5 := flag_val $h $hf .sll
  have f6 := flag_val $h $hf .srl
  have f7 := flag_val $h $hf .sra
  have f8 := flag_val $h $hf .slt
  have f9 := flag_val $h $hf .sltu
  have f10 := flag_val $h $hf .eq
  have f11 := flag_val $h $hf .mul
  have f12 := flag_val $h $hf .mulh
  have f13 := flag_val $h $hf .mulhu
  have f14 := flag_val $h $hf .mulhsu
  have f15 := flag_val $h $hf .div
  have f16 := flag_val $h $hf .divu
  have f17 := flag_val $h $hf .rem
  have f18 := flag_val $h $hf .remu
  simp only [flag_add, flag_sub, flag_and, flag_or, flag_xor, flag_sll, flag_srl, flag_sra,
    flag_slt, flag_sltu, flag_eq, flag_mul, flag_mulh, flag_mulhu, flag_mulhsu, flag_div,
    flag_divu, flag_rem, flag_remu, reduceCtorEq, ↓reduceIte] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18))

set_option hygiene false in
/-- `alu_simp at hs` rewrites the flag and `IS_REAL` columns (from `alu_flags`) in `hs`. -/
macro "alu_simp" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    hreal] $(l)?)

/-- `alu_count` closes a lookup-count side goal `count ≠ 0` once `alu_flags` has run. -/
macro "alu_count" : tactic => `(tactic| (alu_simp; norm_num))

/-! ## Arithmetic helpers -/

/-- A sum that overflows by `k · 2^32` reduces to its low word. -/
theorem mod_of_carry {s c k : ℕ} (e : s = c + 2 ^ 32 * k) (hc : c < 2 ^ 32) : s % 2 ^ 32 = c := by
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- `ofSigned32` of an integer congruent to a u32 `c` is `c`. -/
theorem ofSigned32_of_carry {z : ℤ} {c : ℕ} (k : ℤ) (e : z = c + 2 ^ 32 * k) (hc : c < 2 ^ 32) :
    ofSigned32 z = c := by
  unfold ofSigned32
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem val_eight : (8 : F).val = 8 := rfl

theorem land_eight {x : ℕ} (hx : x < 16) : x &&& 8 = if 8 ≤ x then 8 else 0 := by
  interval_cases x <;> rfl

/-- Isolated sign-bit extraction (`a3_lo`/`AND4[hi, 8, s·8]` in `alu.rs`): with the dummy
low-nibble lookup `(byte - 16·hi) < 16`, the high-nibble lookup `hi < 16`, `s` boolean and
`(s·8) = hi &&& 8`, the byte is `< 256` and `s` is its top bit. -/
-- models: zkp-circuits/research/src/tables/alu.rs:271 @b3e21d9
theorem sign_bit {byte hi s : F} (hlo : (byte - 16 * hi).val < 16) (hhi : hi.val < 16)
    (hs : s * (s - 1) = 0) (hand : (s * 8).val = hi.val &&& (8 : F).val) :
    byte.val < 256 ∧ (s = 1 ∧ 128 ≤ byte.val ∨ s = 0 ∧ byte.val < 128) := by
  have e : byte.val = (byte - 16 * hi).val + 16 * hi.val := by lift_eq
  rw [val_eight, land_eight hhi] at hand
  rcases bool_cases hs with rfl | rfl
  · rw [zero_mul, val_zero'] at hand
    have : hi.val < 8 := by split_ifs at hand; omega
    exact ⟨by omega, Or.inr ⟨rfl, by omega⟩⟩
  · rw [one_mul, val_eight] at hand
    have : 8 ≤ hi.val := by split_ifs at hand; omega
    exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩

/-! ## Operand ranges -/

/-- `A0..3` and `B0..3` are bytes on every real row: by RANGE8 when the row is not bitwise
(`g_ab = IS_REAL - and - or - xor ≠ 0`), by the two nibble lookups per limb otherwise. -/
-- models: zkp-circuits/research/src/tables/alu.rs:230 @b3e21d9
theorem ab_bytes (h : AluRowOk m) (hr : m IS_REAL = 1) :
    (m A0).val < 256 ∧ (m A1).val < 256 ∧ (m A2).val < 256 ∧ (m A3).val < 256 ∧
    (m B0).val < 256 ∧ (m B1).val < 256 ∧ (m B2).val < 256 ∧ (m B3).val < 256 := by
  rcases bool_cases (flag_bool h .and) with h2 | h2
  · rcases bool_cases (flag_bool h .or) with h3 | h3
    · rcases bool_cases (flag_bool h .xor) with h4 | h4
      · -- not bitwise: RANGE8, gate `IS_REAL - and - or - xor = 1`
        simp only [flag_and, flag_or, flag_xor] at h2 h3 h4
        alu_look h 0 as l0; alu_look h 3 as l3; alu_look h 6 as l6; alu_look h 9 as l9
        alu_look h 1 as l1; alu_look h 4 as l4; alu_look h 7 as l7; alu_look h 10 as l10
        have hg : m IS_REAL - m ⟨2, by decide⟩ - m ⟨3, by decide⟩ - m ⟨4, by decide⟩ ≠ 0 := by
          rw [hr, h2, h3, h4]; norm_num
        exact ⟨l0 hg, l3 hg, l6 hg, l9 hg, l1 hg, l4 hg, l7 hg, l10 hg⟩
      · alu_flags h h4
        alu_look h 32 as a0; alu_look h 33 as b0; alu_look h 38 as a1; alu_look h 39 as b1
        alu_look h 44 as a2; alu_look h 45 as b2; alu_look h 50 as a3; alu_look h 51 as b3
        have g : m ⟨4, by decide⟩ ≠ 0 := by alu_count
        exact ⟨(byte_lt_of_nibbles (a0 g).1 (b0 g).1).1, (byte_lt_of_nibbles (a1 g).1 (b1 g).1).1,
          (byte_lt_of_nibbles (a2 g).1 (b2 g).1).1, (byte_lt_of_nibbles (a3 g).1 (b3 g).1).1,
          (byte_lt_of_nibbles (a0 g).2.1 (b0 g).2.1).1, (byte_lt_of_nibbles (a1 g).2.1 (b1 g).2.1).1,
          (byte_lt_of_nibbles (a2 g).2.1 (b2 g).2.1).1, (byte_lt_of_nibbles (a3 g).2.1 (b3 g).2.1).1⟩
    · alu_flags h h3
      alu_look h 30 as a0; alu_look h 31 as b0; alu_look h 36 as a1; alu_look h 37 as b1
      alu_look h 42 as a2; alu_look h 43 as b2; alu_look h 48 as a3; alu_look h 49 as b3
      have g : m ⟨3, by decide⟩ ≠ 0 := by alu_count
      exact ⟨(byte_lt_of_nibbles (a0 g).1 (b0 g).1).1, (byte_lt_of_nibbles (a1 g).1 (b1 g).1).1,
        (byte_lt_of_nibbles (a2 g).1 (b2 g).1).1, (byte_lt_of_nibbles (a3 g).1 (b3 g).1).1,
        (byte_lt_of_nibbles (a0 g).2.1 (b0 g).2.1).1, (byte_lt_of_nibbles (a1 g).2.1 (b1 g).2.1).1,
        (byte_lt_of_nibbles (a2 g).2.1 (b2 g).2.1).1, (byte_lt_of_nibbles (a3 g).2.1 (b3 g).2.1).1⟩
  · alu_flags h h2
    alu_look h 28 as a0; alu_look h 29 as b0; alu_look h 34 as a1; alu_look h 35 as b1
    alu_look h 40 as a2; alu_look h 41 as b2; alu_look h 46 as a3; alu_look h 47 as b3
    have g : m ⟨2, by decide⟩ ≠ 0 := by alu_count
    exact ⟨(byte_lt_of_nibbles (a0 g).1 (b0 g).1).1, (byte_lt_of_nibbles (a1 g).1 (b1 g).1).1,
      (byte_lt_of_nibbles (a2 g).1 (b2 g).1).1, (byte_lt_of_nibbles (a3 g).1 (b3 g).1).1,
      (byte_lt_of_nibbles (a0 g).2.1 (b0 g).2.1).1, (byte_lt_of_nibbles (a1 g).2.1 (b1 g).2.1).1,
      (byte_lt_of_nibbles (a2 g).2.1 (b2 g).2.1).1, (byte_lt_of_nibbles (a3 g).2.1 (b3 g).2.1).1⟩

/-- `A` recomposed from its limbs (constraint 22), in `ℕ`. -/
-- models: zkp-circuits/research/src/tables/alu.rs:202 @b3e21d9
theorem A_val (h : AluRowOk m) (hr : m IS_REAL = 1) :
    (m A).val = (m A0).val + (m A1).val * 256 + (m A2).val * 65536 + (m A3).val * 16777216 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := ab_bytes h hr
  cons_at h.cons 22 as c
  lift_eq c

/-- `B` recomposed from its limbs (constraint 23), in `ℕ`. -/
-- models: zkp-circuits/research/src/tables/alu.rs:203 @b3e21d9
theorem B_val (h : AluRowOk m) (hr : m IS_REAL = 1) :
    (m B).val = (m B0).val + (m B1).val * 256 + (m B2).val * 65536 + (m B3).val * 16777216 := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3⟩ := ab_bytes h hr
  cons_at h.cons 23 as c
  lift_eq c

/-- `A` is a u32 on every real row. -/
-- models: zkp-circuits/research/src/tables/alu.rs:202 @b3e21d9
theorem a_lt (h : AluRowOk m) (hr : m IS_REAL = 1) : (m A).val < 2 ^ 32 := by
  have := A_val h hr
  obtain ⟨h0, h1, h2, h3, -⟩ := ab_bytes h hr
  omega

/-- `B` is a u32 on every real row. -/
-- models: zkp-circuits/research/src/tables/alu.rs:203 @b3e21d9
theorem b_lt (h : AluRowOk m) (hr : m IS_REAL = 1) : (m B).val < 2 ^ 32 := by
  have := B_val h hr
  obtain ⟨-, -, -, -, h0, h1, h2, h3⟩ := ab_bytes h hr
  omega

end Rand.RV32.Alu
