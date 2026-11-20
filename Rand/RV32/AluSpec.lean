import Mathlib.Tactic.Common
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Int.Bitwise

/-!
# The RV32 ALU reference function

`AluOp.eval` is the Lean transcription of `AluOp::eval` in `rand_zkvm::isa`: u32 values are
`ℕ` below `2^32`, signed operations go through the two's-complement helpers `toSigned32` and
`ofSigned32`. Later tasks prove that the ALU chip's constraints compute exactly this function;
`RandTest/AluVectors.lean` checks it against the Rust on exporter-generated vectors.
-/

namespace Rand

/-- Two's-complement reading of a u32. -/
def toSigned32 (n : ℕ) : ℤ := if n < 2 ^ 31 then (n : ℤ) else (n : ℤ) - 2 ^ 32

/-- Wrap an integer into a u32 (`as u32`). -/
def ofSigned32 (z : ℤ) : ℕ := (z % 2 ^ 32).toNat

theorem ofSigned32_lt (z : ℤ) : ofSigned32 z < 2 ^ 32 := by
  have h0 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h1 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  unfold ofSigned32
  omega

/-- The 19 ALU operations, in the Rust enum's order. -/
inductive AluOp
  | add | sub | and | or | xor | sll | srl | sra | slt | sltu | eq
  | mul | mulh | mulhu | mulhsu | div | divu | rem | remu
  deriving DecidableEq, Repr

namespace AluOp

/-- All operations in code order (`AluOp::ALL`). -/
def all : List AluOp :=
  [add, sub, and, or, xor, sll, srl, sra, slt, sltu, eq,
   mul, mulh, mulhu, mulhsu, div, divu, rem, remu]

/-- The numeric code `0..18` (`AluOp::code`). -/
def code : AluOp → ℕ
  | add => 0 | sub => 1 | and => 2 | or => 3 | xor => 4 | sll => 5 | srl => 6
  | sra => 7 | slt => 8 | sltu => 9 | eq => 10 | mul => 11 | mulh => 12
  | mulhu => 13 | mulhsu => 14 | div => 15 | divu => 16 | rem => 17 | remu => 18

/-- Inverse of `code`; `none` outside `0..18` (Rust's `from_code` panics there). -/
def ofCode? : ℕ → Option AluOp
  | 0 => some add | 1 => some sub | 2 => some and | 3 => some or | 4 => some xor
  | 5 => some sll | 6 => some srl | 7 => some sra | 8 => some slt | 9 => some sltu
  | 10 => some eq | 11 => some mul | 12 => some mulh | 13 => some mulhu
  | 14 => some mulhsu | 15 => some div | 16 => some divu | 17 => some rem
  | 18 => some remu | _ => none

/-- Reference semantics on u32 values.  `s = b & 31` is the shift amount; division by zero
gives `0xffffffff` (`rem` gives `a`), and `MIN / -1` gives `MIN` (`MIN % -1` gives `0`). -/
-- models: zkp-circuits/research/src/isa.rs:94 @b3e21d9
def eval (o : AluOp) (a b : ℕ) : ℕ :=
  let s := b &&& 31
  match o with
  | add => (a + b) % 2 ^ 32
  | sub => ofSigned32 ((a : ℤ) - b)
  | and => a &&& b
  | or => a ||| b
  | xor => a ^^^ b
  | sll => (a <<< s) % 2 ^ 32
  | srl => a >>> s
  | sra => ofSigned32 (toSigned32 a >>> s)
  | slt => if toSigned32 a < toSigned32 b then 1 else 0
  | sltu => if a < b then 1 else 0
  | eq => if a = b then 1 else 0
  | mul => (a * b) % 2 ^ 32
  | mulh => ofSigned32 ((toSigned32 a * toSigned32 b) >>> 32)
  | mulhu => (a * b) >>> 32
  | mulhsu => ofSigned32 ((toSigned32 a * (b : ℤ)) >>> 32)
  | div =>
      if b = 0 then 0xffffffff
      else if a = 0x80000000 ∧ b = 0xffffffff then 0x80000000
      else ofSigned32 (Int.tdiv (toSigned32 a) (toSigned32 b))
  | divu => if b = 0 then 0xffffffff else a / b
  | rem =>
      if b = 0 then a
      else if a = 0x80000000 ∧ b = 0xffffffff then 0
      else ofSigned32 (Int.tmod (toSigned32 a) (toSigned32 b))
  | remu => if b = 0 then a else a % b

/-- Every operation maps u32 values to a u32 value. -/
theorem eval_lt (o : AluOp) {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    o.eval a b < 2 ^ 32 := by
  cases o <;> simp only [eval]
  · exact Nat.mod_lt _ (by norm_num)
  · exact ofSigned32_lt _
  · exact Nat.and_lt_two_pow _ hb
  · exact Nat.or_lt_two_pow ha hb
  · exact Nat.xor_lt_two_pow ha hb
  · exact Nat.mod_lt _ (by norm_num)
  · rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · exact ofSigned32_lt _
  · split <;> norm_num
  · split <;> norm_num
  · split <;> norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · exact ofSigned32_lt _
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by norm_num)]
    calc a * b < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 32 * 2 ^ 32 := rfl
  · exact ofSigned32_lt _
  · split
    · norm_num
    · split
      · norm_num
      · exact ofSigned32_lt _
  · split
    · norm_num
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · split
    · exact ha
    · split
      · norm_num
      · exact ofSigned32_lt _
  · split
    · exact ha
    · exact lt_of_le_of_lt (Nat.mod_le _ _) ha

end AluOp

end Rand
