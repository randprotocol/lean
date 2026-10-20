import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.ReduceModChar
import Mathlib.NumberTheory.LucasPrimality

/-!
# The Goldilocks field

`p = 2^64 - 2^32 + 1`, the base field of the Plonky3 AIRs, modelled as `ZMod p`.
Hand-written; models the field used by `rand_zkvm` (circuits pin in `SOURCES.toml`).
-/

namespace Rand

namespace Goldilocks

/-- The Goldilocks prime `2^64 - 2^32 + 1`. -/
def p : ℕ := 18446744069414584321

theorem p_eq : p = 2 ^ 64 - 2 ^ 32 + 1 := by norm_num [p]

end Goldilocks

open Goldilocks

/-- Lucas certificate part 1: `7^(p-1) = 1` in `ZMod p`, with `p` as a literal. -/
private theorem seven_pow_top : (7 : ZMod 18446744069414584321) ^ 18446744069414584320 = 1 := by
  reduce_mod_char

private theorem seven_pow_div_2 : (7 : ZMod 18446744069414584321) ^ 9223372034707292160 ≠ 1 := by
  reduce_mod_char
  decide

private theorem seven_pow_div_3 : (7 : ZMod 18446744069414584321) ^ 6148914689804861440 ≠ 1 := by
  reduce_mod_char
  decide

private theorem seven_pow_div_5 : (7 : ZMod 18446744069414584321) ^ 3689348813882916864 ≠ 1 := by
  reduce_mod_char
  decide

private theorem seven_pow_div_17 : (7 : ZMod 18446744069414584321) ^ 1085102592318504960 ≠ 1 := by
  reduce_mod_char
  decide

private theorem seven_pow_div_257 : (7 : ZMod 18446744069414584321) ^ 71777214277877760 ≠ 1 := by
  reduce_mod_char
  decide

private theorem seven_pow_div_65537 : (7 : ZMod 18446744069414584321) ^ 281470681743360 ≠ 1 := by
  reduce_mod_char
  decide

/-- Primality of `p` by a Lucas certificate: `7` has order `p - 1`, and
`p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`. (`norm_num` alone would trial-divide.)
The modular powers are evaluated by `reduce_mod_char` (square-and-multiply). -/
theorem p_prime : p.Prime := by
  have hfac : p - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by norm_num [p]
  refine lucas_primality p 7 ?_ ?_
  · have h : p - 1 = 18446744069414584320 := by norm_num [p]
    rw [h]
    exact seven_pow_top
  · intro q hq hdvd
    rw [hfac] at hdvd
    have e : ∀ r : ℕ, r.Prime → q ∣ r → q = r := fun r hr h =>
      (Nat.prime_dvd_prime_iff_eq hq hr).1 h
    have key : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
      rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
            · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
              · exact Or.inl (e 2 Nat.prime_two (hq.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl (e 3 (by norm_num) h))
            · exact Or.inr (Or.inr (Or.inl (e 5 (by norm_num) h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (e 17 (by norm_num) h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 257 (by norm_num) h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e 65537 (by norm_num) h)))))
    have hp : p - 1 = 18446744069414584320 := by norm_num [p]
    rw [hp]
    rcases key with rfl | rfl | rfl | rfl | rfl | rfl
    · have h : (18446744069414584320 : ℕ) / 2 = 9223372034707292160 := by norm_num
      rw [h]
      exact seven_pow_div_2
    · have h : (18446744069414584320 : ℕ) / 3 = 6148914689804861440 := by norm_num
      rw [h]
      exact seven_pow_div_3
    · have h : (18446744069414584320 : ℕ) / 5 = 3689348813882916864 := by norm_num
      rw [h]
      exact seven_pow_div_5
    · have h : (18446744069414584320 : ℕ) / 17 = 1085102592318504960 := by norm_num
      rw [h]
      exact seven_pow_div_17
    · have h : (18446744069414584320 : ℕ) / 257 = 71777214277877760 := by norm_num
      rw [h]
      exact seven_pow_div_257
    · have h : (18446744069414584320 : ℕ) / 65537 = 281470681743360 := by norm_num
      rw [h]
      exact seven_pow_div_65537

instance : Fact p.Prime := ⟨p_prime⟩

/-- The Goldilocks field. -/
abbrev F := ZMod p

/-- No wrap-around: the canonical value of a sum, given an explicit bound. -/
theorem val_add_of_lt {a b : F} (h : a.val + b.val < p) : (a + b).val = a.val + b.val := by
  rw [ZMod.val_add, Nat.mod_eq_of_lt h]

/-- No wrap-around: the canonical value of a product, given an explicit bound. -/
theorem val_mul_of_lt {a b : F} (h : a.val * b.val < p) : (a * b).val = a.val * b.val := by
  rw [ZMod.val_mul, Nat.mod_eq_of_lt h]

/-- Casting a small natural number into `F` and back is the identity. -/
theorem val_natCast_of_lt {n : ℕ} (h : n < p) : (n : F).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

end Rand
