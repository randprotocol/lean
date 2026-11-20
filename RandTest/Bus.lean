import Rand.Bus
import Rand.RV32.Contracts

open Rand

-- A gated-off lookup (count 0) with an out-of-table tuple is not binding.
example : lookupsHold rv32Contract [⟨"RANGE8", .lookup, [300], 0⟩] := by
  intro i hi _ hc
  simp at hi
  subst hi
  simp at hc

-- A live lookup with an out-of-table tuple violates the contract.
example : ¬ lookupsHold rv32Contract [⟨"RANGE8", .lookup, [300], 1⟩] := by
  intro h
  have := h ⟨"RANGE8", .lookup, [300], 1⟩ (by simp) rfl (by simp)
  simp [rv32Contract] at this
  have h300 : ((300 : F)).val = 300 := val_natCast_of_lt (n := 300) (by norm_num [Goldilocks.p])
  omega

-- send/receive are not constrained by lookupsHold.
example : lookupsHold rv32Contract [⟨"RANGE8", .send, [300], 1⟩] := by
  intro i hi hk _
  simp at hi
  subst hi
  cases hk

example : rv32Contract "POW2" [40, 0] := by
  have h : ((40 : F)).val = 40 := val_natCast_of_lt (n := 40) (by norm_num [Goldilocks.p])
  simp [rv32Contract, h]

example : rv32Contract "POW2" [5, 32] := by
  have h : ((5 : F)).val = 5 := val_natCast_of_lt (n := 5) (by norm_num [Goldilocks.p])
  have h2 : ((32 : F)).val = 32 := val_natCast_of_lt (n := 32) (by norm_num [Goldilocks.p])
  simp [rv32Contract, h, h2]

example : ¬ rv32Contract "POW2" [40, 2^40] := by
  have h : ((40 : F)).val = 40 := val_natCast_of_lt (n := 40) (by norm_num [Goldilocks.p])
  have h2 : (((2^40 : ℕ) : F)).val = 2^40 := val_natCast_of_lt (by norm_num [Goldilocks.p])
  have e : ((2 : F)^40) = ((2^40 : ℕ) : F) := by push_cast; rfl
  intro hc
  have hc2 := hc.2
  rw [e, h2, h] at hc2
  norm_num at hc2

example : rv32Contract "AND4" [12, 10, 8] := by
  have a : ((12 : F)).val = 12 := val_natCast_of_lt (n := 12) (by norm_num [Goldilocks.p])
  have b : ((10 : F)).val = 10 := val_natCast_of_lt (n := 10) (by norm_num [Goldilocks.p])
  have c : ((8 : F)).val = 8 := val_natCast_of_lt (n := 8) (by norm_num [Goldilocks.p])
  simp [rv32Contract, a, b, c]

example : ¬ rv32Contract "XOR4" [12, 10, 8] := by
  have a : ((12 : F)).val = 12 := val_natCast_of_lt (n := 12) (by norm_num [Goldilocks.p])
  have b : ((10 : F)).val = 10 := val_natCast_of_lt (n := 10) (by norm_num [Goldilocks.p])
  have c : ((8 : F)).val = 8 := val_natCast_of_lt (n := 8) (by norm_num [Goldilocks.p])
  simp [rv32Contract, a, b, c]

example (t : List F) : rv32Contract "ALU" t := trivial
