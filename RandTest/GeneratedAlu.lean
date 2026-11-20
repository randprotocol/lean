import Rand.Generated.RV32.Alu
import Rand.Generated.RV32.AluHonest

open Rand Rand.Generated.RV32.Alu

example : width = 64 := rfl

/-- Every row the real Rust trace generator produced (`alu_trace`, through the exporter)
satisfies every exported constraint, evaluated in the kernel. -/
theorem honestRows_accepted_bool :
    (honestRows.all fun r => (constraints r).all (· == 0)) = true := by
  decide

-- The statement in `Prop` form. (`decide` on it directly is hopeless: instance search
-- picks `Fintype.decidableForallFintype` for `∀ c : F` and enumerates all of `ZMod p`.)
example : ∀ r ∈ honestRows, ∀ c ∈ constraints r, c = 0 := by
  simpa [List.all_eq_true] using honestRows_accepted_bool

-- Not vacuous: the first honest row with its output `C` (column 21) bumped by one is refused.
example :
    (constraints (fun i => if i = ⟨21, by decide⟩ then honestRows.head! i + 1
      else honestRows.head! i)).all (· == 0) = false := by
  decide
