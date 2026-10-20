import Rand.RV32.AluSpec
import Rand.Generated.RV32.AluVectors
import Rand.Generated.RV32.Alu

/-! Review Focus 3: the Lean `AluOp.eval` agrees with the Rust `AluOp::eval` on every
exporter-generated vector (the 9x9 edge set, which includes division by zero, `MIN / -1`,
shifts by 32 and above, and the `mulhsu` sign cases, plus 64 seeded-random pairs per op). -/

open Rand Rand.Generated.RV32.AluVectors

-- The 'Bool' form: `decide` on a `∀ x ∈ list` Prop can pick an instance enumerating a huge type.
set_option maxRecDepth 100000
theorem aluVectors_agree :
    aluVectors.all (fun (c, a, b, r) => (AluOp.ofCode? c).map (·.eval a b) == some r) = true := by
  decide

-- Not vacuous: every op is exercised, and a corrupted result is refused.
example : AluOp.all.length = 19 ∧ aluVectors.length = 19 * 145 := by decide
example : (aluVectors.filter (·.1 == 18)).length = 145 := by decide
example : ((15, 0x80000000, 0xffffffff, 0) :: aluVectors).all
    (fun (c, a, b, r) => (AluOp.ofCode? c).map (·.eval a b) == some r) = false := by decide

/-- `ofCode?` and `code` are inverse, and out-of-range codes are refused. -/
example : AluOp.all.all (fun o => AluOp.ofCode? o.code == some o) = true := by decide
example : AluOp.ofCode? 19 = none := by decide

/-- Bus-rename guard: every `.lookup` interaction of the ALU names a bus that `rv32Contract`
constrains (its fallback is `True`, so a renamed bus would make the lookup vacuous). -/
example : ((Rand.Generated.RV32.Alu.interactions (fun _ => 0)).all fun i =>
    i.kind != .lookup || ["RANGE8", "AND4", "OR4", "XOR4", "POW2"].contains i.bus) = true := by
  decide
