import Rand.Generated.RV32.Tables

/-! Review Focus 2: the RV32 lookup contracts (`Rand.rv32Contract`) against the generated
contents of the fixed tables' `preprocessed_trace`s. -/

open Rand.Generated.RV32.Tables

-- The 256-row lists nest deeper than the default recursion limit when `decide` unfolds them.
set_option maxRecDepth 8000

-- range.rs: rows A = 0..255 in order (the RANGE8 contract `x < 256`).
example : range8Rows.map (·.1) = List.range 256 := by decide

-- range.rs: POW2 = 2^A for A < 32, else 0 (the POW2 contract), and IS_POW2 = [A < 32].
example : ∀ r ∈ range8Rows, r.2.1 = if r.1 < 32 then 2 ^ r.1 else 0 := by decide
example : ∀ r ∈ range8Rows, r.2.2 = if r.1 < 32 then 1 else 0 := by decide

-- nibble.rs: 256 rows, a, b < 16 and AND/OR/XOR columns are the bitwise ops (AND4/OR4/XOR4).
example : nibbleRows.length = 256 := by decide
example : ∀ r ∈ nibbleRows, r.1 < 16 ∧ r.2.1 < 16 ∧ r.2.2.1 = r.1 &&& r.2.1 ∧
    r.2.2.2.1 = r.1 ||| r.2.1 ∧ r.2.2.2.2 = r.1 ^^^ r.2.1 := by decide
-- … and every nibble pair occurs (the contracts claim no pair is missing a row).
example : nibbleRows.map (fun r => (r.1, r.2.1)) =
    (List.range 16).flatMap (fun a => (List.range 16).map (fun b => (a, b))) := by decide
