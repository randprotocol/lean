import Rand.Bus

namespace Rand

/-- What a successful lookup on each RV32 table bus guarantees.  Each clause is the
content of the table's `preprocessed_trace`; bus names equal the
`LookupBus::new("…")` strings in `research/src/tables/mod.rs`.  Other buses claim
nothing. -/
def rv32Contract : String → List F → Prop
  -- models: zkp-circuits/research/src/tables/range.rs:52 @b3e21d9 (rows A = 0..255)
  | "RANGE8", [x] => x.val < 256
  -- models: zkp-circuits/research/src/tables/nibble.rs:64 @b3e21d9 (a, b < 16; AND = a & b)
  | "AND4", [x, y, z] => x.val < 16 ∧ y.val < 16 ∧ z.val = x.val &&& y.val
  -- models: zkp-circuits/research/src/tables/nibble.rs:65 @b3e21d9
  | "OR4", [x, y, z] => x.val < 16 ∧ y.val < 16 ∧ z.val = x.val ||| y.val
  -- models: zkp-circuits/research/src/tables/nibble.rs:66 @b3e21d9
  | "XOR4", [x, y, z] => x.val < 16 ∧ y.val < 16 ∧ z.val = x.val ^^^ y.val
  -- models: zkp-circuits/research/src/tables/range.rs:53 @b3e21d9 (POW2 = 2^A if A < 32 else 0, A < 256)
  | "POW2", [s, w] => s.val < 256 ∧ w.val = if s.val < 32 then 2 ^ s.val else 0
  | _, _ => True

end Rand
