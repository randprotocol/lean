import Rand.Field

namespace Rand

/-- Interaction kinds on a bus.  `lookup` consumes a table entry; `provide` is the
table side; `send`/`receive` are the two halves of a permutation bus. -/
inductive Kind | lookup | provide | send | receive
  deriving DecidableEq

/-- One bus interaction of an AIR row: a tuple on a named bus with a multiplicity. -/
structure Interaction where
  bus   : String
  kind  : Kind
  tuple : List F
  count : F

/-- Bus soundness assumption, in usable form: every *lookup* whose count is
nonzero hits a tuple satisfying the bus contract.  A gated-off lookup
(count `0`) and non-lookup kinds are not constrained. -/
def lookupsHold (contract : String → List F → Prop) (is : List Interaction) : Prop :=
  ∀ i ∈ is, i.kind = .lookup → i.count ≠ 0 → contract i.bus i.tuple

end Rand
