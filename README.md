# Rand: Lean 4 formal verification

Public Lean 4 / Mathlib formalization of parts of the Rand blockchain full node
and its zero-knowledge circuits. Constraints of the Plonky3 AIRs are exported
from the Rust source and soundness is proved against them; the first target is
the RV32 ALU chip.

- [`PROVEN.md`](PROVEN.md): each published theorem, in plain English, with its Lean name, the Rust it models and the assumptions it takes.
- [`ASSUMPTIONS.md`](ASSUMPTIONS.md): everything taken on trust, including a known Poseidon2 constants gap.
- [`SOURCES.toml`](SOURCES.toml): the exact fullnode and circuits commits the model was checked against.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`.

```
lake exe cache get   # prebuilt Mathlib; do not build Mathlib from source
lake build
lake build RandTest
scripts/audit.sh     # no sorry/admit/axiom/native_decide; published theorems use only propext, Classical.choice, Quot.sound
```

The field is Goldilocks, `p = 2^64 - 2^32 + 1`, modelled as `ZMod p` (`Rand/Field.lean`).

## License

GPL-3.0, see `LICENSE`.
