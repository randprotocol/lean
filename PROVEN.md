# Proven

| Theorem | Plain statement | Lean name | Models | Assumptions |
|---|---|---|---|---|

## Scope

Statements are about the Rand chain-21 genesis configuration and the circuits
commit pinned in [`SOURCES.toml`](SOURCES.toml). Source anchors
(`-- models: <repo>/<path>:<line> @<commit>`) are a review prompt: a CI script
reports which anchored Rust bodies changed when a new pin is proposed. They are
not a proof that the Lean model corresponds to the Rust code.

CI runs `#print axioms`-style checks (`scripts/audit.sh`) on every published
theorem and fails unless the result is within `propext`, `Classical.choice`,
`Quot.sound`. See [`ASSUMPTIONS.md`](ASSUMPTIONS.md) for what the theorems take
on trust.
