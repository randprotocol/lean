# Assumptions

Every assumption below matches a named Lean hypothesis (a `structure` field or
a theorem argument, never an `axiom`). The list is the initial one and grows
with the proofs.

- **Known gap: the Poseidon2 round constants are a development seed
  (`research/src/poseidon2_constants.rs`, listed in `research/AGENTS.md`), not
  the published constants. Replacing them changes every chain hash and needs a
  chain cut, which is outside this project; publication does not wait on it.**
- STARK/FRI soundness with the deployed parameters (RV32: blowup 3, 80
  queries, 20 PoW bits; rVM: blowup 4 per rate ¼, 92 queries, 24 PoW bits),
  and LogUp/permutation bus soundness ⇒ multiset equality.
- Poseidon2, BLAKE3, Keccak-f, SHA-256 behave as their bus contracts say.
- Dilithium2 EUF-CMA; validator signatures unforgeable.
- The Rust compiler, Plonky3 prover/verifier code, the RV32 guest toolchain,
  and the RV32→rVM constraint emitter are trusted.
- Honest replicas persist safety state before voting; < 1/3 Byzantine stake
  per epoch; epoch hand-off.
