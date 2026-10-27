# Lean verification of the Rand full node — design

Date: 2026-10-21. Status: draft for approval.
Pins this design was written against: fullnode `246cb5f9` (v0.8.0, chain 21),
circuits `b3e21d9` (rVM phase 5).
Note: fullnode v0.8.0 vendors circuits `d217252` (`CIRCUITS_PIN` in its ci.yml), an ancestor of
`b3e21d9`; this design reads `b3e21d9`, and `research/src/isa.rs`, `research/src/emulator.rs` and
`recursion/src/isa.rs` are identical at the two commits, so the specs transcribed from them
describe what v0.8.0 vendors. Re-check that before any claim about a later fullnode pin.

## 1. Intent

Build a Lean 4 project in its own public repository,
`https://github.com/randprotocol/lean` (checked out at `lean/` in the
monorepo, like the other repos), that machine-checks the
properties the Rand full node depends on: that the ZK circuits accept only
correct executions, and that the validator/ledger cannot finalize conflicting
blocks, double-spend, or create or destroy supply outside the stated rules.

It is for two audiences, and both shape it:

- **Auditors** — who will read the theorem statements, check the build, and
  ask "what exactly is assumed?".
- **The public** — the project is published openly as part of how Rand
  explains its security.

Because it is public, the single worst outcome is a claim larger than what was
proven. Every design choice below favours a smaller, exactly-stated claim over
a larger, vague one.

## 2. Goals, non-goals, anti-goals

**Goals**

1. Circuit soundness at the constraint level, for both proof machines (§4):
   every assignment the AIR constraints accept, given the lookup/permutation
   arguments balance, corresponds to a step of the reference emulator.
2. Validator safety: chained-HotStuff safety under < 1/3 Byzantine stake,
   nullifier uniqueness, total-supply conservation across every action,
   and the fee/gas bounds in §5.4. Gas-price band: 100 to 10 000 base units per
   gas (0.0000001 to 0.00001 RAND).
3. A public, honest account of what is proven and what is assumed, generated
   (where possible) from the build itself.
4. A mechanical tie between the Lean model and the Rust at a pinned commit,
   so the proofs cannot silently drift from the code.

**Non-goals (this design)**

- Proving the STARK/FRI protocol sound, or Poseidon2/BLAKE3/Keccak/SHA-256/
  Dilithium2 secure. These are cryptographic assumptions (§6).
- Proving the Rust compiler, Plonky3's prover/verifier code, the network,
  storage, mempool, RPC, or async runtime correct.
- Liveness of consensus (only safety).
- Proving the full Rust code equivalent to the model. Extraction of selected
  pure functions is a later milestone (M7), not the core deliverable.

**Anti-goals — a failure even if it builds**

- Any `sorry`, `admit`, or project-local `axiom` reachable from a published
  theorem.
- A cryptographic or engineering assumption stated as a Lean `axiom` rather
  than as an explicit named hypothesis the theorem takes.
- A public page that says "verified" about something only partly covered.
- Lean constraints hand-copied from Rust with no check that they still match.

## 3. Constraints

- Lean 4 + Mathlib, toolchain pinned in `lean-toolchain`, Mathlib pinned in
  `lake-manifest.json`. Neither is installed on the dev Mac today (`elan` is
  absent); installing `elan` is part of M0.
- The Goldilocks field `p = 2^64 − 2^32 + 1` is modelled as `ZMod p`;
  the degree-2 extension as the binomial extension Plonky3 uses.
- Proofs must check in CI in reasonable time (target: full build < 30 min on
  a GitHub runner, using Mathlib's cache).
- Pushes go over `gh` HTTPS as `dendisuhubdy`; the SSH identity is suspended.
- The monorepo is private; `fullnode` and the circuits repo are public. CI in
  the `lean` repo clones those two at the commits in `SOURCES.toml`, so anyone
  can reproduce the build without monorepo access.
- **Scope of ledger theorems:** the chain-21 genesis parameters
  (`fullnode/deploy/genesis-chain21.json`). Every public statement says
  "under chain-21 genesis". Generalising over all accepted genesis
  configurations is a later milestone.

## 4. Circuits

There are two STARK machines, both Plonky3 0.7.0 over Goldilocks. Both crates
already state the rule this project formalises: **the emulator is the
reference semantics; if the AIR disagrees with it, the AIR is wrong**
(`research/AGENTS.md:300`, `recursion/src/lib.rs:27–28`, both at circuits `b3e21d9`).

### 4.1 Where the constraints come from (decided)

Constraints are **generated from the Rust, not hand-copied**. A small Rust
exporter (in `circuits`, e.g. `tools/air2lean`) calls Plonky3's
`get_symbolic_constraints` for each chip and its bus interactions, and prints
a Lean file per chip: the column layout, each constraint polynomial, and each
`send/receive/lookup` with its multiplicity. `recursion/src/programs/
constraints.rs` already walks the same symbolic DAG to emit rVM code, so the
mechanism exists.

The generated files are committed under `lean/Rand/Generated/` with the
circuits commit they came from in a header. CI re-runs the exporter at the
pinned commit and fails on any diff. This is the drift guard for circuits.

### 4.2 The specs

- **RV32 machine** (`circuits/research`): RV32IM subset, 19 `AluOp`s,
  9 syscalls (`SYS_HALT` 0 … `SYS_MODQ` 8, `research/src/isa.rs:12–71`). Lean spec transcribed from `research/src/isa.rs`
  (`AluOp::eval` :94, `BranchCond::taken` :135, decode :279) and
  `research/src/emulator.rs::execute` :179, cross-read with
  `research/docs/01-isa.md` (incl. deviations ISA-4/ISA-5).
- **rVM** (`circuits/recursion`): 30 opcodes (`recursion/src/isa.rs:45–128`),
  32 registers, `r0 = 0`, addresses < 2^24, timestamps `16·clk + slot`.
  Spec from `recursion/src/emulator.rs::execute` :224.

The Lean specs are hand-written (the emulators use `HashMap`/event logs and
are not extraction-friendly) and each definition carries a comment naming the
Rust file, line and commit it models.

### 4.3 What is proven, per table

For each chip: **row soundness** — if a row (or row pair, for transitions)
satisfies the generated constraints, and the values it receives over lookup
buses are in the ranges those buses certify (e.g. RANGE8 ⇒ < 256), then the
row's outputs equal the spec function of its inputs. For the ALU this is
"output uniqueness and correctness for all 19 ops"; `research/tools/alu_z3`
already shows it for 9 ops and times out on the rest.

Then the **cross-table arguments**:

- Buses are modelled abstractly: a balanced LogUp/permutation bus is taken as
  multiset equality of sends and receives (the cryptographic step — that a
  balanced terminal sum implies multiset equality except with negligible
  probability — is an assumption, §6).
- **Memory consistency**: given multiset equality between cpu/chip accesses
  and the sorted memory table, prove read-after-write, first-read-is-zero,
  and strict `(addr, ts)` ordering from the 4×RANGE8 `delta` limbs. This is
  the offline memory-checking argument; both machines use it.
- **Whole-machine theorem** (per machine): an accepted trace set corresponds
  to a run of the emulator from the program's initial state, with the public
  values the emulator outputs.

### 4.4 Regression proofs for past bugs

Each previously-fixed forgery gets a Lean witness that the **old** constraint
set admits a bad row and the current one does not:

- ALU padding-row MULT forgery (`fib(10)=999`), fixed at
  `research/src/tables/alu.rs:186–195`.
- Unpinned store `MEM_VAL` (`2c8a39d`).
- ZKQ-3 multi-cell range wrap (`98554a2`), RVM-1 STOREE lane (`b786aae`).

These demonstrate the proofs have teeth, and are good public material.

### 4.5 Tables in scope, in order

RV32: alu → memory → range/nibble → program/decode → cpu → input/public →
poseidon2 (as a bus-level black box: constrained ↔ permutation, assumed
correct) → modq. Keccak and sha256 are treated like poseidon2 (bus contract
only) in this design.

rVM (not used by the live chain: chain-21 genesis has no `aggregation`
section, so results here are labelled "not yet active on chain 21"): memory (REG, RAM) → program → cpu → public → range → poseidon2 (bus
contract) → reduce (FRI fold; degree 8, 90 assert sites, hardest).

### 4.6 The programs the chain accepts proofs from

The machine theorem says "this proof is an honest run of program P". The
ledger's no-double-spend and value-balance claims additionally need P to be
right. Chain 21 accepts RV32 proofs from `hc_bundle` and `hc_auth`
(hand-assembled in `research/src/guests.rs`, no compiler involved) and from
msauth. **In scope (milestone M5b):** a program logic over the Lean RV32 spec,
and proofs that `hc_bundle` emits exactly one nullifier per spent note
(deterministic from the note and its key) and enforces value balance, and that
`hc_auth` binds the authorising key. These are what make §5.2 an end-to-end
statement rather than a conditional one; until M5b lands, `PROVEN.md` states
§5.2 as conditional on the bundle program's statement.

### 4.7 msauth and the constraint emitter

- **msauth** (M-of-N Dilithium2, M_MAX 3): state the guest's intended
  statement in Lean and prove the *host model* (`research/src/msauth.rs`)
  meets it, given Dilithium2 EUF-CMA as an assumption. The guest binary's
  compiled code is out of scope (trusted compiler).
- The rVM programs that verify RV32 proofs (`verify_rv32`, `rv32n`, `rv32r`,
  `rv32t`) and the emitter in `recursion/src/programs/constraints.rs` are
  **listed as trusted** in this design. Verifying the emitter is a named
  follow-up (it is the link that makes aggregation sound).

## 5. Validator and ledger

All under `fullnode/crates/randprotocol-core/src` unless noted. The model is
hand-written; each definition names the Rust it models.

### 5.1 Consensus safety

Chained HotStuff, three-chain commit, round-robin leader over a
stake-weighted set.

- Quorum: `stake·3 > total·2` (`types/validator.rs:70`), third: `stake·3 >
  total` (:77), leader `validators[view % n]` (:87).
- Vote rule (`consensus/hotstuff.rs:1920–1923`): vote only if
  `block.view > last_voted_view ∧ block.view = view` and
  (`justify.view > locked_qc.view` ∨ block extends the locked block).
- Lock and commit: `update_lock_and_commit` :1675, `consecutive_views` :51,
  sync path `consensus/commit_rule.rs:28`.
- QC validity: `QuorumCertificate::verify_with` (`types/block.rs:140`) —
  same view/hash, voters in set, no duplicates, quorum; signatures abstracted
  as an unforgeability hypothesis.

Model: an abstract state machine over a block tree, honest replicas following
the rules, Byzantine replicas arbitrary, persistence of `SafetyState` before
broadcast assumed (it is, per the code). **Theorem:** if Byzantine stake is
< 1/3 of total within an epoch, no two conflicting blocks are both committed.
Epoch changes (`staking.rs:473 derive_set`) are handled by proving safety per
epoch with the hand-off as a stated assumption in this design; cross-epoch
safety is a named follow-up. The operator override `release_lock` is outside
the honest model and the public page says so.

### 5.2 Nullifier uniqueness

From the ledger model (`ledger/mod.rs` `is_spent` :2102, `apply_bundle_notes`
:2192, `shared_set.rs`): a block that applies successfully never spends a
nullifier already spent, and never spends one twice within the block. The
MMR root (`nullifier_mmr.rs`) is modelled with an uninterpreted hash; prove
append/root agree with the set.

### 5.3 Supply conservation

The code already checks, in ~20 test files, the identity at
`ledger/supply.rs:299`:

```
total_supply = issued − slashed − registration_fees_burned − base_fees_burned
total_supply = pool + register + vesting + program vaults + perps + multisig
```

**Theorem:** every successful `apply` of every `Action` (45 variants,
`types/transaction.rs:88`) preserves it, and so does `close_block`.
Each action is modelled by its balance deltas only; the parts of an action
that are proof-verified (e.g. a shielded transfer's value balance) take the
verifier's statement as a hypothesis. Token backing (`tokens.rs:1181`) is a
separate, later theorem.

Arithmetic: the Rust uses `saturating_*` and u128 sums. The model uses
bounded naturals with saturation made explicit, and the theorem either
proves saturation unreachable under a stated supply bound or states it as a
hypothesis — whichever is true; the builder finds out.

### 5.4 Fees and gas

From `core/gas.rs`, `ledger/fees.rs`, `ledger/mod.rs`:

- **Gas-price band:** whatever the load sequence, the price produced by
  `next_price_capped` (`gas.rs:300`) stays in
  `[floor, 100·floor]`, with floor = 100 base units/gas (0.0000001 RAND) at
  genesis. Bytes are priced separately; same style of bound for the byte
  price.
- **Minimum transfer fee:** the user chooses the fee; the ledger accepts a
  shielded transfer only if fee ≥ `BUNDLE_BASE + prove_base`
  (`ledger/mod.rs:2638–2648`, `gas::fee_floor`). Theorem: under chain-21
  genesis that minimum is exactly 0.001 RAND, a transfer paying less is
  refused, and gas/byte prices do not enter it. Plus: the amount burned vs
  paid to the proposer, per `bundle_fee_split`.
- **Floor is genesis-fixed:** no action or governance vote changes the
  minimum gas price; changing it requires a new genesis or activation height.
- Subsidy halving (`gas::subsidy` :676, zero from the 64th halving), USD
  subsidy `min(usd·10⁹/price, cap)` (`fees.rs:107`), `SetRandPrice` ±2× band
  with > 2/3 validator weight (`rand_price.rs:160`).

The $ price of RAND is not part of any theorem.

### 5.5 Perps and multisig (later)

Margin/liquidation live in the engine guest
(`circuits/durian-market/perp-core/src/clearing.rs`, `engine.rs`), not the
node. Its invariant (`engine.rs:34`) and `equity`/`maintenance_margin` are
good M7 extraction targets. Multisig signer checks (`multisig.rs:81`) likewise.

## 6. Assumptions page (public)

`lean/ASSUMPTIONS.md` lists every assumption, each matching a named Lean
hypothesis (a `structure` field or theorem argument, never an `axiom`):

- STARK/FRI soundness with the deployed parameters (RV32: blowup 3, 80
  queries, 20 PoW bits; rVM: blowup 4 per rate ¼, 92 queries, 24 PoW bits),
  and LogUp/permutation bus soundness ⇒ multiset equality.
- Poseidon2, BLAKE3, Keccak-f, SHA-256 behave as their bus contracts say.
  **Known gap, stated prominently:** the Poseidon2 round constants are a
  development seed (`research/src/poseidon2_constants.rs`, listed in
  `research/AGENTS.md`), not the published constants. Replacing them changes
  every chain hash and needs a chain cut, which is outside this project;
  publication does not wait on it.
- Dilithium2 EUF-CMA; validator signatures unforgeable.
- The Rust compiler, Plonky3 prover/verifier code, the RV32 guest toolchain,
  and the RV32→rVM constraint emitter are trusted.
- Honest replicas persist safety state before voting; < 1/3 Byzantine stake
  per epoch; epoch hand-off (§5.1).

`lean/PROVEN.md` lists each published theorem: plain-English statement, Lean
name, Rust source it models with commit, and the assumptions it takes. A CI
step runs `#print axioms` on each published theorem and fails unless the
result is within `propext`, `Classical.choice`, `Quot.sound`; the output is
committed alongside.

## 7. Tie to the code

- `lean/SOURCES.toml` pins the fullnode and circuits commits the model was
  checked against.
- Circuits: the exporter diff check (§4.1) — hard failure.
- Validator: each model definition carries a source anchor
  (`-- models: crates/randprotocol-core/src/types/validator.rs:70 @246cb5f9`).
  A CI script hashes the referenced Rust function bodies at the pinned commit
  and, when a new pin is proposed, reports which anchors' bodies changed.
  This is a review prompt, not proof of correspondence; `PROVEN.md` says so.

## 8. Milestones

Each ends with green CI, no `sorry`, updated `PROVEN.md`.

- **M0 — Scaffold.** `elan`, Lake project `Rand`, Mathlib, CI (build, axiom
  audit, sorry/axiom grep), `ASSUMPTIONS.md`, `PROVEN.md`, `SOURCES.toml`,
  Goldilocks `ZMod p` + extension basics.
- **M1 — RV32 ALU.** `air2lean` exporter; generated ALU constraints; spec of
  the 19 ops; row soundness for all 19; MULT-forgery regression witness.
  First public result.
- **M2 — RV32 memory + buses.** Range/nibble contracts, memory table,
  offline memory-checking theorem.
- **M3 — HotStuff safety.**
- **M4 — Economics.** Gas band, fixed transfer fee, floor-is-genesis,
  subsidies, supply conservation over all 45 actions, nullifier uniqueness.
- **M5 — RV32 rest.** program/decode, cpu, input/public, modq; whole-machine
  theorem.
- **M5b — Accepted programs.** RV32 program logic; `hc_bundle` and
  `hc_auth` statements (§4.6); §5.2 becomes unconditional.
- **M6 — rVM.** memory, program, cpu, public, range, reduce; whole-machine
  theorem.
- **M7 — Extraction.** Aeneas or hax on pure functions (quorum check, fee
  and subsidy functions, `AluOp::eval`, modq NTT, perp margin), proving the
  extracted Rust equals the hand-written spec.

## 9. Left to the builder

- Exact Lean/Mathlib versions; project layout under `lean/Rand/`.
- Exporter implementation details and output format, provided it is
  deterministic and covers bus interactions.
- Proof techniques (`decide`, `omega`, `polyrith`, `grind`, bit-blasting)
  per table; whether to split very wide chips (keccak 2612 columns) by row
  kind.
- How to model the block tree and Byzantine behaviour in M3.
- Whether Aeneas or hax for M7.

## 10. Calls made by Claude (not decided by the user)

- Generated-not-hand-copied constraints with a CI diff check (§4.1).
- Crypto and trust assumptions as named hypotheses, never `axiom`s (§6).
- Poseidon2/Keccak/SHA-256 as bus contracts, not proven.
- msauth: host model against its statement; compiled guest trusted.
- Per-epoch consensus safety first; cross-epoch later.
- Milestone order: RV32 ALU first (user agreed), then memory, then consensus.
- Location of this design under `docs/specs/` in the `lean` repo.
- Proving `hc_bundle`/`hc_auth` in scope as M5b (recommended to the user;
  not yet explicitly confirmed).
- Publish with the Poseidon2 gap stated rather than waiting for a chain cut
  (recommended to the user; not yet explicitly confirmed).
- Ledger theorems scoped to chain-21 genesis first.
- rVM results labelled not-yet-active (no aggregation in chain-21 genesis).
- Fee theorem is about the minimum accepted fee, not a fixed payment.
