# LANTERN formal design oracle

This offline reference model tests the evidence and simulated-ledger rules behind
LANTERN's proposed decision receipts. It does not run an agent, connect to Alpha,
or validate a Python application. The application remains a separate proposal.

Use Lean 4.35.0 through Elan; `lean-toolchain` pins the version. There are no
third-party Lean packages. From this directory, run:

```bash
python3 tools/verify.py
```

The acceptance lane builds the executable, audits theorem dependencies, replays
stored proofs through the bundled Lean kernel, checks concrete Lean examples,
runs JSON fixtures, defeats three weakened guards, and explores a bounded state
space. The fresh proof replay also checks imports and can take several minutes;
it is not an independent checker. The lane writes `reports/latest.json` and
`reports/axioms.txt`. Generated reports are ignored by Git and include the source
digest needed to identify their inputs. `PASS` concerns this lane only;
application conformance is explicitly `NOT_RUN`.

## What is proved

`Lantern/Model.lean` defines the state machine. `Lantern/Proofs.lean` proves that
each accepted transition preserves its invariants and that every accepted replay
from the empty state satisfies them, for arbitrary finite traces and natural-number
identifiers. These proofs are independent of the explorer's small bounds.

| Guarantee | Meaning and principal theorem |
| --- | --- |
| Supported observed evidence | Each accepted citation matches a recorded successful outcome with the same run, attempt, and artifact. `observed_references_supported` |
| Honest coverage | Every registered attempt in a run labeled complete has a definitive success or failure. `complete_receipts_have_outcomes` |
| Retry safety | The simulated ledger contains at most one entry for each `(run, operation)` key. `commitment_keys_nodup` |
| Exact duplicate handling | Repeating an existing commitment returns the identical state, including after sealing. `duplicate_commit_idempotent` |
| Payload conflict handling | Under the consistency invariant, the same key with a different payload is rejected. `conflicting_commit_rejected` |

The receipt predicate also checks that references belong to the requested run;
`receipt_validation_sound` proves its stated reference and coverage guarantees.
`timeout_does_not_create_outcome` distinguishes uncertainty from completion.
`checkState_iff` connects the executable invariant check to the proved predicate.

The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`, the
standard Lean foundations. It rejects other dependencies, including proof holes
or native-evaluation axioms. The [Lean validation reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains this distinction. Human review of the statements is still required.

## State and transition contract

Requests identify a run, logical operation, attempt, and opaque payload. Attempts
are unique within a run. A retry uses a new attempt ID while retaining the operation
and payload. Outcomes identify a run and attempt, with either failure or a success
artifact. Timeouts are stored separately. Evidence references, commitments, sealed
runs, and complete runs complete the state.

Dispatch must precede its outcome; definitive outcomes cannot be overwritten.
A late success can resolve a timeout before sealing. Citations require matching
success. A commitment requires a successful request matching its run, operation,
and payload. It records one simulated ledger entry, not an external payment.
Finalization seals a run; a complete finalization additionally requires coverage.
Sealed runs reject changes, except exact commitment retries returning cached state.

`cite` admits a reference as observed evidence. It does not represent every source
mentioned in model text. Preserve raw mentions and rejected actions in the original
record; unsupported mentions must not become observed edges. The oracle rejects
unsafe transitions rather than rewriting that record. A future adapter must keep
these meanings distinct.

These are safety rules. They do not prove eventual completion, budget compliance,
user consent, the correctness of a selection, or the truth of returned content.
Coverage can be complete even when the task failed. An empty run is vacuously
covered. The future UI must keep coverage and task success separate.

## JSON interface

Build with `lake build`, then pass one document on standard input:

```bash
.lake/build/bin/oracle <<'EOF'
{"events":[
  {"kind":"dispatch","run":0,"operation":0,"attempt":0,"payload":0},
  {"kind":"succeed","run":0,"attempt":0,"artifact":7},
  {"kind":"cite","run":0,"attempt":0,"artifact":7},
  {"kind":"commit","run":0,"operation":0,"payload":0},
  {"kind":"finalize","run":0,"complete":true}
]}
EOF
```

All IDs are nonnegative integers. Each event requires exactly these fields:

| `kind` | Remaining fields |
| --- | --- |
| `dispatch` | `run`, `operation`, `attempt`, `payload` |
| `succeed` | `run`, `attempt`, `artifact` |
| `fail`, `timeout` | `run`, `attempt` |
| `cite` | `run`, `attempt`, `artifact` |
| `commit` | `run`, `operation`, `payload` |
| `finalize` | `run`, `complete` (Boolean) |

Accepted output has `accepted: true` and `state`, including chronological arrays
and per-run coverage summaries. Rejected output has `accepted: false`, `category`,
and a zero-based failing event `index`. A malformed document has category
`malformed_input`; its index is null if no event could be identified. Rejection is
a verdict with exit code zero; invalid command-line usage returns exit code two.
Only the first failing event is reported. Extra fields are rejected. JSON parsing,
serialization, compiled execution, and I/O are tested boundaries, not proved by the
state-machine theorems. The compiled interface is an offline development tool.

Stable transition errors: `run_sealed`, `attempt_exists`,
`operation_payload_conflict`, `request_missing`, `outcome_exists`,
`unsupported_evidence`, `commit_payload_conflict`, `commit_unconfirmed`, and
`incomplete_coverage`.

## Adversarial evidence and limits

`fixtures/traces.json` contains independently specified expected verdicts and
selected state fields. Valid witnesses exclude a reject-everything oracle. Full-state
comparisons check duplicate idempotence. `Lantern/Examples.lean` checks concrete
receipt cases by kernel reduction.

`oracle --mutants` uses breadth-first search over eight events with one identifier
per domain. Removing citation support produces a one-event counterexample;
removing complete-coverage checking takes two events; duplicating an existing
commitment takes four. The last trace remains legal in the baseline: its required
behavior is one ledger entry, whereas the mutant creates two. The report saves
each shortest trace within this alphabet and its violating state.

`oracle --explore` uses two values each for runs, operations, attempts, payloads,
and artifacts: 52 event choices, maximum trace length six, at most 50,000 states.
It deduplicates exact states and checks every accepted transition it visits.
The current run reached the state cap while expanding depth four, discovering
some depth-five states and no depth-six states. This is partial bounded evidence;
it does not establish exhaustive depth-six coverage. See the generated report for
counts and truncation. Universal safety comes from the proofs above.

Trust assumes one coordinator serializes observations, the recorder registers the
relevant calls, and run/key/payload identities faithfully represent their contents.
Missing dispatches, forged outcomes, bypassed tools, external effects, concurrent
coordinators, and crash recovery are outside the guarantee. Identifiers are not
cryptographic attestations. No fairness, causal influence, hidden-motive detection,
or method novelty follows from these results.

## Review and next use

Review the model's meanings and trust boundaries before treating it as a contract
for the application. Once a real runner exists, feed its exported traces to this
oracle and compare its receipts and final simulated ledger with oracle results,
including dropped completions, late results, and retries. That integration and
any persistent wire format require human architectural review. Lean stays outside
the live application. Pre-event artifact eligibility still needs an organizer ruling.

All substantive work remains uncommitted on `feat/lean-evidence-oracle` for semantic
review. The current Obsidian entry point is
`Projects/NYCAIRR HackBU/NYCAIRR HackBU - LANTERN Formal Validation and Findings`.
