import Std

namespace Lantern

/- A single trusted coordinator linearizes observations. Natural-number identifiers
are scoped explicitly; payload is an opaque identity, not a claim about price or
truth. Timeouts are observations of uncertainty, never fabricated outcomes. -/

structure Request where
  run : Nat
  operation : Nat
  attempt : Nat
  payload : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Result where
  | success (artifact : Nat)
  | failure
  deriving DecidableEq, Repr, Inhabited

structure Outcome where
  run : Nat
  attempt : Nat
  result : Result
  deriving DecidableEq, Repr, Inhabited

structure Evidence where
  run : Nat
  attempt : Nat
  artifact : Nat
  deriving DecidableEq, Repr, Inhabited

structure Commitment where
  run : Nat
  operation : Nat
  payload : Nat
  deriving DecidableEq, Repr, Inhabited

structure State where
  requests : List Request := []
  outcomes : List Outcome := []
  timeouts : List (Nat × Nat) := []
  evidence : List Evidence := []
  commitments : List Commitment := []
  sealed : List Nat := []
  complete : List Nat := []
  deriving DecidableEq, Repr, Inhabited

inductive Event where
  | dispatch (request : Request)
  | succeed (run attempt artifact : Nat)
  | fail (run attempt : Nat)
  | timeout (run attempt : Nat)
  | cite (evidence : Evidence)
  | commit (commitment : Commitment)
  | finalize (run : Nat) (complete : Bool)
  deriving DecidableEq, Repr, Inhabited

def hasRequest (s : State) (run attempt : Nat) : Bool :=
  s.requests.any fun r => decide (r.run = run ∧ r.attempt = attempt)

def hasOutcome (s : State) (run attempt : Nat) : Bool :=
  s.outcomes.any fun o => decide (o.run = run ∧ o.attempt = attempt)

def supports (s : State) (e : Evidence) : Bool :=
  s.outcomes.any fun o =>
    decide (o.run = e.run ∧ o.attempt = e.attempt ∧ o.result = .success e.artifact)

def covered (s : State) (run : Nat) : Bool :=
  s.requests.all fun r => r.run != run || hasOutcome s r.run r.attempt

def hasCommitment (s : State) (c : Commitment) : Bool :=
  s.commitments.any fun old => decide (old.run = c.run ∧ old.operation = c.operation)

def hasExactCommitment (s : State) (c : Commitment) : Bool :=
  s.commitments.any fun old => decide (old = c)

def canCommit (s : State) (c : Commitment) : Bool :=
  s.requests.any fun r =>
    decide (r.run = c.run ∧ r.operation = c.operation ∧ r.payload = c.payload) &&
    s.outcomes.any fun o =>
      decide (o.run = r.run ∧ o.attempt = r.attempt) &&
      match o.result with | .success _ => true | .failure => false

def step (s : State) (event : Event) : Except String State :=
  match event with
  | .dispatch r =>
    if r.run ∈ s.sealed then .error "run_sealed"
    else if hasRequest s r.run r.attempt then .error "attempt_exists"
    else if s.requests.any (fun old => decide
        (old.run = r.run ∧ old.operation = r.operation ∧ old.payload ≠ r.payload)) then
      .error "operation_payload_conflict"
    else .ok { s with requests := r :: s.requests }
  | .succeed run attempt artifact =>
    if run ∈ s.sealed then .error "run_sealed"
    else if !hasRequest s run attempt then .error "request_missing"
    else if hasOutcome s run attempt then .error "outcome_exists"
    else .ok { s with outcomes := ⟨run, attempt, .success artifact⟩ :: s.outcomes }
  | .fail run attempt =>
    if run ∈ s.sealed then .error "run_sealed"
    else if !hasRequest s run attempt then .error "request_missing"
    else if hasOutcome s run attempt then .error "outcome_exists"
    else .ok { s with outcomes := ⟨run, attempt, .failure⟩ :: s.outcomes }
  | .timeout run attempt =>
    if run ∈ s.sealed then .error "run_sealed"
    else if !hasRequest s run attempt then .error "request_missing"
    else if hasOutcome s run attempt then .error "outcome_exists"
    else if (run, attempt) ∈ s.timeouts then .ok s
    else .ok { s with timeouts := (run, attempt) :: s.timeouts }
  | .cite e =>
    if e.run ∈ s.sealed then .error "run_sealed"
    else if !supports s e then .error "unsupported_evidence"
    else .ok { s with evidence := e :: s.evidence }
  | .commit c =>
    -- Cached duplicate replies remain legal after sealing, but cannot mutate state.
    if hasCommitment s c then
      if hasExactCommitment s c then .ok s
      else .error "commit_payload_conflict"
    else if c.run ∈ s.sealed then .error "run_sealed"
    else if !canCommit s c then .error "commit_unconfirmed"
    else .ok { s with commitments := c :: s.commitments }
  | .finalize run complete =>
    if run ∈ s.sealed then .error "run_sealed"
    else if complete && !covered s run then .error "incomplete_coverage"
    else .ok { s with sealed := run :: s.sealed,
                      complete := if complete then run :: s.complete else s.complete }

def replayFrom (s : State) : List Event → Except String State
  | [] => .ok s
  | event :: events => match step s event with
    | .error err => .error err
    | .ok next => replayFrom next events

def replay (events : List Event) : Except String State := replayFrom {} events

/- These predicates describe independently meaningful state properties. They are
not used as an omnibus guard by step. The proof must inspect each transition. -/
def Supported (s : State) : Prop :=
  ∀ e ∈ s.evidence, ∃ o ∈ s.outcomes,
    o.run = e.run ∧ o.attempt = e.attempt ∧ o.result = .success e.artifact

def CompleteSealed (s : State) : Prop := ∀ run ∈ s.complete, run ∈ s.sealed

def HonestCoverage (s : State) : Prop :=
  ∀ run ∈ s.complete, ∀ r ∈ s.requests, r.run = run →
    ∃ o ∈ s.outcomes, o.run = r.run ∧ o.attempt = r.attempt

def UniqueCommitments (s : State) : Prop :=
  ∀ a ∈ s.commitments, ∀ b ∈ s.commitments,
    a.run = b.run → a.operation = b.operation → a = b

def NoDuplicateKeys (s : State) : Prop :=
  (s.commitments.map fun c => (c.run, c.operation)).Nodup

def WellFormed (s : State) : Prop :=
  Supported s ∧ CompleteSealed s ∧ HonestCoverage s ∧ UniqueCommitments s ∧
    NoDuplicateKeys s

-- A receipt request is scoped to one run. Outcome success is separate from coverage.
def validateReceipt (s : State) (run : Nat) (refs : List Evidence)
    (claimsComplete : Bool) : Bool :=
  refs.all (fun e => decide (e.run = run) && supports s e) &&
    (!claimsComplete || covered s run)

end Lantern
