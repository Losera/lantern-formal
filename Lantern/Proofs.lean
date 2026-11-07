import Lantern.Model

namespace Lantern

theorem initial_wellFormed : WellFormed {} := by
  simp [WellFormed, Supported, CompleteSealed, HonestCoverage, UniqueCommitments,
    NoDuplicateKeys]

theorem supports_iff (s : State) (e : Evidence) :
    supports s e = true ↔ ∃ o ∈ s.outcomes,
      o.run = e.run ∧ o.attempt = e.attempt ∧ o.result = .success e.artifact := by
  simp [supports, List.any_eq_true]

theorem covered_iff (s : State) (run : Nat) :
    covered s run = true ↔ ∀ r ∈ s.requests, r.run = run →
      ∃ o ∈ s.outcomes, o.run = r.run ∧ o.attempt = r.attempt := by
  simp [covered, hasOutcome, List.all_eq_true, List.any_eq_true]
  grind

theorem step_preserves_wellFormed (s t : State) (e : Event)
    (valid : WellFormed s) (accepted : step s e = .ok t) : WellFormed t := by
  rcases valid with ⟨hs, hcs, hc, hu, hn⟩
  cases e <;> simp only [step] at accepted
  all_goals repeat' (split at accepted)
  all_goals simp_all only [Except.ok.injEq, reduceCtorEq]
  all_goals
    subst t
    simp_all [WellFormed, Supported, CompleteSealed, HonestCoverage,
      UniqueCommitments, NoDuplicateKeys, supports, covered, hasOutcome, hasCommitment,
      hasExactCommitment, List.any_eq_true]
  all_goals grind

theorem replayFrom_preserves_wellFormed (events : List Event) (s t : State)
    (valid : WellFormed s) (accepted : replayFrom s events = .ok t) : WellFormed t := by
  induction events generalizing s with
  | nil =>
    simp only [replayFrom, Except.ok.injEq] at accepted
    subst t
    exact valid
  | cons e es ih =>
    simp only [replayFrom] at accepted
    cases h : step s e with
    | error err => simp [h] at accepted
    | ok next =>
      simp [h] at accepted
      exact ih next (step_preserves_wellFormed s next e valid h) accepted

theorem replay_sound (events : List Event) (s : State)
    (accepted : replay events = .ok s) : WellFormed s :=
  replayFrom_preserves_wellFormed events {} s initial_wellFormed accepted

theorem observed_references_supported (events : List Event) (s : State)
    (accepted : replay events = .ok s) : Supported s :=
  (replay_sound events s accepted).1

theorem complete_receipts_have_outcomes (events : List Event) (s : State)
    (accepted : replay events = .ok s) : HonestCoverage s :=
  (replay_sound events s accepted).2.2.1

theorem commitments_unique (events : List Event) (s : State)
    (accepted : replay events = .ok s) : UniqueCommitments s :=
  (replay_sound events s accepted).2.2.2.1

theorem commitment_keys_nodup (events : List Event) (s : State)
    (accepted : replay events = .ok s) : NoDuplicateKeys s :=
  (replay_sound events s accepted).2.2.2.2

theorem duplicate_commit_idempotent (s : State) (c : Commitment)
    (present : c ∈ s.commitments) : step s (.commit c) = .ok s := by
  have key : hasCommitment s c = true := by
    simp only [hasCommitment, List.any_eq_true]
    exact ⟨c, present, by simp⟩
  have exactMatch : hasExactCommitment s c = true := by
    simp only [hasExactCommitment, List.any_eq_true]
    exact ⟨c, present, by simp⟩
  simp [step, key, exactMatch]

theorem conflicting_commit_rejected (s : State) (c old : Commitment)
    (valid : UniqueCommitments s) (present : old ∈ s.commitments)
    (sameRun : old.run = c.run) (sameOperation : old.operation = c.operation)
    (differentPayload : old.payload ≠ c.payload) :
    step s (.commit c) = .error "commit_payload_conflict" := by
  have key : hasCommitment s c = true := by
    simp only [hasCommitment, List.any_eq_true]
    exact ⟨old, present, by simp [sameRun, sameOperation]⟩
  have notExact : hasExactCommitment s c = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [hasExactCommitment, List.any_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨a, ha, heq⟩
    subst a
    have := valid old present c ha sameRun sameOperation
    exact differentPayload (congrArg Commitment.payload this)
  simp [step, key, notExact]

theorem receipt_validation_sound (s : State) (run : Nat) (refs : List Evidence)
    (claimsComplete : Bool) (h : validateReceipt s run refs claimsComplete = true) :
    (∀ e ∈ refs, e.run = run ∧ ∃ o ∈ s.outcomes,
      o.run = e.run ∧ o.attempt = e.attempt ∧ o.result = .success e.artifact) ∧
    (claimsComplete = true → ∀ r ∈ s.requests, r.run = run →
      ∃ o ∈ s.outcomes, o.run = r.run ∧ o.attempt = r.attempt) := by
  simp only [validateReceipt, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  constructor
  · intro e he
    have := h.1 e he
    exact ⟨of_decide_eq_true this.1, (supports_iff s e).mp this.2⟩
  · intro complete
    have cov : covered s run = true := by grind
    exact (covered_iff s run).mp cov

theorem timeout_does_not_create_outcome (s t : State) (run attempt : Nat)
    (h : step s (.timeout run attempt) = .ok t) : t.outcomes = s.outcomes := by
  simp only [step] at h
  repeat' (split at h)
  all_goals simp_all
  all_goals subst t; rfl

end Lantern
