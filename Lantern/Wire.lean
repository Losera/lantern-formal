import Lantern
import Lean

namespace Lantern
open Lean

def natField (j : Json) (key : String) : Except String Nat := do
  (← j.getObjVal? key).getNat?

-- Unknown fields are rejected so a misspelled safety-relevant field cannot be ignored.
def exactFields (j : Json) (names : List String) : Except String Unit := do
  let obj ← j.getObj?
  for (key, _) in obj.toList do
    unless key ∈ names do throw s!"unknown field: {key}"
  for key in names do
    let _ ← j.getObjVal? key

def parseEvent (j : Json) : Except String Event := do
  let kind ← (← j.getObjVal? "kind").getStr?
  match kind with
  | "dispatch" =>
    exactFields j ["kind", "run", "operation", "attempt", "payload"]
    return .dispatch ⟨← natField j "run", ← natField j "operation",
      ← natField j "attempt", ← natField j "payload"⟩
  | "succeed" =>
    exactFields j ["kind", "run", "attempt", "artifact"]
    return .succeed (← natField j "run") (← natField j "attempt") (← natField j "artifact")
  | "fail" | "timeout" =>
    exactFields j ["kind", "run", "attempt"]
    let run ← natField j "run"
    let attempt ← natField j "attempt"
    return if kind == "fail" then .fail run attempt else .timeout run attempt
  | "cite" =>
    exactFields j ["kind", "run", "attempt", "artifact"]
    return .cite ⟨← natField j "run", ← natField j "attempt", ← natField j "artifact"⟩
  | "commit" =>
    exactFields j ["kind", "run", "operation", "payload"]
    return .commit ⟨← natField j "run", ← natField j "operation", ← natField j "payload"⟩
  | "finalize" =>
    exactFields j ["kind", "run", "complete"]
    return .finalize (← natField j "run") (← (← j.getObjVal? "complete").getBool?)
  | _ => throw s!"unknown event: {kind}"

def requestJson (r : Request) : Json := Json.mkObj [
  ("run", toJson r.run), ("operation", toJson r.operation),
  ("attempt", toJson r.attempt), ("payload", toJson r.payload)]

def evidenceJson (e : Evidence) : Json := Json.mkObj [
  ("run", toJson e.run), ("attempt", toJson e.attempt), ("artifact", toJson e.artifact)]

def commitmentJson (c : Commitment) : Json := Json.mkObj [
  ("run", toJson c.run), ("operation", toJson c.operation), ("payload", toJson c.payload)]

def eventJson : Event → Json
  | .dispatch r => Json.mkObj (("kind", toJson "dispatch") ::
      [("run", toJson r.run), ("operation", toJson r.operation),
       ("attempt", toJson r.attempt), ("payload", toJson r.payload)])
  | .succeed r a art => Json.mkObj [("kind", toJson "succeed"), ("run", toJson r),
      ("attempt", toJson a), ("artifact", toJson art)]
  | .fail r a => Json.mkObj [("kind", toJson "fail"), ("run", toJson r), ("attempt", toJson a)]
  | .timeout r a => Json.mkObj [("kind", toJson "timeout"), ("run", toJson r), ("attempt", toJson a)]
  | .cite e => Json.mkObj [("kind", toJson "cite"), ("run", toJson e.run),
      ("attempt", toJson e.attempt), ("artifact", toJson e.artifact)]
  | .commit c => Json.mkObj [("kind", toJson "commit"), ("run", toJson c.run),
      ("operation", toJson c.operation), ("payload", toJson c.payload)]
  | .finalize r c => Json.mkObj [("kind", toJson "finalize"), ("run", toJson r), ("complete", toJson c)]

def outcomeJson (o : Outcome) : Json := Json.mkObj [
  ("run", toJson o.run), ("attempt", toJson o.attempt),
  ("result", match o.result with
    | .success art => Json.mkObj [("status", toJson "success"), ("artifact", toJson art)]
    | .failure => Json.mkObj [("status", toJson "failure")])]

def stateJson (s : State) : Json := Json.mkObj [
  ("requests", toJson (s.requests.reverse.map requestJson)),
  ("outcomes", toJson (s.outcomes.reverse.map outcomeJson)),
  ("timeouts", toJson (s.timeouts.reverse.map fun (r, a) =>
    Json.mkObj [("run", toJson r), ("attempt", toJson a)])),
  ("evidence", toJson (s.evidence.reverse.map evidenceJson)),
  ("commitments", toJson (s.commitments.reverse.map commitmentJson)),
  ("sealed", toJson s.sealed.reverse), ("complete", toJson s.complete.reverse),
  ("coverage", toJson ((s.requests.map (·.run) ++ s.sealed).eraseDups.map fun run =>
    Json.mkObj [("run", toJson run), ("covered", toJson (covered s run)),
      ("pending", toJson ((s.requests.reverse.filter fun r =>
        r.run == run && !hasOutcome s r.run r.attempt).map (·.attempt)))]))]

def malformed (detail : String) (index : Json := .null) : Json := Json.mkObj [
  ("accepted", toJson false), ("category", toJson "malformed_input"),
  ("detail", toJson detail), ("index", index)]

-- Deliberately sequential: the first failing event is the stable error boundary.
def runWire (input : Json) : Json := Id.run do
  let events ← match (do exactFields input ["events"]; (← input.getObjVal? "events").getArr?) with
    | .error err => return malformed err
    | .ok events => pure events
  let mut s : State := {}
  for i in [:events.size] do
    let event ← match parseEvent events[i]! with
      | .error err => return malformed err (toJson i)
      | .ok e => pure e
    match step s event with
    | .error err => return Json.mkObj [("accepted", toJson false),
        ("category", toJson err), ("index", toJson i)]
    | .ok next => s := next
  return Json.mkObj [("accepted", toJson true), ("state", stateJson s)]

instance (s : State) : Decidable (WellFormed s) := by
  unfold WellFormed Supported CompleteSealed HonestCoverage UniqueCommitments NoDuplicateKeys
  infer_instance

def checkState (s : State) : Bool := decide (WellFormed s)

-- The executable checker decides the exact proved predicate, not a proxy metric.
theorem checkState_iff (s : State) : checkState s = true ↔ WellFormed s := by
  simp [checkState]

end Lantern
