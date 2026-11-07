import Lantern.Wire

namespace Lantern
open Lean

inductive Variant where
  | baseline | unsupported | incomplete | duplicate
  deriving BEq, Repr

def variantStep (variant : Variant) (s : State) (e : Event) : Except String State :=
  match variant, e with
  | .unsupported, .cite ref =>
    if ref.run ∈ s.sealed then .error "run_sealed"
    else .ok {s with evidence := ref :: s.evidence}
  | .incomplete, .finalize run complete =>
    if run ∈ s.sealed then .error "run_sealed"
    else .ok {s with sealed := run :: s.sealed, complete := if complete then run :: s.complete else s.complete}
  | .duplicate, .commit c =>
    if hasExactCommitment s c && decide (c.run ∉ s.sealed) then
      .ok {s with commitments := c :: s.commitments}
    else step s e
  | _, _ => step s e

def alphabet (width : Nat) : Array Event := Id.run do
  let mut events := #[]
  for r in [:width] do
    for o in [:width] do
      for a in [:width] do
        for p in [:width] do
          events := events.push (.dispatch ⟨r, o, a, p⟩)
    for a in [:width] do
      for art in [:width] do
        events := events.push (.succeed r a art)
        events := events.push (.cite ⟨r, a, art⟩)
      events := events.push (.fail r a)
      events := events.push (.timeout r a)
    for o in [:width] do
      for p in [:width] do
        events := events.push (.commit ⟨r, o, p⟩)
    events := events.push (.finalize r false)
    events := events.push (.finalize r true)
  return events

-- Breadth first, exact-state deduplication. All actions have unit trace length.
-- States at the depth bound are retained but not expanded. No symmetry reduction.
def explore (variant : Variant) (width maxDepth cap : Nat) : Json := Id.run do
  let actions := alphabet width
  let mut seen := ({} : Std.HashSet String).insert (reprStr ({} : State))
  let mut queue : Array (State × List Event) := #[( {}, [])]
  let mut cursor := 0
  let mut expanded := 0
  let mut edges := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut depths := Array.replicate (maxDepth + 1) 0
  depths := depths.set! 0 1
  let mut violation : Option (List Event) := none
  let mut violationState : Option State := none
  let mut truncated := false
  let mut expandedDepth := 0
  while cursor < queue.size && !truncated && violation.isNone do
    let (s, revTrace) := queue[cursor]!
    cursor := cursor + 1
    if revTrace.length >= maxDepth then continue
    expanded := expanded + 1
    expandedDepth := max expandedDepth revTrace.length
    for event in actions do
      edges := edges + 1
      match variantStep variant s event with
      | .error _ => rejected := rejected + 1
      | .ok t =>
        accepted := accepted + 1
        let trace := event :: revTrace
        if !checkState t then
          violation := some trace.reverse
          violationState := some t
          break
        let key := reprStr t
        unless seen.contains key do
          if seen.size >= cap then
            truncated := true
            break
          seen := seen.insert key
          queue := queue.push (t, trace)
          depths := depths.set! trace.length (depths[trace.length]! + 1)
  return Json.mkObj [
    ("variant", toJson (reprStr variant)), ("width", toJson width),
    ("alphabetSize", toJson actions.size), ("depthBound", toJson maxDepth),
    ("stateCap", toJson cap), ("states", toJson seen.size),
    ("statesByDepth", toJson depths), ("poppedStates", toJson cursor),
    ("expandedStates", toJson expanded),
    ("deepestExpandedDepth", toJson expandedDepth),
    ("edges", toJson edges), ("acceptedEdges", toJson accepted),
    ("rejectedEdges", toJson rejected), ("truncated", toJson truncated),
    ("violation", match violation with
      | none => .null
      | some trace => toJson (trace.map eventJson)),
    ("violationState", match violationState with
      | none => .null
      | some s => stateJson s),
    ("searchExhausted", toJson (!truncated && violation.isNone && cursor == queue.size))]

end Lantern
