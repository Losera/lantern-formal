import Lantern.Wire

namespace Lantern

-- Kernel-checked concrete witnesses for the receipt API and non-vacuity.
def goodTrace : List Event := [
  .dispatch ⟨0, 0, 0, 0⟩, .succeed 0 0 7, .cite ⟨0, 0, 7⟩,
  .commit ⟨0, 0, 0⟩, .finalize 0 true]

example : (replay goodTrace).isOk = true := by decide
example : validateReceipt
    {outcomes := [⟨0, 0, .success 7⟩]} 0 [⟨0, 0, 7⟩] false = true := by decide
example : validateReceipt
    {outcomes := [⟨0, 0, .success 7⟩]} 1 [⟨0, 0, 7⟩] false = false := by decide
example : validateReceipt
    {outcomes := [⟨0, 0, .success 7⟩]} 0 [⟨0, 0, 8⟩] false = false := by decide
example : validateReceipt
    {requests := [⟨0, 0, 0, 0⟩], timeouts := [(0, 0)]} 0 [] true = false := by decide
example : validateReceipt
    {requests := [⟨0, 0, 0, 0⟩], outcomes := [⟨0, 0, .failure⟩]} 0 [] true = true := by decide
example : validateReceipt {} 0 [] true = true := by decide

end Lantern
