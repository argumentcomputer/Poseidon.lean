import YatimaStdLib.Matrix
import YatimaStdLib.Zmod

/-!
# Generates the Poseidon MDS Matrix

TODO : Add documentation
-/

def generatePoseidonMDS (p t : Nat) : Matrix (Zmod p) := Id.run do
  let mut answer : Matrix (Zmod p) := #[]
  for c in [0 : t] do
    answer := answer.push #[]
    for r in [t : 2*t] do
      answer := answer.set! (answer.size - 1) (answer[answer.size - 1]!.push <| Zmod.modInv (r + c))
  return answer
