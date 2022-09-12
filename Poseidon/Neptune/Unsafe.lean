import Poseidon.Util.Zmod

namespace Unsafe

open Zmod

variable (p t : Nat)

/- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC (c a : Fin t → Zmod p) (i : Fin t) : Zmod p := (a i) + (c i)

end Unsafe