import Poseidon.Util.Zmod
import Poseidon.Util.Util

namespace Unsafe

open Zmod Util.Matrix

variable (p t : Nat)

/- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC (c a : Array (Zmod p)) (i : Fin (c.size)) {eq : c.size = a.size} : Zmod p := 
  (Array.zipWith c a (. + .))[i]

/- An `R_f`-round, that is, a full round. -/
def R_f_round (S_box' : Zmod p → Zmod p) (c a : Array (Zmod p))
    (MDS : Matrix (Zmod p)) {eq : c.size = a.size} : Fin (c.size) → Zmod p := c

/- An `R_p`-round, that is, a partial round. -/
def R_p_round (S_box' : Zmod p → Zmod p) (c a : Array (Zmod p))
    (MDS : Matrix (Zmod p)) {eq : c.size = a.size}  : Fin (c.size) → Zmod p := c

/- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (S_box' : Zmod p → Zmod p) (c a : Array (Zmod p)) 
    (MDS : Matrix (Zmod p)) {eq : c.size = a.size}  : Fin (c.size) → Zmod p := S_box'

end Unsafe