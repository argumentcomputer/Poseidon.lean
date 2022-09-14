import Poseidon.Util.Zmod
import Poseidon.Util.Matrix
import Poseidon.Util.Util

namespace Unsafe

open Zmod Matrix Util

variable (p t : Nat)

/- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC (c a : Vector (Zmod p) t) : Vector (Zmod p) t := c + a

/- An `R_f`-round, that is, a full round. -/
def R_f_round (S_box' : Zmod p → Zmod p) (c : Vector (Zmod p) t)
    (MDS : Matrix (Zmod p) t t) (a : Vector (Zmod p) t) : Vector (Zmod p) t :=
    matrixVecAction MDS $ fun i => S_box' (ARC p t c a i)

/- An `R_p`-round, that is, a partial round. -/
def R_p_round (S_box' : Zmod p → Zmod p) (c : Vector (Zmod p) t)
    (MDS : Matrix (Zmod p) t t) (a : Vector (Zmod p) t) : Vector (Zmod p) t :=
    matrixVecAction MDS
      (λ i => dite ((i : Nat) = 0) (λ _ => S_box' (ARC p t c a i)) (λ _ => ARC p t c a i))

def iterate {A : Sort u} (n : Nat) (f : A → A) : A → A :=
  match n with
    | 0 => id
    | (k + 1) => f ∘ (iterate k f)

/- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (R_f R_p : Nat) (S_box' : Zmod p → Zmod p) (c a : Vector (Zmod p) t) 
    (MDS : Matrix (Zmod p) t t) : Vector (Zmod p) t :=
    (iterate R_f (R_f_round p t S_box' c MDS)) ((iterate R_p (R_p_round p t S_box' c MDS'))
      ((iterate R_f $ R_f_round p t S_box' c MDS) a))

end Unsafe