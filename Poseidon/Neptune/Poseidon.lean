import Poseidon.Util.Zmod
import Poseidon.Util.Matrix
import Poseidon.Util.Util

import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Lemmas

namespace Unsafe

open Zmod Matrix Util Nat

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

/- Adding an `r`-chunk to the state. -/
def add_to_state (r : Nat) (m : Vector (Zmod p) r) 
  (a : Vector (Zmod p) t) : Vector (Zmod p) t :=
  λ i => dite ((i : Nat) < r) (λ h => a i + m (castLt i h)) (λ _ => a i)

def r_elements_of_zmodp (r d cap : Nat) 
                        (a : Vector (Zmod p) ((d + 1) * r + (r + cap)))
                        (hr : 1 ≤ r) : Vector (Zmod p) r := 
  (λ (j : Fin r) => 
    a ⟨(d + 1) + j, 
        add_lt_add_of_le_of_lt ((le_mul_iff_one_le_right (Nat.succ_pos _)).2 hr)
          (lt_add_of_lt_of_nonneg j.2 (Nat.zero_le _))⟩) 

def helper_step (d r : Nat)
                (a : Vector (Zmod p) ((d + 1) * r + (r + cap))) 
                (j : Fin (d * r + (r + cap))) : ¬j.1 < (d + 1) * r → Zmod p := 
  λ _ => a ⟨(j : Nat) + r, helper d r cap j⟩

def simplifications (d r cap : Nat) (a : Vector (Zmod p) ((d + 1) * r + (r + cap))) 
                    (hr : 1 ≤ r) (j : Fin (d * r + (r + cap))) : j.val < (Nat.succ d) * r → Zmod p :=
  λ h => 
    a (castLt j (lt_trans h
              ((lt_add_iff_pos_right _).2 (add_pos_of_pos_of_nonneg (Nat.pos_of_ne_zero
                (one_le_iff_ne_zero.1 hr)) (Nat.zero_le _)))))

def compose_MDS (R_f R_p r cap : Nat) (hr : 1 ≤ r) 
                (S_box : Zmod p → Zmod p) (c : Vector (Zmod p) (r + cap)) 
                (MDS : Matrix (Zmod p) (r + cap) (r + cap)) (k : Nat) 
                (a : Vector (Zmod p) (k * r + (r + cap))) : Vector (Zmod p) (r + cap) :=
/-
TODO: we have the following error
code generator does not support recursor 'Nat.rec' yet, 
consider using 'match ... with' and/or structural recursion
-/   
  match k with
    | 0 => by
      rw [Nat.zero_mul] at a 
      rw [Nat.zero_add] at a;
      refine λ i => P_perm p (r + cap) R_p R_f S_box c a MDS i
    | (d + 1) => by
        let rec_call := compose_MDS R_f R_p r cap hr S_box c MDS d 
        refine (λ i => P_perm p (r + cap) R_p R_f S_box c
                         (add_to_state p (r + cap) r (r_elements_of_zmodp p r d cap a hr) 
                            (rec_call (λ j => dite ((j : ℕ) < (.succ d) * r) 
                                          (simplifications p d r cap a hr j) 
                                          (helper_step p d r a j)
                                          )))
                             MDS 
                             i)

/- The Poseidon hash function, takes `N` bits and returns `o` `𝔽_p`-elements. -/
def P_hash (R_f R_p r o cap : Nat) (hr : 1 ≤ r) (S_box : Zmod p → Zmod p) 
  (c : Vector (Zmod p) (r + cap))
  (MDS : Matrix (Zmod p) (r + cap) (r + cap)) (ho : o < r + cap)
  (k : Nat) (a : Vector (Zmod p) (k * r + (r + cap))) : Vector (Zmod p) o :=
  @Function.comp (Fin o) (Fin (r + cap)) (Zmod p)
    (compose_MDS p R_f R_p r cap hr S_box c MDS k a)
    (fin_coercion ho)
end Unsafe