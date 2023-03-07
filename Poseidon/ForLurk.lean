import Poseidon.HashImpl
import Poseidon.Parameters.Lurk4
import Poseidon.Parameters.Lurk3

/-!
# Parameters for Lurk Profile

This module contains the definitions necessary to use the exact profile,
context, and input formatting to mirror the Poseidon hashing used in Lurk.
-/

namespace Poseidon.Lurk

open Poseidon 

/-- The pre-computed hashing context used by Lurk for commitments-/
def Context3 : Hash.Context Lurk3.Profile := 
  ⟨Lurk3.MDS, Lurk3.roundConstants⟩

/-- The pre-computed hashing context used by Lurk. -/
def Context4 : Hash.Context Lurk4.Profile :=
  ⟨Lurk4.MDS, Lurk4.roundConstants⟩

/--
The hashing function used by Lurk for commitments that uses pre-initialized Lurk parameters and
constants
-/
def hash3 (f₁ f₂ f₃ : Zmod p) : Zmod p :=
  Poseidon.hash Lurk3.Profile Context3 #[f₁, f₂, f₃] .merkleTree

/--
The hashing function used by Lurk that uses pre-initialized Lurk parameters and
constants.
-/
def hash4 (f₁ f₂ f₃ f₄ : Zmod p) : Zmod p :=
  Poseidon.hash Lurk4.Profile Context4 #[f₁, f₂, f₃, f₄] .merkleTree
