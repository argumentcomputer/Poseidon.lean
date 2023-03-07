import Poseidon.HashImpl
import Poseidon.Parameters.Lurk
import Poseidon.Parameters.Lurk3

/-!
# Parameters for Lurk Profile

This module contains the definitions necessary to use the exact profile,
context, and input formatting to mirror the Poseidon hashing used in Lurk.
-/

namespace Poseidon.Lurk

open Poseidon 

abbrev F := Zmod Lurk.Profile.p

def Context3 : Hash.Context Lurk3.Profile := 
  ⟨Lurk3.MDS, Lurk3.roundConstants⟩

/-- The pre-computed hashing context used by Lurk. -/
def Context4 : Hash.Context Profile :=
  ⟨Lurk.MDS, Lurk.roundConstants⟩

def hash3 (f₁ f₂ f₃ : F) : F :=
  Poseidon.hash Lurk3.Profile Context3 #[f₁, f₂, f₃] .merkleTree
/--
The hashing function used by Lurk that uses pre-initialized Lurk parameters and
constants.
-/
def hash4 (f₁ f₂ f₃ f₄ : F) : F :=
  Poseidon.hash Lurk.Profile Context4 #[f₁, f₂, f₃, f₄] .merkleTree
