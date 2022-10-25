import Poseidon.HashImpl
import Poseidon.Parameters.Lurk

/-!
# Parameters for Lurk Profile

This module contains the definitions necessary to use the exact profile, context, and input formatting
to mirror the Poseidon hashing used in Lurk.
-/

open Poseidon

abbrev F' := Zmod Lurk.Profile.p

/--
The pre-computed hashing context used by Lurk.
-/
def Lurk.Context : Hash.Context Lurk.Profile := ⟨Lurk.MDS, Lurk.roundConstants⟩

/--
The hashing function used by Lurk that uses pre-initialized Lurk parameters and constants.
-/
def Lurk.hash : F' → F' → F' → F' → F'
  | f₁, f₂, f₃, f₄ => Poseidon.hash Lurk.Profile Lurk.Context #[f₁, f₂, f₃, f₄] .merkleTree