import Poseidon.Profile
import YatimaStdLib.Zmod
import YatimaStdLib.Matrix

-- TODO : Add these to `YatimaStdLib.Zmod`

def Zmod.norm (x : Zmod n) : Nat :=
  if x < 0 then (x.rep - (x.rep / n - 1) * n).toNat else x.toNat

instance : Repr (Zmod n) where
  reprPrec n _ := s!"0x{Nat.toDigits 16 n.norm |>.asString}"

private def repeatM {m : Type _ → Type _} [Monad m] (f : m α) : Nat → m PUnit
  | 0 => pure ()
  | n + 1 => f *> repeatM f n

namespace Poseidon

namespace Hash

structure Context (profile : Profile) where
  mdsMatrix : Matrix (Zmod profile.prime)
  roundConst : Array (Zmod profile.prime)

structure State (profile : Profile) where
  round : Nat
  state : Vector (Zmod profile.prime)

def initialState {profile : Profile} (input : Vector (Zmod profile.prime)) : State profile := ⟨0, input⟩

end Hash

open Hash in
abbrev HashM (profile : Profile) := ReaderT (Context profile) $ StateM (State profile)

variable (profile : Profile)

namespace HashM

open Matrix in
def linearLayer : HashM profile PUnit := do 
  let mds := (← read).mdsMatrix
  modify (fun ⟨r, vec⟩ => ⟨r, action mds vec⟩)

def addConst : HashM profile PUnit := do
  let t := profile.t
  let round := (← get).round
  let const := (← read).roundConst.extract (t * round) (t * round + t)
  modify fun ⟨r, vec⟩ => ⟨r, vec + const⟩

def fullRound : HashM profile PUnit :=
  addConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.map profile.sBox⟩) *>
  linearLayer profile

def partialRound : HashM profile PUnit :=
  addConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.set! 0 (profile.sBox vec[0]!)⟩) *>
  linearLayer profile

def runRounds : HashM profile PUnit :=  
  repeatM (fullRound profile) (profile.fullRounds / 2) *>
  repeatM (partialRound profile) (profile.partialRounds) *>
  repeatM (fullRound profile) (profile.fullRounds / 2) 

open Hash in
def hash (context : Context profile) (input : Vector (Zmod profile.prime)) : State profile := 
  Prod.snd <$> StateT.run (ReaderT.run (runRounds profile) context) (initialState input) 

end HashM

open Hash

-- TODO : Add more validation by sequencing with the `ExceptM` monad
def validateInputs (context : Context profile)  (input : Vector (Zmod profile.prime)) : Bool :=
  input.size == profile.t &&
  context.roundConst.size == profile.t * (profile.fullRounds + profile.partialRounds) &&
  profile.t == context.mdsMatrix.size &&
  profile.t == context.mdsMatrix.transpose.size

def hash (context : Context profile)  (input : Vector (Zmod profile.prime)) : Vector (Zmod profile.prime) := 
  if validateInputs profile context input then (HashM.hash profile context input).state else #[]

end Poseidon
