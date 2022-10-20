import Poseidon.Profile
import YatimaStdLib.Zmod
import YatimaStdLib.Matrix
import YatimaStdLib.Monad

namespace Poseidon

namespace Hash

structure Context (profile : HashProfile) where
  mdsMatrix : Matrix (Zmod profile.p)
  roundConst : Array (Zmod profile.p)

structure State (profile : HashProfile) where
  round : Nat
  state : Vector (Zmod profile.p)

def initialState {profile : HashProfile} (input : Vector (Zmod profile.p)) : State profile := ⟨0, input⟩

end Hash

open Hash in
abbrev HashM (profile : HashProfile) := ReaderT (Context profile) $ StateM (State profile)

variable (profile : HashProfile)

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

open Monad in
def runRounds : HashM profile PUnit :=  
  repeatM (fullRound profile) (profile.fullRounds / 2) *>
  repeatM (partialRound profile) (profile.partRounds) *>
  repeatM (fullRound profile) (profile.fullRounds / 2) 

open Hash in
def hash (context : Context profile) (input : Vector (Zmod profile.p)) : State profile := 
  Prod.snd <$> StateT.run (ReaderT.run (runRounds profile) context) (initialState input) 

end HashM

open Hash

-- TODO : Add more validation by sequencing with the `ExceptM` monad
def validateInputs (context : Context profile)  (input : Vector (Zmod profile.p)) : Bool :=
  input.size == profile.t &&
  context.roundConst.size == profile.t * (profile.fullRounds + profile.partRounds) &&
  profile.t == context.mdsMatrix.size &&
  profile.t == context.mdsMatrix.transpose.size

def hashInput (context : Context profile) (input : Vector (Zmod profile.p)) : Vector (Zmod profile.p) := 
  if validateInputs profile context input then (HashM.hash profile context input).state else #[]

end Poseidon
