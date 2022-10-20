import Poseidon.Profile
import YatimaStdLib.ByteArray
import YatimaStdLib.Monad
import YatimaStdLib.Zmod

/-!
# Generates the Poseidon Round Constants

TODO : Add documentation
-/

private def fieldBits (isPrime : Bool) : UInt64 := if isPrime then 1 else 0

private def sBoxBits : Int → UInt64
  | -1 => 2
  |  3 => 0
  |  5 => 1
  |  _ => 3

private def fieldSizeBits (prime : Nat) : UInt64 := prime.log2 + 1 |>.toUInt64

private def padOne (u : UInt64) : Nat → UInt64
  | 0     => u
  | n + 1 => (u <<< 1) + 1 |> (padOne · n)

private def grainStateInit (isPrime : Bool) (a : Int) (prime : Nat) (t fullRound partialRound : UInt64) := 
  (fieldBits isPrime) |> (· <<< (4 : UInt64))
                      |> (· + sBoxBits a)
                      |> (· <<< (12 : UInt64))
                      |> (· + fieldSizeBits prime)
                      |> (· <<< (12 : UInt64))
                      |> (· + t)
                      |> (· <<< (10 : UInt64))
                      |> (· + fullRound)
                      |> (· <<< (10 : UInt64))
                      |> (· + partialRound)
                      |> (padOne · 14)
                      |>.toByteArray
                      |>.push 0xff
                      |>.push 0xff

structure RCState (p : Nat) where
  bitRound : Array Bit
  state  : ByteArray
  rndCon : Array (Zmod p)

def init (prof : Poseidon.HashProfile) : RCState prof.p where
  bitRound := #[]
  state := grainStateInit true prof.a 
                               prof.p
                               prof.t.toUInt64 
                               prof.fullRounds.toUInt64 
                               prof.partRounds.toUInt64
  rndCon := #[]

abbrev RoundConstantM (profile : Poseidon.HashProfile) := StateM (RCState profile.p)

def notEnoughConst : RoundConstantM prof Bool := 
  get >>= fun s => pure $ s.rndCon.size < (prof.fullRounds + prof.partRounds)*prof.t

def notEnoughBits : RoundConstantM prof Bool :=
  get >>= fun s => pure $ s.bitRound.size < prof.p.log2 + 1

def extractBit : RoundConstantM prof Bit := do
  let stt := (← get).state
  let bits := #[stt.getBit 62, stt.getBit 51, stt.getBit 38, 
                stt.getBit 23, stt.getBit 13, stt.getBit 0]
  return Bit.arrayXOr bits

def generateBitArray : RoundConstantM prof Unit := do
  modify fun ⟨_, s, rC⟩ => ⟨#[], s, rC⟩
  Monad.repeatWhile notEnoughBits do
    let b₁ ← extractBit
    modify (fun ⟨br, s, rc⟩ => ⟨br, s.shiftAdd b₁, rc⟩)
    let b₂ ← extractBit
    modify (fun ⟨br, s, rc⟩ => ⟨br, s.shiftAdd b₂, rc⟩)
    if b₁ == .one then
      modify fun ⟨bR, s, rC⟩ => ⟨bR.push b₂, s, rC⟩
    else
      pure ()

def generate (prof : Poseidon.HashProfile) : RoundConstantM prof Unit := do 
  for _ in [:160] do
    let b ← extractBit
    modify (fun ⟨br, s, rc⟩ => ⟨br, s.shiftAdd b, rc⟩)
  Monad.repeatWhile notEnoughConst do
    generateBitArray
    let c := Bit.arrayToNat (← get).bitRound
    if c < prof.p then 
      modify fun ⟨bR, s, rC⟩ => ⟨bR, s, rC.push c⟩
    else
      return ()
  return ()

def RoundConstantM.run (profile : Poseidon.HashProfile) : Array (Zmod profile.p) :=
   Id.run <| Prod.snd <$> generate profile (init profile) |>.rndCon
