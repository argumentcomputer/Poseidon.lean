import Poseidon.Profile
import YatimaStdLib.Zmod

/-!
# Generates the Poseidon Round Constants

TODO : Add documentation
-/

def UInt8.showBits (u : UInt8) : String := 
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

private def ByteArray.toString (bs : ByteArray) : String := Id.run do
  if bs.isEmpty then "b[]" else
  let mut ans := "b["
  for u in bs do
    ans := ans ++ u.showBits ++ ","
  return ans.dropRight 1 ++ "]"

instance : Repr ByteArray where
  reprPrec bs _ := bs.toString

private def fieldBits (isPrime : Bool) : UInt64 := if isPrime then 1 else 0

private def sBoxBits : Int → UInt64
  | -1 => 2
  |  3 => 0
  |  5 => 1
  |  _ => 3

-- def p := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

private def fieldSizeBits (prime : Nat) : UInt64 := prime.log2 + 1 |>.toUInt64

private def padOne (u : UInt64) : Nat → UInt64
  | 0     => u
  | n + 1 => (u <<< 1) + 1 |> (padOne · n)

-- TODO : Figure out if choosing to reverse is a bad idea

private partial def UInt64.toByteArray (u : UInt64) : ByteArray := 
  let rec loop (u : UInt64) (acc : Array UInt8) :=
    if u == 0 then acc else loop (u >>> 8) <| acc.push (u &&& (0xff : UInt64)).toUInt8
  loop u #[] |>.reverse 
             |> ByteArray.mk

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

inductive Bit where
  | one
  | zero
deriving BEq

instance : ToString Bit where
  toString 
    | .one  => "1"
    | .zero => "0" 
open Bit

def Bit.xOr : Bit → Bit → Bit
  | one, zero
  | zero, one => one
  | _, _      => zero

def Bit.toNat : Bit → Nat
  | zero => 0
  | one  => 1

def Bit.toUInt8 : Bit → UInt8 := Nat.toUInt8 ∘ Bit.toNat 

private def bArXOr (bs : Array Bit) : Bit := bs.foldl (fun b b' => b.xOr b') zero

def bArToNat (bs : Array Bit) : Nat := bs.foldl (fun b b' => b*2 + b'.toNat) 0

private def ByteArray.getD (bs : ByteArray) (idx : Int) : UInt8 :=
  if idx < 0 || bs.size ≤ idx then 0 else bs[idx.toNat]!

private def ByteArray.getBit (bs : ByteArray) (n : Nat) : Bit := 
  let (idx, rem) := (n / 8, 2^(n % 8) |>.toUInt8)
  if bs[bs.size - 1 - idx]! &&& rem == 0 then zero else one

-- Shifts the byte array left by 1, preserves length (so in particular kills the first coefficient
private def ByteArray.shiftLeft (bs : ByteArray) : ByteArray := Id.run do
  let mut answer : ByteArray := .mkEmpty bs.size
  for idx in [:bs.size] do
    answer := answer.push <| (bs[idx]! <<< 1) + (bs.getD (idx + 1) >>> 7)
  answer

private def ByteArray.shiftAdd (bs : ByteArray) (b : Bit) : ByteArray :=
  let ans := bs.shiftLeft
  ans.set! (ans.size - 1) (ans[(ans.size - 1)]! + b.toUInt8)

#eval ByteArray.shiftAdd (.mk #[0xef, 0xab]) one

structure RCState (p : Nat) where
  bitRound : Array Bit
  state  : ByteArray
  rndCon : Array (Zmod p)

def init (prof : Poseidon.Profile) : RCState prof.prime where
  bitRound := #[]
  state := grainStateInit true 5 prof.prime 
                                 prof.t.toUInt64 
                                 prof.fullRounds.toUInt64 
                                 prof.partialRounds.toUInt64
  rndCon := #[]

abbrev RoundConstantM (profile : Poseidon.Profile) := StateM (RCState profile.prime)

private def repeatWhile {m : Type _ → Type _} [Monad m] (f : m PUnit) (test : m Bool) : m PUnit := 
  test >>= fun b => if b then pure () else f

def enoughConst : RoundConstantM prof Bool := 
  get >>= fun s => pure $ s.rndCon.size ≥ (prof.fullRounds + prof.partialRounds)*prof.t

def enoughBits : RoundConstantM prof Bool :=
  get >>= fun s => pure $ s.bitRound.size ≥ 255

def generateBit : RoundConstantM prof Bit := do
  let stt := (← get).state
  let bits := #[stt.getBit 0, stt.getBit 13, stt.getBit 23, 
                stt.getBit 38, stt.getBit 51, stt.getBit 62]
  return bArXOr bits

def addToBitArray : RoundConstantM prof Unit := sorry

def generate (prof : Poseidon.Profile) : RoundConstantM prof Unit := do
  for _ in [:160] do
    let b ← generateBit
    modify (fun ⟨br, s, rc⟩ => ⟨br, s.shiftAdd b, rc⟩)
  return ()

def RoundConstantM.run (profile : Poseidon.Profile) : Array (Zmod profile.prime) :=
   Id.run <| Prod.snd <$> generate profile (init profile) |>.rndCon

def testProfile : Poseidon.Profile := {
  N := 1275
  t := 5
  fullRounds := 8
  partialRounds := 60
  prime := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
  a := 5
  sBox := fun x => x^5
}