/-!
# Generates the Poseidon Round Constants

TODO : Add documentation
-/

def UInt8.showBits (u : UInt8) : String := 
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def ByteArray.toString (bs : ByteArray) : String := Id.run do
  if bs.isEmpty then "b[]" else
  let mut ans := "b["
  for u in bs do
    ans := ans ++ u.showBits ++ ","
  return ans.dropRight 1 ++ "]"

instance : Repr ByteArray where
  reprPrec bs _ := bs.toString

def fieldBits (isPrime : Bool) : UInt64 := if isPrime then 1 else 0

def sBoxBits : Int → UInt64
  | -1 => 2
  |  3 => 0
  |  5 => 1
  |  _ => 3

def p := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def fieldSizeBits (prime : Nat) : UInt64 := prime.log2 + 1 |>.toUInt64

private def padOne (u : UInt64) : Nat → UInt64
  | 0     => u
  | n + 1 => (u <<< 1) + 1 |> (padOne · n)

-- TODO : Figure out if choosing to reverse is a bad idea

partial def UInt64.toByteArray (u : UInt64) : ByteArray := 
  let rec loop (u : UInt64) (acc : Array UInt8) :=
    if u == 0 then acc else loop (u >>> 8) <| acc.push (u &&& (0xff : UInt64)).toUInt8
  loop u #[] |>.reverse 
             |> ByteArray.mk

def grainStateInit (isPrime : Bool) (a : Int) (prime : Nat) (t fullRound partialRound : UInt64) := 
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

def ByteArray.getBit (bs : ByteArray) (n : Nat) : Bool := 
  let (idx, rem) := (n / 8, 2^(n % 8) |>.toUInt8)
  not $ bs.get! (bs.size - 1 - idx) &&& rem == 0 

#eval (grainStateInit true 5 p 5 8 41)

#eval 0b10000000 >>> 7

structure RCState where
  state : ByteArray
  

abbrev RoundConstantsM := StateM ByteArray