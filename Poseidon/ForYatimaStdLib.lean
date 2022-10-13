import YatimaStdLib.Zmod
import YatimaStdLib.NonEmpty

open Float (log)

def Zmod.norm (x : Zmod n) : Nat :=
  if x < 0 then (x.rep - (x.rep / n - 1) * n).toNat else x.toNat

instance : Repr (Zmod n) where
  reprPrec n _ := s!"0x{Nat.toDigits 16 n.norm |>.asString}"

def repeatM {m : Type _ → Type _} [Monad m] (f : m PUnit) : Nat → m PUnit
  | 0 => pure ()
  | n + 1 => f *> repeatM f n

partial def repeatWhile {m : Type _ → Type _} [Monad m] (test : m Bool) (f : m PUnit) : m PUnit := 
  test >>= fun b => if b then f *> (repeatWhile test f) else pure ()

def NEList.min {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ as.min then a else as.min

def NEList.max {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ as.max then as.max else a

def allProd (as : List α) (bs : List β) : List (α × β) 
  := as.map (fun a => bs.map fun b => (a, b)) |>.join

def List.minWith (f : α → β) [LE β] [DecidableRel (@LE.le β _)] : List α → Option α 
  | [] => .none
  | a :: as => match as.minWith f with
    | .some a' => if f a ≤ f a' then .some a else .some a'
    | .none => .some a

def Float.toNat : Float → Nat := USize.toNat ∘ Float.toUSize

def logBase (base arg : Float) : Float := log arg / log base

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

def ByteArray.padLeft (bs : ByteArray) (u : UInt8) : Nat → ByteArray
  | 0 => bs
  | n + 1 => ByteArray.mk #[u] ++ bs.padLeft u n

partial def UInt64.toByteArray (u : UInt64) : ByteArray := 
  let rec loop (u : UInt64) (acc : Array UInt8) :=
    if u == 0 then acc else loop (u >>> 8) <| acc.push (u &&& (0xff : UInt64)).toUInt8
  loop u #[] |>.reverse 
             |> ByteArray.mk
             |> (fun bs => bs.padLeft 0 (8 - bs.size))
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
def bArXOr (bs : Array Bit) : Bit := bs.foldl (fun b b' => b.xOr b') zero

def bArToNat (bs : Array Bit) : Nat := bs.foldl (fun b b' => b*2 + b'.toNat) 0

def ByteArray.getD (bs : ByteArray) (idx : Int) : UInt8 :=
  if idx < 0 || bs.size ≤ idx then 0 else bs[idx.toNat]!

def UInt8.getBit (u : UInt8) (n : Nat) : Bit := 
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then zero else one

def ByteArray.getBit (bs : ByteArray) (n : Nat) : Bit := 
  let (idx, rem) := (n / 8, n%8) 
  bs[idx]!.getBit rem
-- Shifts the byte array left by 1, preserves length (so in particular kills the first coefficient
def ByteArray.shiftLeft (bs : ByteArray) : ByteArray := Id.run do
  let mut answer : ByteArray := .mkEmpty bs.size
  for idx in [:bs.size] do
    answer := answer.push <| (bs[idx]! <<< 1) + (bs.getD (idx + 1) >>> 7)
  answer

def ByteArray.shiftAdd (bs : ByteArray) (b : Bit) : ByteArray :=
  let ans := bs.shiftLeft
  ans.set! (ans.size - 1) (ans[(ans.size - 1)]! + b.toUInt8)
