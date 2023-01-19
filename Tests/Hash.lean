import LSpec
import Poseidon
import Poseidon.Parameters.Lurk
import Poseidon.Parameters.PermX5_254_3
import Poseidon.Parameters.PermX5_254_5
import Poseidon.Parameters.PermX5_255_3
import Poseidon.Parameters.PermX5_255_5
import Poseidon.Parameters.HashTestPyProfiles

/-!
# Poseidon hashing tests

This module contains tests for the main hash function found in `Poseidon.Hash` and `Poseidon.HashImpl`
-/

open LSpec Poseidon

section Test

/- The following tests are taken from the reference implementation `test_vectors.txt` -/
section ReferenceImplementation

section PermX5_254_3

def PermX5_254_3.input : Vector (Zmod PermX5_254_3.p) :=
#[0x0000000000000000000000000000000000000000000000000000000000000000,
  0x0000000000000000000000000000000000000000000000000000000000000001,
  0x0000000000000000000000000000000000000000000000000000000000000002]

def PermX5_254_3.output : Vector (Zmod PermX5_254_3.p) :=
#[0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a,
  0x0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29,
  0x0e7ae82e40091e63cbd4f16a6d16310b3729d4b6e138fcf54110e2867045a30c]

open PermX5_254_3 in
def permX5_254_3_test := test "Perm_x5_254_3 hashes match" $
  Poseidon.hashInputWithCtx PermX5_254_3 PermX5_254_3.Context input == output

end PermX5_254_3

section PermX5_254_5

def PermX5_254_5.input : Vector (Zmod PermX5_254_5.p) :=
#[0x0000000000000000000000000000000000000000000000000000000000000000,
  0x0000000000000000000000000000000000000000000000000000000000000001,
  0x0000000000000000000000000000000000000000000000000000000000000002,
  0x0000000000000000000000000000000000000000000000000000000000000003,
  0x0000000000000000000000000000000000000000000000000000000000000004]

def PermX5_254_5.output : Vector (Zmod PermX5_254_5.p) :=
#[0x299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465,
  0x1148aaef609aa338b27dafd89bb98862d8bb2b429aceac47d86206154ffe053d,
  0x24febb87fed7462e23f6665ff9a0111f4044c38ee1672c1ac6b0637d34f24907,
  0x0eb08f6d809668a981c186beaf6110060707059576406b248e5d9cf6e78b3d3e,
  0x07748bc6877c9b82c8b98666ee9d0626ec7f5be4205f79ee8528ef1c4a376fc7]

open PermX5_254_5 in
def permX5_254_5_test := test "Perm_x5_254_5 hashes match" $
  Poseidon.hashInputWithCtx PermX5_254_5 PermX5_254_5.Context input == output

end PermX5_254_5

section PermX5_255_3

def PermX5_255_3.input : Vector (Zmod PermX5_255_3.p) := 
#[0x0000000000000000000000000000000000000000000000000000000000000000,
  0x0000000000000000000000000000000000000000000000000000000000000001,
  0x0000000000000000000000000000000000000000000000000000000000000002]

def PermX5_255_3.output : Vector (Zmod PermX5_255_3.p) := 
#[0x28ce19420fc246a05553ad1e8c98f5c9d67166be2c18e9e4cb4b4e317dd2a78a,
  0x51f3e312c95343a896cfd8945ea82ba956c1118ce9b9859b6ea56637b4b1ddc4,
  0x3b2b69139b235626a0bfb56c9527ae66a7bf486ad8c11c14d1da0c69bbe0f79a]

open PermX5_255_3 in
def permX5_255_3_test := test "Perm_x5_255_3 hashes match" $
  Poseidon.hashInputWithCtx PermX5_255_3 PermX5_255_3.Context input == output

end PermX5_255_3

section PermX5_255_5

def PermX5_255_5.input : Vector (Zmod PermX5_255_5.p) := 
#[0x0000000000000000000000000000000000000000000000000000000000000000,
  0x0000000000000000000000000000000000000000000000000000000000000001,
  0x0000000000000000000000000000000000000000000000000000000000000002,
  0x0000000000000000000000000000000000000000000000000000000000000003,
  0x0000000000000000000000000000000000000000000000000000000000000004]

def PermX5_255_5.output : Vector (Zmod PermX5_255_5.p) := 
#[0x2a918b9c9f9bd7bb509331c81e297b5707f6fc7393dcee1b13901a0b22202e18,
  0x65ebf8671739eeb11fb217f2d5c5bf4a0c3f210e3f3cd3b08b5db75675d797f7,
  0x2cc176fc26bc70737a696a9dfd1b636ce360ee76926d182390cdb7459cf585ce,
  0x4dc4e29d283afd2a491fe6aef122b9a968e74eff05341f3cc23fda1781dcb566,
  0x03ff622da276830b9451b88b85e6184fd6ae15c8ab3ee25a5667be8592cce3b1]

open PermX5_255_5 in
def permX5_255_5_test := test "Perm_x5_255_5 hashes match" $
  Poseidon.hashInputWithCtx PermX5_255_5 PermX5_255_5.Context input == output

end PermX5_255_5

def refTests : TestSeq := group "Reference implementation hash tests" $ 
  permX5_254_3_test ++ permX5_254_5_test ++ permX5_255_3_test ++ permX5_255_5_test

end ReferenceImplementation

/- The following tests are taken from the Python implementation -/
section PythonImplementation

def output254 : Zmod pyProfile254.p := 0x1357e867b0efbd9d865420117785ee2c9360745c7c5b4bc11782be67e6cb0b59

def py254_test := test "pyProfile254 hashes match" $
  (Poseidon.hashInputWithCtx pyProfile254 pyProfile254.Context #[0,1,2])[1]! == output254

def output255 : Zmod pyProfile255.p := 0x4415f84efb53753a723c8a57fc8a56038b88471d4bb32fb8d82240289fd0a33d

def py255_test := test "pyProfile255 hashes match" $
  (Poseidon.hashInputWithCtx pyProfile255 pyProfile255.Context #[0,1,2,3,4])[1]! == output255

def pyTests : TestSeq := group "Python implementation hash tests" $
  py254_test ++ py255_test

end PythonImplementation

/-
The following tests are generated from the Filecoin implementation using the following rust script:
<https://gist.github.com/mpenciak/003a74bcab5ccda33e3066debb7cb7af>
-/
section FilecoinImplementation

def testSec (arity : Nat) : SecProfile := {
  M := 128
  t := arity + 1
  p := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
  a := 5
}

def partRoundsFix : Nat → Nat
  | 2 => 55
  | 4 | 5 => 56
  | 8 | 11 => 57
  | 16 | 24 => 59
  | 36 => 60
  | n => testSec n |>.hashProfile true |>.partRounds

def testProfile (arity : Nat) : HashProfile := {
  testSec arity with
  fullRounds := 8
  partRounds := partRoundsFix arity
}

def testContext (arity : Nat) : Hash.Context (testProfile arity) := {
  mdsMatrix := generatePoseidonMDS (testProfile arity).p (arity + 1)
  roundConst := Poseidon.generateRConstants false (testProfile arity)
}

def testInput (arity : Nat) : Array $ Zmod (testProfile arity).p := 
  List.iota arity |>.reverse 
                  |>.map (Coe.coe ∘ Nat.pred)
                  |>.toArray

def runTest (arity : Nat) (domain : Domain) := 
  Poseidon.hash (testProfile arity) (testContext arity) (testInput arity) domain

def arity2Test := test "Arity 2 hash matches" $
  runTest 2 .merkleTree == 0x396508d75e76a56b739e0fd902efe161a6fba9339d05a69d2e203c369a02e7ff
def arity4Test := test "Arity 4 hash matches" $
  runTest 4 .merkleTree == 0x58a54b10a9e5848a00db3c6579229399fb6b4605bf1327ec019814ff6662075d
def arity5Test := test "Arity 5 hash matches" $
  runTest 5 .merkleTree == 0x6be783a29264a3f265318717f5d7a0406aed498275f024558e98cd34f6ee687d
def arity8Test := test "Arity 8 hash matches" $
  runTest 8 .merkleTree == 0x2394611da3a5de5512010042116770774b682e9d9cc4aed92a9934f56d38a5e6
def arity11Test := test "Arity 11 hash matches" $
  runTest 11 .merkleTree == 0x0c0fc1b2e5227f286ca537e232ebe87a09f3dcd8ccb08fc1cee3bbc32b693163
def arity16Test := test "Arity 16 hash matches" $
  runTest 16 .merkleTree == 0x2d3ae2663381ae8ac1c2fb5a6f871e635b8dbc6d30680a6f1291c74060266d37
def arity24Test := test "Arity 24 hash matches" $
  runTest 24 .merkleTree == 0x63beb8831f11ae15066f39bf783f3d9fc3e779f6468815b1d7ef3569f585b321
def arity36Test := test "Arity 36 hash matches" $
  runTest 36 .merkleTree == 0x699303082a6e5d5f540a30e03c10bbaa75cd368df8a8ac3c4473606dfa4e8140

def arityTests : TestSeq := group "Merkle tree fixed arity tests" $
  arity2Test ++ arity4Test ++ arity5Test ++ arity8Test ++ arity11Test ++ arity16Test ++ arity24Test ++ arity36Test

def length2Test := test "Length 2 hash matches" $
  runTest 2 .fixedLength == 0x04e709f77fd728223a1c0b283010a0873b5775d0ba06433304f735ffc2e669bd
def length4Test := test "Length 4 hash matches" $
  runTest 4 .fixedLength == 0x3a21a6ae86754a2939443980077d75934984de08542c99778935b00a07909d45
def length5Test := test "Length 5 hash matches" $
  runTest 5 .fixedLength == 0x459e4319f97c1f417ebdef68223b098af7ecb0d4d16e00a0d5d68daa93913a23
def length8Test := test "Length 8 hash matches" $
  runTest 8 .fixedLength == 0x25d3a8bd42833f107c4a67999ee7d77d49e9c1d71b5496bfb4ca8e7be58a8f02
def length11Test := test "Length 11 hash matches" $
  runTest 11 .fixedLength == 0x264ce24c59ecaf3d1b8467924198c7bf7ee4d33be28e8bf3b7d1bd0950da6b14
def length16Test := test "Length 16 hash matches" $
  runTest 16 .fixedLength == 0x3c314071b81b71e8834e7fbfa18ccb160325f9b740c8eff2ce7960dbce194478
def length24Test := test "Length 24 hash matches" $
  runTest 24 .fixedLength == 0x136af1567a79e7ac24e63db464d2637895e6a800d333e74f1e7d6a7b872cd14f
def length36Test := test "Length 36 hash matches" $
  runTest 36 .fixedLength == 0x6468d3da7ff183f37e409ff379a7ea4f57c52956eb4c412a3f9c5325e0c056d5

def lengthTests : TestSeq := group "Fixed length input tests" $
  length2Test ++ length4Test ++ length5Test ++ length8Test ++ length11Test ++ length16Test ++ length24Test ++ length36Test

def rustTests : TestSeq := group "Filecoin implementation hash tests" $
  arityTests ++ lengthTests

end FilecoinImplementation

def main : IO UInt32 := do
  IO.println "------------------------"
  IO.println "Testing hash calculation"
  IO.println "------------------------"
  lspecIO $ refTests ++ pyTests ++ rustTests