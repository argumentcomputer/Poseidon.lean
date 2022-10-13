import LSpec
import Poseidon.Hash
import Poseidon.Parameters.PoseidonPerm255

open LSpec

namespace Poseidon 

section poseidonperm_x5_255_5

def testProfile : Poseidon.HashProfile := PermX5_255_5

def testContext : Poseidon.Hash.Context testProfile := {
  mdsMatrix := PermX5_255_5.MDS
  roundConst := PermX5_255_5.roundConstants
}

def input : Vector (Zmod testProfile.p) := 
            #[0x0000000000000000000000000000000000000000000000000000000000000000,
              0x0000000000000000000000000000000000000000000000000000000000000001,
              0x0000000000000000000000000000000000000000000000000000000000000002,
              0x0000000000000000000000000000000000000000000000000000000000000003,
              0x0000000000000000000000000000000000000000000000000000000000000004]

def output : Vector (Zmod testProfile.p) := 
             #[0x2a918b9c9f9bd7bb509331c81e297b5707f6fc7393dcee1b13901a0b22202e18,
               0x65ebf8671739eeb11fb217f2d5c5bf4a0c3f210e3f3cd3b08b5db75675d797f7,
               0x2cc176fc26bc70737a696a9dfd1b636ce360ee76926d182390cdb7459cf585ce,
               0x4dc4e29d283afd2a491fe6aef122b9a968e74eff05341f3cc23fda1781dcb566,
               0x03ff622da276830b9451b88b85e6184fd6ae15c8ab3ee25a5667be8592cce3b1]

#lspec 
  test "poseidonperm_x5_255_5" (Poseidon.hash testProfile testContext input == output)

end poseidonperm_x5_255_5