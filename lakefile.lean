import Lake
open Lake DSL

package Poseidon 

@[defaultTarget]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "11336e502174b1449f525b1e44d76f6a44fbd274"

require LSpec from git
   "https://github.com/yatima-inc/LSpec" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"

-- Tests
lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash