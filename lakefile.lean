import Lake
open Lake DSL

package Poseidon 

@[default_target]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "2b914196a8c67838e63c1c1e44eaf339b8a50eb7"

require LSpec from git
   "https://github.com/yatima-inc/LSpec" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

-- Tests
lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash