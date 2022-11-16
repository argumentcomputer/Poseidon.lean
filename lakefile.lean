import Lake
open Lake DSL

package Poseidon 

@[default_target]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f905b68f529de2af44cf6ea63489b7e3cd090050"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

-- Tests
lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash