import Lake
open Lake DSL

package Poseidon 

@[defaultTarget]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "cbf5cd7c098c4369d93b9b8399a323bf0a28c107"

require LSpec from git
   "https://github.com/yatima-inc/LSpec" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"
