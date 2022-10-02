import LSpec
import Poseidon.Util.Matrix

open LSpec Vector

section vector_tests

def v1 : Vector Int := #[1, 3, -3]
def v2 : Vector Int := #[3, -1, 2]

#lspec
  test "vector addition" (v1 + v2 = #[4, 2, -1]) $
  test "vector dot" (dot v1 v2 = -6) $
  test "vector scale" ((-2) * v2 = #[-6, 2, -4]) $
  test "vector 0" (zero Int 4 = #[0,0,0,0] )

end vector_tests

section matrix_tests

open Matrix

def m1 : Matrix Int := #[#[1, 4, 7], #[2, 5, 8], #[3, 6, 9]]
def m2 : Matrix Int := #[#[-1, 2, 1], #[3, -1, 1], #[2, 2, 1]]

#lspec
  test "row works" (row m1 0 = #[1,2,3]) $
  test "transpose works" (transpose m1 = #[#[1,2,3],#[4, 5, 6], #[7, 8, 9]]) $
  test "action works" (action m1 v2 = #[7, 19, 31]) $
  test "mul works" (mul m1 m2 = #[#[6, 12, 18], #[4, 13, 22], #[9, 24, 39]])

end matrix_tests
