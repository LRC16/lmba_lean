import Lean.Elab.Tactic.BVDecide
import Mathlib

@[simp]
theorem bv32_and_not_self(x : BitVec 32) :
  x &&& ~~~x = 0 := by 
  simp

@[simp]
theorem bv32_not_and_self(x : BitVec 32) :
  ~~~x &&& x = 0 := by 
  simp

@[simp]
theorem bv32_or_not_self(x : BitVec 32) :
  x ||| ~~~x = BitVec.allOnes 32 := by 
  simp

@[simp]
theorem bv32_not_or_self(x : BitVec 32) :
  ~~~x ||| x = BitVec.allOnes 32 := by 
  simp

@[simp]
theorem bv32_neg_mul (x y : BitVec 32) :
  -x * y = -(x * y) := by
  simp

theorem bv32_not_and (x y : BitVec 32) :
  ~~~(x &&& y) = ~~~x ||| ~~~y := by
  rw [BitVec.not_and]

theorem bv32_not_or (x y : BitVec 32) :
  ~~~(x ||| y) = ~~~x &&& ~~~y := by
  rw [BitVec.not_or]

theorem bv32_not_xor_eq_or (x y : (BitVec 32)) :
  ~~~(x ^^^ y) = (~~~x &&& ~~~y) ||| (x &&& y) := by
  bv_decide

theorem bv32_xor_eq_or (x y : (BitVec 32)) :
  (x ^^^ y) = (~~~x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

theorem bv32_x_distr (x y: BitVec 32) :
  x = (x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

theorem bv32_y_distr (x y: BitVec 32) :
  y = (x &&& y ||| ~~~x &&& y) := by
  bv_decide

theorem bv32_add (x y z: BitVec 32) (h: x + y = z):
  x + y = z := by
  apply h

theorem bv32_add_assoc (x y z : BitVec 32) :
  x + y + z = x + (y + z) := by
  rw [BitVec.add_assoc]

theorem bv32_add_comm(x y : BitVec 32) :
  x + y = y + x := by
  rw[BitVec.add_comm]

theorem bv32_add_neg_eq_sub {x y : BitVec 32} :
  x + -y = x - y := by
  rw [BitVec.add_neg_eq_sub]

theorem bv32_mul_comm (x y : BitVec 32) :
  x * y = y * x := by
  rw [BitVec.mul_comm]

theorem bv32_var_mul_comm (x y z: BitVec 32) : (x &&& y) * z = z * (x &&& y) := by
  rw [BitVec.mul_comm]

theorem bv32_mul_add (x y z : BitVec 32) :
  x * (y + z) = x * y + x * z := by
  rw [BitVec.mul_add]

theorem bv32_neg_eq_mul (x : BitVec 32) :
  -x = x *  (BitVec.allOnes 32) := by
  rw [← BitVec.negOne_eq_allOnes]
  rw [BitVec.mul_neg]
  rw [BitVec.mul_one]

theorem bv32_add_mul_one (x y : BitVec 32) :
  x + x * y = x * (1#32 + y) := by
  rw [BitVec.mul_add]
  rw [BitVec.mul_one]

theorem bv32_or_eq_add1 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& y) = (x &&& y) + (~~~x &&& y) := by
  bv_decide

theorem bv32_or_eq_add2 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& ~~~y) = (x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add3 (x y : BitVec 32) :
  (x &&& y) ||| (x &&& ~~~y) = (x &&& y) + (x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add4 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (~~~x &&& y) = (~~~x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem bv32_or_eq_add5 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& ~~~y) = (~~~x &&& ~~~y) + (x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add6 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& y) = (~~~x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem bv32_or_eq_add7 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& y) = (x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem bv32_or_eq_add8 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& ~~~y) = (x &&& ~~~y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add9 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (x &&& y) = (x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem bv32_or_eq_add10 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add11 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add12 (x y : BitVec 32) :
  (~~~x &&& y) ||| (x &&& ~~~y) = (~~~x &&& y) + (x &&& ~~~y) := by
  bv_decide

theorem bv32_or_eq_add_three (x y : BitVec 32) : (x ||| y) = (x &&& ~~~y) + (x &&& y) + (~~~x &&& y) := by
 bv_decide

theorem bv32_sum_all (x y : BitVec 32) :
  (~~~x &&& ~~~y) + (~~~x &&& y) + (x &&& y) + (x &&& ~~~y) = BitVec.allOnes 32 := by
  bv_decide
/-- 
Let x,y be 32-bit bit-vectors. Prove the equivalence of the following two expressions: $-3\cdot \lnot (x\oplus y)-2\cdot (x\oplus y)+2\cdot (x\lor y)+3\cdot (x\lor \lnot y)-5\cdot \lnot (x\lor y)-5\cdot \lnot (x\lor \lnot y)-8\cdot (x\land \lnot y)$, $2\cdot (x\land y)-5\cdot \lnot (x\land y)$
-/ 
theorem mba_challenge_cad41c6d (x y : BitVec 32) :  -3#32 * ~~~(x ^^^ y) - 2#32 * (x ^^^ y) + 2#32 * (x ||| y) + 3#32 * (x ||| ~~~y) - 5#32 * ~~~(x ||| y) - 5#32 * ~~~(x ||| ~~~y) - 8#32 * (x &&& ~~~y) = 2#32 * (x &&& y) - 5#32 * ~~~(x &&& y) := by
  sorry
