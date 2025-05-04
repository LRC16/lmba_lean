-- This module serves as the root of the `Theorems` library.
-- Import modules here that should be built as part of the library.
import Theorems.Basic

import Lean.Elab.Tactic.BVDecide
import Mathlib

theorem my_not_and (x y : BitVec 32) :
  ~~~(x &&& y) = ~~~x ||| ~~~y := by
  rw [BitVec.not_and]

theorem my_not_or (x y : BitVec 32) :
  ~~~(x ||| y) = ~~~x &&& ~~~y := by
  rw [BitVec.not_or]

theorem my_not_xor_eq_or (x y : (BitVec 32)) :
  ~~~(x ^^^ y) = (~~~x &&& ~~~y) ||| (x &&& y) := by
  bv_decide

theorem my_xor_eq_or (x y : (BitVec 32)) :
  (x ^^^ y) = (~~~x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

theorem my_x_distr (x y: BitVec 32) :
  x = (x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

theorem my_y_distr (x y: BitVec 32) :
  y = (x &&& y ||| ~~~x &&& y) := by
  bv_decide

theorem my_add (x y z: BitVec 32) (h: x + y = z):
  x + y = z := by
  apply h

theorem my_add_assoc (x y z : BitVec 32) :
  x + y + z = x + (y + z) := by
  rw [BitVec.add_assoc]

theorem my_add_comm(x y : BitVec 32) :
  x + y = y + x := by
  rw[BitVec.add_comm]

theorem my_add_neg_eq_sub {x y : BitVec 32} :
  x + -y = x - y := by
  rw [BitVec.add_neg_eq_sub]

theorem my_mul_comm (x y : BitVec 32) :
  x * y = y * x := by
  rw [BitVec.mul_comm]

theorem my_var_mul_comm (x y z: BitVec 32) : (x &&& y) * z = z * (x &&& y) := by
  rw [BitVec.mul_comm]

theorem my_mul_add (x y z : BitVec 32) :
  x * (y + z) = x * y + x * z := by
  rw [BitVec.mul_add]

theorem my_neg_eq_mul (x : BitVec 32) :
  -x = x *  (BitVec.allOnes 32) := by
  rw [← BitVec.neg_one_eq_allOnes]
  rw [BitVec.mul_neg]
  rw [BitVec.mul_one]

theorem my_add_mul_one (x y : BitVec 32) :
  x + x * y = x * (1#32 + y) := by
  nth_rw 1 [← BitVec.mul_one x]
  rw [← BitVec.mul_add]


theorem my_neg_mul (x y : BitVec 32) :
  -x * y = -(x * y) := by
  simp

theorem my_or_eq_add1 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& y) = (x &&& y) + (~~~x &&& y) := by
  bv_decide

theorem my_or_eq_add2 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& ~~~y) = (x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add3 (x y : BitVec 32) :
  (x &&& y) ||| (x &&& ~~~y) = (x &&& y) + (x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add4 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (~~~x &&& y) = (~~~x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem my_or_eq_add5 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& ~~~y) = (~~~x &&& ~~~y) + (x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add6 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& y) = (~~~x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem my_or_eq_add7 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& y) = (x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem my_or_eq_add8 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& ~~~y) = (x &&& ~~~y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add9 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (x &&& y) = (x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem my_or_eq_add10 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add11 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add12 (x y : BitVec 32) :
  (~~~x &&& y) ||| (x &&& ~~~y) = (~~~x &&& y) + (x &&& ~~~y) := by
  bv_decide

theorem my_or_eq_add_three (x y : BitVec 32) : (x ||| y) = (x &&& ~~~y) + (x &&& y) + (~~~x &&& y) := by
 bv_decide

theorem my_sum_all (x y : BitVec 32) :
  (~~~x &&& ~~~y) + (~~~x &&& y) + (x &&& y) + (x &&& ~~~y) = BitVec.allOnes 32 := by
  bv_decide




theorem mba_challenge_a99d8fd0 (x y : (BitVec 32)) :
  ((((((Int32.toBitVec (4294967296-4)) * (~~~(x ^^^ y))) + ((Int32.toBitVec (14)) * (~~~(x ||| y)))) + ((Int32.toBitVec (8)) * (~~~(x ||| (~~~y))))) + ((Int32.toBitVec 2) * (x &&& (~~~y)))) + ((Int32.toBitVec (4)) * (x &&& y))) = (((Int32.toBitVec 2) * (~~~y)) + ((Int32.toBitVec 8) * (~~~x))) := by
  rw [my_not_xor_eq_or]
  rw [my_or_eq_add6]
  rw [my_mul_add]
  simp [my_not_or]
  simp only [my_mul_comm]
  simp [my_mul_comm 14#32]
  nth_rw 4 [my_add_comm]
  nth_rw 1 [← my_add_assoc]
  simp [← my_mul_add]

  rw [my_mul_comm 4#32]
  nth_rw 4 [my_add_comm]
  nth_rw 1 [my_add_comm]
  simp [← my_add_assoc]
  simp [← my_mul_add]
  rw [BitVec.add_comm ((~~~x &&& ~~~y) * 10#32) (8#32 * (~~~x &&& y))]
  rw [← my_add 2#32 8#32 10#32]
  rw [my_mul_add]
  simp [← my_add_assoc]
  simp [my_var_mul_comm]
  simp [my_add_comm]
  simp [← my_add_assoc]
  rw [← my_mul_add]
  rw [← my_or_eq_add8]
  rw [← my_y_distr]
  rw [my_add_assoc]
  rw [← my_mul_add]
  rw [← my_or_eq_add10]
  rw [← my_x_distr]
  abel



theorem mba_challenge_7b1a4532 (x y : BitVec 32) :
  ((((Int32.toBitVec (-1)) * (~~~(x &&& (~~~y)))) - ((Int32.toBitVec (3)) * (x ^^^ y))) + (Int32.toBitVec (4) * (~~~(x ||| (~~~y))))) = (((Int32.toBitVec (-1)) * (x ||| (~~~y))) - (Int32.toBitVec (2) * (x &&& (~~~y)))) := by


  try simp [← my_add_neg_eq_sub]
  try simp [← my_neg_mul]
  try simp [my_not_and, my_not_or]


  try simp [my_not_xor_eq_or]
  try simp [my_xor_eq_or]
  try simp [my_or_eq_add1, my_or_eq_add2, my_or_eq_add3, my_or_eq_add4, my_or_eq_add5, my_or_eq_add6, my_or_eq_add7, my_or_eq_add8, my_or_eq_add9, my_or_eq_add10, my_or_eq_add11, my_or_eq_add12]
  try simp [my_or_eq_add_three]
  simp [my_mul_add]
  rw [my_add_comm (4294967293#32 * (~~~x &&& y))]
  simp [← my_add_assoc]
  simp [← my_var_mul_comm]
  rw [my_add_assoc]
  simp [← my_mul_add]
  nth_rw 4 [my_add_assoc]
  rw [my_add_comm ((~~~x &&& ~~~y) * 4294967295#32) ((x &&& ~~~y) * 4294967294#32)]
  simp [← my_add_assoc]
  nth_rw 5 [my_add_assoc]
  simp [← my_mul_add]
  rw [my_add_comm]
  simp [← my_add_assoc]
  nth_rewrite 3 [my_add_comm]
  simp [← my_add_assoc]
  nth_rewrite 4 [my_add_comm]
  simp [my_add_mul_one]
  abel















theorem mba_challenge_34178047 (x y : BitVec 32) :
  ((((((Int32.toBitVec (-4)) * (x ||| y)) + ((Int32.toBitVec (4)) * (~~~(x &&& (~~~x))))) + ((Int32.toBitVec (8)) * (~~~(x &&& (~~~y))))) - ((Int32.toBitVec (12)) * (~~~(x ||| y)))) - ((Int32.toBitVec (8)) * (~~~(x ||| (~~~y))))) = ((Int32.toBitVec (8)) * (x &&& y)) := by


  try simp [BitVec.neg_mul]
  try simp [← BitVec.add_neg_eq_sub]
  try simp [← BitVec.neg_mul]
  try simp [my_not_and, my_not_or]


  try simp [my_not_xor_eq_or]
  try simp [my_xor_eq_or]
  try simp [my_or_eq_add1, my_or_eq_add2, my_or_eq_add3, my_or_eq_add4, my_or_eq_add5, my_or_eq_add6, my_or_eq_add7, my_or_eq_add8, my_or_eq_add9, my_or_eq_add10, my_or_eq_add11, my_or_eq_add12]
  try simp [my_or_eq_add_three]


  try simp [my_mul_add]

  try nth_rewrite 2 [my_add_assoc]
  rw [my_add_comm _ (4294967284#32 * (~~~x &&& ~~~y))]
  nth_rewrite 2 [← my_add_assoc]
  nth_rewrite 2 [← my_add_assoc]
  simp [← my_mul_add]
  simp [← my_var_mul_comm]
  simp [← my_mul_add]
  simp [my_var_mul_comm]
  simp [← my_add_assoc]
  nth_rw 4 [my_add_assoc]
  rw [my_add_comm 4294967292#32]
  simp [← my_add_assoc]
  simp [← my_mul_add]
  rw [my_add_comm ((x &&& ~~~y) + (x &&& y) + (~~~x &&& y))  (~~~x &&& ~~~y)]
  rw [my_add_comm ((x &&& ~~~y) + (x &&& y))  (~~~x &&& y)]
  rw [my_add_comm (x &&& ~~~y) (x &&& y)]
  simp [← my_add_assoc]
  simp [my_sum_all]
  rw [my_add_comm]
  rw [← my_add_assoc]
  simp [←  my_var_mul_comm]
  simp [← my_mul_add]
