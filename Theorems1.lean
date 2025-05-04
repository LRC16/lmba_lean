-- This module serves as the root of the `Theorems` library.
-- Import modules here that should be built as part of the library.
import Theorems.Basic

import Lean.Elab.Tactic.BVDecide

import Mathlib



theorem t1 (x y : (BitVec 32)) :
  ~~~(x ^^^ y) = (~~~x &&& ~~~y) ||| (x &&& y) := by
  bv_decide

theorem t2 (x y : (BitVec 32)) :
  (x ^^^ y) = (~~~x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

--BitVec.not_and

--BitVec.not_or

--BitVec.not_not

/- theorem t3 (x y : (BitVec 32)) :
  x &&& (x ||| y) = x := by
  bv_decide


theorem t4 (x y : (BitVec 32)) :
  x &&& (y ||| x) = x := by
  bv_decide


theorem t5 (x y : (BitVec 32)) :
  (y ||| x) &&& x = x := by
  bv_decide

theorem t6 (x y : (BitVec 32)) :
  (x ||| y) &&& x = x := by
  bv_decide -/

theorem neg (x : BitVec 32) :
  -x = x *  (BitVec.allOnes 32) := by
  rw [← BitVec.neg_one_eq_allOnes]
  rw [BitVec.mul_neg]
  rw [BitVec.mul_one]

theorem add_mul_one (x y : BitVec 32) :
  x + x * y = x * (1#32 + y) := by
  nth_rw 1 [← BitVec.mul_one x]
  rw [← BitVec.mul_add]




theorem all (x y : BitVec 32) :
  (~~~x &&& ~~~y) + (~~~x &&& y) + (x &&& y) + (x &&& ~~~y) = BitVec.allOnes 32 := by
  bv_decide



theorem r1 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& y) = (x &&& y) + (~~~x &&& y) := by
  bv_decide

theorem r2 (x y : BitVec 32) :
  (x &&& y) ||| (~~~x &&& ~~~y) = (x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem r3 (x y : BitVec 32) :
  (x &&& y) ||| (x &&& ~~~y) = (x &&& y) + (x &&& ~~~y) := by
  bv_decide

theorem r5 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (~~~x &&& y) = (~~~x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem r6 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& ~~~y) = (~~~x &&& ~~~y) + (x &&& ~~~y) := by
  bv_decide

theorem r7 (x y : BitVec 32) :
  (~~~x &&& ~~~y) ||| (x &&& y) = (~~~x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem r8 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& y) = (x &&& ~~~y) + (~~~x &&& y) := by
  bv_decide

theorem r9 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (~~~x &&& ~~~y) = (x &&& ~~~y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem r10 (x y : BitVec 32) :
  (x &&& ~~~y) ||| (x &&& y) = (x &&& ~~~y) + (x &&& y) := by
  bv_decide

theorem r11 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem r12 (x y : BitVec 32) :
  (~~~x &&& y) ||| (~~~x &&& ~~~y) = (~~~x &&& y) + (~~~x &&& ~~~y) := by
  bv_decide

theorem r4 (x y : BitVec 32) :
  (~~~x &&& y) ||| (x &&& ~~~y) = (~~~x &&& y) + (x &&& ~~~y) := by
  bv_decide


theorem a1 (x y: BitVec 32) :
  x = (x &&& y) ||| (x &&& ~~~y) := by
  bv_decide

theorem a2 (x y: BitVec 32) :
  y = (x &&& y ||| ~~~x &&& y) := by
  bv_decide

lemma l10 : 10#32 = 8#32 + 2#32 := by
  bv_decide

theorem r13 (x y : BitVec 32) : (~~~x ||| y) = (~~~x &&& y) + (~~~x &&& ~~~y) + (x &&& y) := by
 bv_decide

theorem r14 (x y : BitVec 32) : (x ||| ~~~y) = (x &&& ~~~y) + (~~~x &&& ~~~y) + (x &&& y) := by
 bv_decide

 theorem r15 (x y : BitVec 32) : (x ||| y) = (~~~x &&& y) + (x &&& y) + (x &&& ~~~y) := by
 bv_decide

theorem r16 (x y : BitVec 32) : (~~~x ||| ~~~y) = (x &&& ~~~y) + (~~~x &&& ~~~y) + (~~~x &&& y) := by
 bv_decide

theorem mul_swap (x y z: BitVec 32) : (x &&& y ) * z = z * (x &&& y) := by
  rw [BitVec.mul_comm]






theorem mba_challenge_a99d8fd0 (x y : (BitVec 32)) :
  ((((((Int32.toBitVec (4294967296-4)) * (~~~(x ^^^ y))) + ((Int32.toBitVec (14)) * (~~~(x ||| y)))) + ((Int32.toBitVec (8)) * (~~~(x ||| (~~~y))))) + ((Int32.toBitVec 2) * (x &&& (~~~y)))) + ((Int32.toBitVec (4)) * (x &&& y))) = (((Int32.toBitVec 2) * (~~~y)) + ((Int32.toBitVec 8) * (~~~x))) := by
/-   try simp [BitVec.neg_mul]
  try simp [← BitVec.add_neg_eq_sub]
  try simp [← BitVec.neg_mul]
  try simp [BitVec.not_and, BitVec.not_or, BitVec.not_not]


  try simp [t1]
  try simp [t2]
  try simp [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  try simp [r13, r14, r15, r16]


  try simp [BitVec.mul_add]


  try simp [← BitVec.add_assoc]

  try simp [← mul_swap] -/




  rw [t1]
  rw [r7]
  rw [BitVec.mul_add]
  simp [BitVec.not_or]
  simp only [BitVec.mul_comm]
  simp [BitVec.mul_comm 14#32]
  nth_rw 4 [BitVec.add_comm]
  nth_rw 1 [← BitVec.add_assoc]
  rw [← BitVec.mul_add]
  simp [BitVec.append]
  rw [BitVec.mul_comm 4#32]
  nth_rw 4 [BitVec.add_comm]
  nth_rw 1 [BitVec.add_comm]
  simp [←BitVec.add_assoc]
  rw [← BitVec.mul_add]
  simp [BitVec.append]
  rw [BitVec.add_comm ((~~~x &&& ~~~y) * 10#32) (8#32 * (~~~x &&& y))]
  rw [l10]
  rw [BitVec.mul_add]
  nth_rw 1 [← BitVec.add_assoc]
  rw [BitVec.mul_comm _ 8#32]
  rw [← BitVec.mul_add]
  rw [← r12]
  rw [← a1]
  rw [BitVec.mul_comm _ 2#32]
  simp [BitVec.add_comm]
  rw [← BitVec.add_assoc]
  rw [← BitVec.mul_add]
  rw [← r9]
  rw[← a2]



theorem mba_challenge_7b1a4532 (x y : BitVec 32) :
  ((((Int32.toBitVec (-1)) * (~~~(x &&& (~~~y)))) - ((Int32.toBitVec (3)) * (x ^^^ y))) + (Int32.toBitVec (4) * (~~~(x ||| (~~~y))))) = (((Int32.toBitVec (-1)) * (x ||| (~~~y))) - (Int32.toBitVec (2) * (x &&& (~~~y)))) := by

  try simp [BitVec.neg_mul]
  try simp [← BitVec.add_neg_eq_sub]
  try simp [← BitVec.neg_mul]

  try simp [BitVec.not_and, BitVec.not_or, BitVec.not_not]


  try simp [t1]
  try simp [t2]
  try simp [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  try simp [r13, r14, r15, r16]


  try simp [BitVec.mul_add]


  try simp [← BitVec.add_assoc]

  try simp [← mul_swap]













  nth_rw 1 [BitVec.add_comm]
  simp [← BitVec.add_assoc]
  nth_rw 2 [BitVec.add_comm]
  simp [← BitVec.add_assoc]
  nth_rw 4 [BitVec.add_comm]
  simp [← BitVec.add_assoc]
  simp [← BitVec.add_comm]
  nth_rw 1 [BitVec.add_comm]
  simp [← BitVec.add_assoc]
  try simp [← BitVec.mul_add]
  nth_rw 3 [BitVec.add_assoc]
  rw [BitVec.add_comm ((x &&& y) * 4294967295#32) ((~~~x &&& y) * 4294967295#32)]
  simp [← BitVec.add_assoc]
  nth_rw 1 [← BitVec.mul_one (~~~x &&& y)]
  rw [← BitVec.mul_add]
  simp [BitVec.append]
  nth_rw 3 [BitVec.add_assoc]
  rw [BitVec.add_comm ((x &&& y) * 4294967295#32) ((x &&& ~~~y) * 4294967295#32)]
  simp [← BitVec.add_assoc]
  rw [← BitVec.mul_add]
  rw [← BitVec.add_comm]
  simp [← BitVec.add_assoc]










theorem mba_challenge_34178047 (x y : BitVec 32) :
  ((((((Int32.toBitVec (-4)) * (x ||| y)) + ((Int32.toBitVec (4)) * (~~~(x &&& (~~~x))))) + ((Int32.toBitVec (8)) * (~~~(x &&& (~~~y))))) - ((Int32.toBitVec (12)) * (~~~(x ||| y)))) - ((Int32.toBitVec (8)) * (~~~(x ||| (~~~y))))) = ((Int32.toBitVec (8)) * (x &&& y)) := by


  try simp [BitVec.neg_mul]
  try simp [← BitVec.add_neg_eq_sub]
  try simp [← BitVec.neg_mul]
  try simp [BitVec.not_and, BitVec.not_or, BitVec.not_not]


  try simp [t1]
  try simp [t2]
  try simp [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  try simp [r13, r14, r15, r16]


  try simp [BitVec.mul_add]


  try simp [← BitVec.add_assoc]

  try simp [← mul_swap]

  nth_rw 2 [BitVec.add_assoc]

  simp [← BitVec.mul_add]

  nth_rw 2 [BitVec.add_assoc]

  rw [BitVec.add_comm ((~~~x &&& y) * 8#32) ((~~~x &&& ~~~y) * 4294967292#32)]
  try simp [← BitVec.add_assoc]
  nth_rw 1 [BitVec.add_assoc]
  simp [← BitVec.mul_add]
  try simp [mul_swap]
  nth_rw 2 [BitVec.add_assoc]
  rw [BitVec.add_comm]
  rw [← BitVec.mul_add]
  try simp [← BitVec.add_assoc]
  simp [← BitVec.mul_add]
  try simp [← BitVec.add_assoc]
  simp [all]
