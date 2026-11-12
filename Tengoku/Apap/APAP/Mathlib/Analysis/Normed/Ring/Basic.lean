module

public import Tengoku

public section
namespace Tengoku.Apap end Tengoku.Apap open Tengoku.Apap 
variable {R : Type*} [SeminormedRing R] {a b c : R}

lemma Tengoku.Apap.norm_one_sub_mul (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  calc ‖c - a * b‖ = ‖(c - a) + a * (1 - b)‖ := by noncomm_ring
    _ ≤ ‖c - a‖ + ‖1 - b‖ := by grw [norm_add_le, norm_mul_le, ha, one_mul]

lemma Tengoku.Apap.norm_one_sub_mul' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ :=
  (norm_one_sub_mul (R := Rᵐᵒᵖ) hb).trans_eq (add_comm _ _)

lemma Tengoku.Apap.nnnorm_one_sub_mul (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ :=
  norm_one_sub_mul ha

lemma Tengoku.Apap.nnnorm_one_sub_mul' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ :=
  norm_one_sub_mul' hb
-- Tengoku: root names of this library moved to Tengoku.Apap so they do not collide with other libraries (generated)
