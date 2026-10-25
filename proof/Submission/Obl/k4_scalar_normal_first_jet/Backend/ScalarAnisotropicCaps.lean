/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAnisotropicCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAnisotropicCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBoxCaps
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Local scalar normalization of the original three-dimensional cube cap. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem interval_grid_cost_le {q W : ℝ} (hq : 0 < q) (hW : q ≤ W) :
    2 * W / q + 3 ≤ 5 * W / q := by
  have h : 1 ≤ W / q := (le_div_iff₀ hq).mpr (by simpa using hW)
  calc
    _ = 2 * (W / q) + 3 := by ring
    _ ≤ 5 * (W / q) := by linarith
    _ = _ := by ring

theorem original_normalized_scalar_cap_enlarged {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A E : Set Λ) (X : Λ → Fin 2 → ℝ)
    (a : Fin 2 → ℝ) {H r C d L : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hL : 1 ≤ L) (hr : 0 < r)
    (hC : 0 ≤ C) (hEA : E ⊆ A)
    (hbox : ∀ l ∈ E, X l 0 ∈ Icc (a 0) (a 0 + L * r) ∧
      X l 1 ∈ Icc (a 1) (a 1 + H * r))
    (hcap : ∀ b : Fin 2 → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (b i) (b i + H * r)} ≤ C * (H * r) ^ (1 + d)) :
    ν.real E / H ^ d ≤ 25 * L * C * r ^ (1 + d) := by
  have hq : 0 < H * r := mul_pos hH hr
  have hqr : H * r ≤ L * r := mul_le_mul_of_nonneg_right (hH1.trans hL) hr.le
  have hW : ∀ i : Fin 2, 0 ≤ (![L * r, H * r] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hb := original_rectangular_cap ν A E X a ![L * r, H * r] hq
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)) hW hEA (fun l hl i => by
      fin_cases i
      · exact (hbox l hl).1
      · exact (hbox l hl).2) hcap
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hb
  have hqfactor : 2 * (H * r) / (H * r) + 3 = 5 := by field_simp; ring
  rw [hqfactor] at hb
  have hprod := mul_le_mul_of_nonneg_right (interval_grid_cost_le hq hqr) (by norm_num : (0 : ℝ) ≤ 5)
  have hbound := hb.trans (mul_le_mul_of_nonneg_right hprod
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)))
  have hpow : (H * r) ^ (1 + d) = (H * r) * (H ^ d * r ^ d) := by
    rw [Real.rpow_add hq, Real.rpow_one, Real.mul_rpow hH.le hr.le]
  have hrpow : r ^ (1 + d) = r * r ^ d := by rw [Real.rpow_add hr, Real.rpow_one]
  have he : (5 * (L * r) / (H * r) * 5) * (C * (H * r) ^ (1 + d)) =
      H ^ d * (25 * L * C * r ^ (1 + d)) := by
    rw [hpow, hrpow]
    field_simp
    ring
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hH d)).mpr
  rw [he] at hbound
  simpa only [mul_comm] using hbound

theorem original_normalized_scalar_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A E : Set Λ) (X : Λ → Fin 2 → ℝ)
    (a : Fin 2 → ℝ) {H r C d : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hr : 0 < r)
    (hC : 0 ≤ C) (hEA : E ⊆ A)
    (hbox : ∀ l ∈ E, X l 0 ∈ Icc (a 0) (a 0 + r) ∧
      X l 1 ∈ Icc (a 1) (a 1 + H * r))
    (hcap : ∀ b : Fin 2 → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (b i) (b i + H * r)} ≤ C * (H * r) ^ (1 + d)) :
    ν.real E / H ^ d ≤ 25 * C * r ^ (1 + d) := by
  simpa only [one_mul, mul_one] using
    original_normalized_scalar_cap_enlarged ν A E X a hH hH1 (L := 1) (by norm_num) hr hC hEA
      (by simpa only [one_mul] using hbox) hcap

theorem original_normalized_sliced_cap_enlarged {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A E : Set Λ) (X : Λ → Fin 3 → ℝ)
    (a : Fin 3 → ℝ) {H p r C d L : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hL : 1 ≤ L) (hHp : H ≤ p) (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hEA : E ⊆ A)
    (hbox : ∀ l ∈ E, X l 0 ∈ Icc (a 0) (a 0 + L * r) ∧
      X l 1 ∈ Icc (a 1) (a 1 + L * p) ∧ X l 2 ∈ Icc (a 2) (a 2 + H * r))
    (hcap : ∀ b : Fin 3 → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (b i) (b i + H * r)} ≤ C * (H * r) ^ (2 + d)) :
    ν.real E / (H ^ d * p) ≤ 125 * L ^ 2 * C * r ^ (1 + d) := by
  have hp : 0 < p := hH.trans_le hHp
  have hq : 0 < H * r := mul_pos hH hr
  have hqr : H * r ≤ L * r := mul_le_mul_of_nonneg_right (hH1.trans hL) hr.le
  have hqp : H * r ≤ L * p := (mul_le_of_le_one_right hH.le hr1).trans
    (hHp.trans (by nlinarith : p ≤ L * p))
  have hW : ∀ i : Fin 3, 0 ≤ (![L * r, L * p, H * r] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hb := original_rectangular_cap ν A E X a ![L * r, L * p, H * r] hq
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)) hW hEA (fun l hl i => by
      fin_cases i
      · exact (hbox l hl).1
      · exact (hbox l hl).2.1
      · exact (hbox l hl).2.2) hcap
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hb
  have hqfactor : 2 * (H * r) / (H * r) + 3 = 5 := by field_simp; ring
  rw [hqfactor] at hb
  have hprod : (2 * (L * r) / (H * r) + 3) * ((2 * (L * p) / (H * r) + 3) * 5) ≤
      (5 * (L * r) / (H * r)) * ((5 * (L * p) / (H * r)) * 5) := by
    gcongr
    · exact interval_grid_cost_le hq hqr
    · exact interval_grid_cost_le hq hqp
  have hbound := hb.trans (mul_le_mul_of_nonneg_right hprod
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)))
  have hpow : (H * r) ^ (2 + d) = (H * r) ^ 2 * (H ^ d * r ^ d) := by
    rw [Real.rpow_add hq, Real.mul_rpow (z := d) hH.le hr.le]
    norm_num
  have hrpow : r ^ (1 + d) = r * r ^ d := by
    rw [Real.rpow_add hr, Real.rpow_one]
  have he : (5 * (L * r) / (H * r)) * ((5 * (L * p) / (H * r)) * 5) * (C * (H * r) ^ (2 + d)) =
      (H ^ d * p) * (125 * L ^ 2 * C * r ^ (1 + d)) := by
    rw [hpow, hrpow]
    field_simp
    ring
  apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hH d) hp)).mpr
  rw [he] at hbound
  simpa only [mul_comm] using hbound

theorem original_normalized_sliced_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A E : Set Λ) (X : Λ → Fin 3 → ℝ)
    (a : Fin 3 → ℝ) {H p r C d : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hHp : H ≤ p) (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hEA : E ⊆ A)
    (hbox : ∀ l ∈ E, X l 0 ∈ Icc (a 0) (a 0 + r) ∧
      X l 1 ∈ Icc (a 1) (a 1 + p) ∧ X l 2 ∈ Icc (a 2) (a 2 + H * r))
    (hcap : ∀ b : Fin 3 → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (b i) (b i + H * r)} ≤ C * (H * r) ^ (2 + d)) :
    ν.real E / (H ^ d * p) ≤ 125 * C * r ^ (1 + d) := by
  simpa only [one_mul, mul_one, one_pow] using
    original_normalized_sliced_cap_enlarged ν A E X a hH hH1 (L := 1) (by norm_num) hHp hr hr1 hC hEA
      (by simpa only [one_mul] using hbox) hcap

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
