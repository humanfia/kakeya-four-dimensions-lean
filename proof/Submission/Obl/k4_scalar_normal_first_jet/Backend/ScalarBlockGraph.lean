/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockGraph.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockGraph.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLipschitz
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry
import Mathlib.MeasureTheory.Function.Floor

/-! The residual graph in an actual original starting scalar bin. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

def scalarStartingLabels {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (c H : ℝ) (b : ℤ) : Set Λ :=
  {l | (l, c) ∈ E ∧ ⌊D.scalar F l c / H⌋ = b}

theorem scalarStartingLabels_measurable {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (F : ℝ → ℝ) (c H : ℝ) (b : ℤ) : MeasurableSet (scalarStartingLabels D E F c H b) :=
  (measurable_prodMk_right hE).inter (((D.measurable_at_scalar F c).div_const H).floor (MeasurableSet.singleton b))

theorem scalarStartingLabels_normalized_value {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (c : ℝ) {H : ℝ} (hH : 0 < H)
    (b : ℤ) {l : Λ} (hl : l ∈ scalarStartingLabels D E F c H b) :
    (D.scalar F l c - H * b) / H ∈ Icc (0 : ℝ) 1 := by
  have hz := (mesh_lower_endpoint hH hl.2).1
  exact ⟨div_nonneg (by linarith [hz.1]) hH.le,
    (div_le_iff₀ hH).mpr (by linarith [hz.2])⟩

namespace ScalarNormalHyp

theorem exists_starting_residual_graph {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {S : ℝ → Set ℝ} {K ζ d H : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H) (c : ℝ) (b : ℤ) :
    ∃ G : ℝ → ℝ, (∀ s t, |G s - G t| ≤ |s - t|) ∧
      (∀ l ∈ scalarStartingLabels D E F c H b,
        |D.residual F l c - G ((6 * K ^ 2) * D.y l c)| ≤ 12 * K ^ 2 * H) ∧
      ∀ l ∈ scalarStartingLabels D E F c H b, |G ((6 * K ^ 2) * D.y l c)| ≤ 16 * K ^ 2 := by
  let A := scalarStartingLabels D E F c H b
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hL : 0 < 6 * K ^ 2 := by positivity
  have hS : ∀ l ∈ A, ∀ l' ∈ A,
      |(D.x l c - F c * D.y l c - 0 * 0) - (D.x l' c - F c * D.y l' c - 0 * 0)| ≤ H := by
    intro l hl l' hl'
    have hh := same_mesh_cell_close hH (hl.2.trans hl'.2.symm)
    simpa only [ScalarMotion.scalar, zero_mul, sub_zero] using hh
  have hR : ∀ l ∈ A, ∀ l' ∈ A,
      |D.residual F l c - D.residual F l' c| ≤
        K * (|D.x l c - D.x l' c| + |D.y l c - D.y l' c| + |(0 : ℝ) - 0| + ζ) := by
    intro l hl l' hl'
    simpa only [sub_self, abs_zero, zero_add, add_zero] using
      h.residual_comparison (l, c) hl.1 (l', c) hl'.1
  have hcmp := scalar_frozen_residual_comparison A (fun l => D.x l c) (fun l => D.y l c)
    (fun _ => 0) (fun l => D.residual F l c) hK0 hH.le hζH (h.row_bounded c)
    (show |(0 : ℝ)| ≤ K by simpa using hK0) hS hR
  have hcmp' : ∀ l ∈ A, ∀ l' ∈ A,
      |D.residual F l c - D.residual F l' c| ≤
        (6 * K ^ 2) * |D.y l c - D.y l' c| + (6 * K ^ 2) * H := by
    intro l hl l' hl'
    have hh := hcmp l hl l' hl'
    simp only [sub_self, abs_zero, add_zero] at hh
    have hcoef : 2 * K + K ^ 2 ≤ 6 * K ^ 2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hcoef
      (add_nonneg (abs_nonneg (D.y l c - D.y l' c)) hH.le)
    nlinarith
  obtain ⟨G, hG, hnear⟩ := lipschitz_coordinate_factor_unit A (fun l => D.y l c)
    (fun l => D.residual F l c) hL hcmp'
  have hnear' : ∀ l ∈ A, |D.residual F l c - G ((6 * K ^ 2) * D.y l c)| ≤ 12 * K ^ 2 * H := by
    intro l hl
    have hh := hnear l hl
    linarith
  refine ⟨G, hG, hnear', ?_⟩
  intro l hl
  have hq := (h.active_bounds hK hl.1).2.2.1
  have hh := abs_sub_le (G ((6 * K ^ 2) * D.y l c)) (D.residual F l c) 0
  rw [sub_zero, sub_zero, abs_sub_comm (G ((6 * K ^ 2) * D.y l c)) (D.residual F l c)] at hh
  have hsmall := mul_le_mul_of_nonneg_left hH1 (show 0 ≤ 12 * K ^ 2 by positivity)
  linarith [hnear' l hl]

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
