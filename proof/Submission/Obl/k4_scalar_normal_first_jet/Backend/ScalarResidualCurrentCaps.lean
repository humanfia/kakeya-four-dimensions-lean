/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualCurrentCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualCurrentCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMovingGroupCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualObservations
import Mathlib.MeasureTheory.Function.Floor

/-! The residual kernel reads the current scalar cell under the original anchor group. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_left_residual_group_cap {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {F : ℝ → ℝ} (hF : Measurable F)
    (s : ℝ) (bin : ℤ) {H p K C d anchor : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hHp : H ≤ p)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, |D.y₁ q.1| ≤ K)
    (hcap : ∀ t a b : ℝ,
      ν.real {l | (l, t) ∈ E ∧ D.y l t ∈ Icc a (a + H * p) ∧
        D.scalar F l t ∈ Icc b (b + H * p)} ≤ C * (H * p) ^ (1 + d)) :
    let c := s + H * anchor
    let A := {l | (l, c) ∈ E ∧ (⌊D.scalar F l c / H⌋ : ℤ) = bin}
    let νb := scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
      (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
    ∀ u j z, νb.real {l | (l, u) ∈ scalarLeftBlockEvent E A s H ∧
      (⌊D.y l c / p⌋ : ℤ) = j ∧ (⌊scalarLeftObservation D F s H bin (u, l) / p⌋ : ℤ) = z} ≤
        25 * (1 + 2 * K) * C * p ^ (1 + d) := by
  dsimp only
  intro u j z
  let c := s + H * anchor
  let Aanchor : Set Λ := (fun l => (l, c)) ⁻¹' E
  let A : Set Λ := {l | (l, c) ∈ E ∧ (⌊D.scalar F l c / H⌋ : ℤ) = bin}
  let Q := scalarLeftBlockEvent E A s H
  let B : Set Λ := {l | (l, u) ∈ Q ∧ (⌊D.y l c / p⌋ : ℤ) = j ∧
    (⌊scalarLeftObservation D F s H bin (u, l) / p⌋ : ℤ) = z}
  have hAm : MeasurableSet A := (measurable_prodMk_right hE).inter
    (((D.measurable_at_scalar F c).div_const H).floor (MeasurableSet.singleton bin))
  have hQm := scalarLeftBlockEvent_measurable hE hAm s H
  have hBm : MeasurableSet B := (measurable_prodMk_right hQm).inter
    ((((D.measurable_at_y c).div_const p).floor (MeasurableSet.singleton j)).inter
      ((((scalarLeftObservation_measurable D hF s H bin).comp
        (measurable_const.prodMk measurable_id)).div_const p).floor (MeasurableSet.singleton z)))
  have hmove l (hl : l ∈ B) : |D.y l (s + H * u) - D.y l c| ≤ K * H := by
    have hu := (scalarLeftBlockEvent_unit hH hblock hl.1).2
    have hudiff : |u - anchor| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
    have hy₁ := hcoeff (l, s + H * u) hl.1.1
    have he : D.y l (s + H * u) - D.y l c = D.y₁ l * H * (u - anchor) := by
      dsimp [ScalarMotion.y, c]
      ring
    rw [he, abs_mul, abs_mul, abs_of_pos hH]
    simpa only [mul_one] using mul_le_mul
      (mul_le_mul_of_nonneg_right hy₁ hH.le) hudiff (abs_nonneg _) (mul_nonneg hK hH.le)
  have hY l (hl : l ∈ B) : D.y l c ∈ Icc (p * j) (p * j + p) :=
    (mesh_lower_endpoint hp hl.2.1).1
  have hZ l (hl : l ∈ B) :
      (D.scalar F l (s + H * u) - H * bin) / H ∈ Icc (p * z) (p * z + p) :=
    (mesh_lower_endpoint hp hl.2.2).1
  exact original_normalized_moving_group_joint_cap ν Aanchor
    {l | (l, s + H * u) ∈ E} B (fun l => D.y l c)
    (fun l => D.y l (s + H * u)) (fun l => D.scalar F l (s + H * u))
    (fun l => ⌊D.scalar F l c / H⌋) bin hBm (fun l hl => hl.1.2)
    (fun l hl => hl.1.1) hH hH1 hp hHp hK hC hmove hY hZ (hcap (s + H * u))

theorem original_residual_spatial_palette {Λ : Type*} (A : Set Λ) (Y : Λ → ℝ)
    {K p : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hp1 : p ≤ 1)
    (hY : ∀ l ∈ A, |Y l| ≤ 2 * K) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 7 * K * p ^ (-1 : ℝ) ∧
      ∀ l ∈ A, (⌊Y l / p⌋ : ℤ) ∈ J := by
  obtain ⟨J, hcard, hcover, _⟩ := bounded_scalar_grid_indices A Y (by positivity) hp hY
  refine ⟨J, hcard.trans ?_, hcover⟩
  rw [Real.rpow_neg_one]
  have he : 7 * K * p⁻¹ = 7 * K / p := by ring
  rw [he]
  apply (le_div_iff₀ hp).mpr
  have hmul : (2 * (2 * K) / p + 3) * p = 4 * K + 3 * p := by field_simp; ring
  rw [hmul]
  linarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
