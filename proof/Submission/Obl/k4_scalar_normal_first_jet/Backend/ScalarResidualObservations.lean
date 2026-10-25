/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualObservations.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualObservations.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualBlockModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockEvent

/-! Every original trajectory in a starting bin supplies the actual residual observations. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

noncomputable def scalarLeftObservation {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    (F : ℝ → ℝ) (s H : ℝ) (bin : ℤ) (q : ℝ × Λ) : ℝ :=
  (D.scalar F q.2 (s + H * q.1) - H * bin) / H

theorem scalarLeftObservation_measurable {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    {F : ℝ → ℝ} (hF : Measurable F) (s H : ℝ) (bin : ℤ) :
    Measurable (scalarLeftObservation D F s H bin) :=
  (((D.measurable_scalar hF).comp
    (measurable_snd.prodMk (measurable_const.add (measurable_const.mul measurable_fst)))).sub_const
      (H * bin)).div_const H

theorem original_left_residual_observations {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (s a slope : ℝ) (bin : ℤ)
    {H p K anchor : ℝ} (hH : 0 < H) (hHp : H ≤ p) (hp1 : p ≤ 1) (hK : 1 ≤ K)
    (hanchor : anchor ∈ Icc (0 : ℝ) 1) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, D.Bounded K q.1) (hF : ∀ t, |F t| ≤ K) (hslope : |slope| ≤ K)
    (hrow : ∀ q ∈ E, |F q.2 - (a + slope * q.2)| ≤ K * H * p) :
    let c := s + H * anchor
    let A := {l | (l, c) ∈ E ∧ (⌊D.scalar F l c / H⌋ : ℤ) = bin}
    let k := fun l => scalarFirstJet D F (fun _ => slope) l c
    let b := fun l => (D.scalar F l c - H * bin) / H - anchor * k l
    ∀ l u, (l, u) ∈ scalarLeftBlockEvent E A s H →
      |scalarLeftObservation D F s H bin (u, l)| ≤ 23 * K ^ 2 ∧
      |scalarLeftObservation D F s H bin (u, l) - (b l + k l * u)| ≤ 16 * K ^ 2 * p ∧
      |scalarFirstJet D F (fun _ => slope) l (s + H * u) - k l| ≤ 6 * K ^ 2 * H := by
  dsimp only
  intro l u hq
  let c := s + H * anchor
  let k := scalarFirstJet D F (fun _ => slope) l c
  let Z := (D.scalar F l c - H * bin) / H
  have hu : u ∈ Icc (0 : ℝ) 1 := (scalarLeftBlockEvent_unit hH hblock hq).2
  have hdata := original_left_block_residual_model D F l s a slope bin
    hH hHp hp1 hK hanchor hu (hcoeff (l, c) hq.2.1) (hunit hq.2.1).2
    (hF c) hslope (hrow (l, c) hq.2.1) (hrow (l, s + H * u) hq.1)
  have hk : |k| ≤ 6 * K ^ 2 := hdata.2.2
  have hZ : |Z| ≤ 1 := by
    have hh := (mesh_lower_endpoint hH hq.2.2).2
    dsimp only [Z]
    rw [abs_div, abs_of_pos hH]
    exact (div_le_iff₀ hH).mpr (by simpa only [one_mul] using hh.le)
  have huc : |u - anchor| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
  have hproduct : |(u - anchor) * k| ≤ 6 * K ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul huc hk (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hlinear : |Z + (u - anchor) * k| ≤ 1 + 6 * K ^ 2 :=
    (abs_add_le _ _).trans (add_le_add hZ hproduct)
  have hmodel : |scalarLeftObservation D F s H bin (u, l) - (Z + (u - anchor) * k)| ≤ 16 * K ^ 2 * p := by
    convert hdata.1 using 1 <;> dsimp [scalarLeftObservation, Z, k, c, scalarFirstJet] <;> congr 1 <;> ring
  have hbound : |scalarLeftObservation D F s H bin (u, l)| ≤ 23 * K ^ 2 := by
    have hh := abs_sub_le (scalarLeftObservation D F s H bin (u, l)) (Z + (u - anchor) * k) 0
    simp only [sub_zero] at hh
    have hpK := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 16 * K ^ 2 by positivity)
    nlinarith [show 1 ≤ K ^ 2 by nlinarith [hK]]
  refine ⟨hbound, ?_, hdata.2.1⟩
  convert hmodel using 1 <;> dsimp [Z, k, c] <;> congr 1 <;> ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
