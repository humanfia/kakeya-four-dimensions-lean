/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockFirstJetCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockFirstJetCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockResidualWindows
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualWindowTransfer

/-! Original dense first-jet covers on one actual fitted scalar block. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarNormalHyp

theorem exists_original_block_first_jet_covers {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H s duration : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ)
    (hd0 : 0 ≤ d) (hd : d < 1) (hH : 0 < H) (hH1 : H ≤ 1)
    (hζHp : ζ ≤ H * H ^ (1 / 8 : ℝ)) (hduration : 0 ≤ duration)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E)
    (a slope : ℝ) (hslope : |slope| ≤ K)
    (hrow : ∀ q ∈ E, |F q.2 - (a + slope * q.2)| ≤ K * H * H ^ (1 / 8 : ℝ))
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 1) Λ ℤ (scalarBlockFitBound K)
      (H ^ (1 / 8 : ℝ)) duration) :
    ∃ A : Set Λ, MeasurableSet A ∧
      H * duration / (20000 * K ^ 6) ≤ (ν.prod volume).real (E ∩ (A ×ˢ univ)) ∧
      ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (scalarBlockFitBound K) ^ 2) ∧
          ∀ l ∈ A, ∀ t, (l, t) ∈ E →
            ∃ v ∈ L t ⌊D.scalar F l t / H⌋,
              |scalarFirstJet D F (fun _ => slope) l t - v| ≤ r := by
  have hp : 0 < H ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hH _
  have hp1 : H ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hH.le hH1 (by norm_num)
  have hHp : H ≤ H ^ (1 / 8 : ℝ) := Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)
  obtain ⟨anchor, center, A, hanchor, hAm, hA, hmassA, hwindow⟩ :=
    h.exists_original_block_residual_windows hK hζ hd.le hH hH1 hp hp1 hHp hζHp hduration
      hblock hmass a slope hslope hrow hconcentration
  refine ⟨A, hAm, hmassA, ?_⟩
  exact original_first_jet_covers_of_block_windows D E F s a slope A center hH hH1 hK
    (scalarBlockFitBound_bounds hK).1 (scalarBlockFitBound_residual_bounds hK).2.1
    hd0 hd hanchor h.unit_time hblock h.coefficients h.row_bounded hslope hrow hA hwindow

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
