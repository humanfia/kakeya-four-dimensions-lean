/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockModel.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockModel.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedRows

/-! Construct the normalized observation row from actual scalar-normal data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set
open scoped NNReal

namespace ScalarNormalHyp

theorem exists_normalized_observation_row {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : MeasureTheory.Measure Λ} {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d c H : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hH : 0 < H)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ H ^ 2) (hc : c ∈ scalarNormalTimes E) :
    ∃ g : ℝ → ℝ, LipschitzWith (⟨K, zero_le_one.trans hK⟩ : ℝ≥0) g ∧ g c = F c ∧
      (∀ t ∈ scalarNormalTimes E, |g t - F t| ≤ 2 * K * ζ) ∧
      (∀ u v, |(g (c + H * u) - F c) / H - (g (c + H * v) - F c) / H| ≤ K * |u - v|) ∧
      (∀ u, |u| ≤ 1 → |(g (c + H * u) - F c) / H| ≤ K) ∧
      ∀ base u l, |u| ≤ 1 → (l, c + H * u) ∈ E →
        |(D.scalar F l (c + H * u) - base) / H -
          ((D.scalar F l c - base) / H + u * D.residual F l c -
            ((g (c + H * u) - F c) / H) * D.y l c)| ≤ H * (K + 5 * K ^ 2) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  obtain ⟨g, hg, hgc, hnear, hnorm, hbound⟩ :=
    original_row_anchor_normalization hK0 hH hc h.active_row_comparison
  have hunit u (hu : |u| ≤ 1) : |(g (c + H * u) - F c) / H| ≤ K :=
    (hbound u).trans (by nlinarith)
  refine ⟨g, hg, hgc, hnear, hnorm, hunit, ?_⟩
  intro base u l hu hl
  have hcoeff := h.coefficients _ hl
  have hbounds := h.active_bounds hK hl
  have hmodel := original_quadratic_normalized_model_error
    (a₀ := D.x₀ l) (a₁ := D.x₁ l) (a₂ := D.x₂ l) (b₀ := D.y₀ l) (b₁ := D.y₁ l)
    (c := c) (base := base) hH hK0 hζ hζH hu hcoeff.2.2.1 hcoeff.2.2.2.2
    hbounds.2.1 (hunit u hu) (hnear _ ⟨l, hl⟩)
  simpa only [ScalarMotion.scalar, ScalarMotion.x, ScalarMotion.y, ScalarMotion.residual] using hmodel

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
