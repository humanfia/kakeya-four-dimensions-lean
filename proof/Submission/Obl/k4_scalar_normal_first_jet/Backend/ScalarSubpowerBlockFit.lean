/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarSubpowerBlockFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarSubpowerBlockFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformBlockFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformLoss

/-! A single uniform subpower duration loss for all original scalar blocks. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts

def OriginalScalarBlockFitAt {d : ℝ} (Λ : Type*) [MeasurableSpace Λ] (K p duration : ℝ) : Prop :=
  ∀ (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ) (ζ H s : ℝ),
    ScalarNormalHyp D ν E F S K ζ d → 0 < ζ → 0 < H → H ≤ 1 → H ≤ p →
    ζ ≤ H ^ 2 → E ⊆ univ ×ˢ Icc s (s + H) → H / K ≤ (ν.prod volume).real E →
    ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc s (s + H) ∧
      T ⊆ scalarNormalTimes E ∧ ENNReal.ofReal (H * duration) ≤ volume T ∧
      |a| ≤ 80 * K ^ 2 ∧ |slope| ≤ 80 * K ^ 2 ∧
      ∀ t ∈ T, |F t - (a + slope * t)| ≤ 80 * K ^ 2 * H * p

theorem uniform_subpower_original_scalar_block_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {exponent d : ℝ} (hexponent : 0 < exponent) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, OriginalScalarBlockFitAt (d := d) Λ (K k) (N k ^ (-exponent)) (Q k)⁻¹ := by
  obtain ⟨τ, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun τ k => OriginalScalarBlockFitAt (d := d) Λ (K k) (N k ^ (-exponent)) (N k ^ (-τ)))
    (fun τ hτ => uniform_original_scalar_block_affine_fit N K hN hNt hK hsub hexponent hd0 hd hτ)
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-τ k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
