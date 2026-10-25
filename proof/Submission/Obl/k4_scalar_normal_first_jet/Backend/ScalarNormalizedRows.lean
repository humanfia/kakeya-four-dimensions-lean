/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalizedRows.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalizedRows.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLipschitz
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalModel

/-! Normalize an active scalar row while preserving its original anchor. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set
open scoped NNReal

theorem original_row_anchor_normalization {U : Set ℝ} {F : ℝ → ℝ} {K ζ c H : ℝ}
    (hK : 0 ≤ K) (hH : 0 < H) (hc : c ∈ U)
    (hF : ∀ t ∈ U, ∀ s ∈ U, |F t - F s| ≤ K * (|t - s| + ζ)) :
    ∃ g : ℝ → ℝ, LipschitzWith (⟨K, hK⟩ : ℝ≥0) g ∧ g c = F c ∧
      (∀ t ∈ U, |g t - F t| ≤ 2 * K * ζ) ∧
      (∀ u v, |(g (c + H * u) - F c) / H - (g (c + H * v) - F c) / H| ≤ K * |u - v|) ∧
      ∀ u, |(g (c + H * u) - F c) / H| ≤ K * |u| := by
  have hcompare : ∀ t ∈ U, ∀ s ∈ U,
      |F t - F s| ≤ (⟨K, hK⟩ : ℝ≥0) * dist t s + K * ζ := by
    intro t ht s hs
    simpa only [Real.dist_eq, mul_add] using hF t ht s hs
  obtain ⟨g, hg, hgc, hnear⟩ := lipschitz_approx_preserving_anchor hc hcompare
  have hnorm u v : |(g (c + H * u) - F c) / H - (g (c + H * v) - F c) / H| ≤ K * |u - v| := by
    rw [← sub_div, abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    have h := hg.dist_le_mul (c + H * u) (c + H * v)
    change |g (c + H * u) - g (c + H * v)| ≤ K * |(c + H * u) - (c + H * v)| at h
    rw [show (c + H * u) - (c + H * v) = H * (u - v) by ring,
      abs_mul, abs_of_pos hH] at h
    simpa only [sub_sub_sub_cancel_right, mul_assoc, mul_comm, mul_left_comm] using h
  refine ⟨g, hg, hgc, (fun t ht => by simpa only [mul_assoc] using hnear t ht), hnorm, ?_⟩
  intro u
  have h := hnorm u 0
  simpa only [mul_zero, add_zero, hgc, sub_self, zero_div, sub_zero] using h

theorem original_quadratic_normalized_model_error
    {a₀ a₁ a₂ b₀ b₁ c H K ζ base u Fstar Fcur gcur : ℝ}
    (hH : 0 < H) (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hζH : ζ ≤ H ^ 2)
    (hu : |u| ≤ 1) (ha : |a₂| ≤ K) (hb : |b₁| ≤ K)
    (hy : |b₀ + b₁ * (c + H * u)| ≤ 2 * K)
    (hφ : |(gcur - Fstar) / H| ≤ K) (hrow : |gcur - Fcur| ≤ 2 * K * ζ) :
    |((a₀ + a₁ * (c + H * u) + a₂ * (c + H * u) ^ 2) -
        Fcur * (b₀ + b₁ * (c + H * u)) - base) / H -
      (((a₀ + a₁ * c + a₂ * c ^ 2 - Fstar * (b₀ + b₁ * c)) - base) / H +
        u * (a₁ + 2 * a₂ * c - Fstar * b₁) -
        ((gcur - Fstar) / H) * (b₀ + b₁ * c))| ≤ H * (K + 5 * K ^ 2) := by
  let Y := b₀ + b₁ * (c + H * u)
  have hperturb : |((gcur - Fcur) * Y) / H| ≤ 4 * K ^ 2 * H := by
    rw [abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    rw [abs_mul]
    have h := mul_le_mul hrow hy (abs_nonneg Y) (by positivity : 0 ≤ 2 * K * ζ)
    have h' := mul_le_mul_of_nonneg_left hζH (by positivity : 0 ≤ 4 * K ^ 2)
    nlinarith
  have hrem := quadratic_local_error hH.le hK hu ha hb hφ
  have hid := quadratic_local_identity a₀ a₁ a₂ b₀ b₁ c H Fstar base u gcur hH.ne'
  have he : ((a₀ + a₁ * (c + H * u) + a₂ * (c + H * u) ^ 2) -
        Fcur * (b₀ + b₁ * (c + H * u)) - base) / H -
      (((a₀ + a₁ * c + a₂ * c ^ 2 - Fstar * (b₀ + b₁ * c)) - base) / H +
        u * (a₁ + 2 * a₂ * c - Fstar * b₁) - ((gcur - Fstar) / H) * (b₀ + b₁ * c)) =
      H * (u ^ 2 * a₂ - u * ((gcur - Fstar) / H) * b₁) + ((gcur - Fcur) * Y) / H := by
    have hobs : ((a₀ + a₁ * (c + H * u) + a₂ * (c + H * u) ^ 2) -
        Fcur * (b₀ + b₁ * (c + H * u)) - base) / H =
      ((a₀ + a₁ * (c + H * u) + a₂ * (c + H * u) ^ 2) -
        gcur * (b₀ + b₁ * (c + H * u)) - base) / H + ((gcur - Fcur) * Y) / H := by
      dsimp [Y]
      ring
    rw [hobs, hid]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
