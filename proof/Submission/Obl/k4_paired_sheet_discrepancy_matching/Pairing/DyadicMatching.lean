/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/DyadicMatching.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.GeometricDiscrepancy

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

theorem dyadic_ratio_rpow {M Δ : ℝ} (hM : 0 < M) (hΔ : 0 < Δ) (k : ℕ) (p : ℝ) :
    (M * 2 ^ k / (2 * Δ)) ^ p = (M / (2 * Δ)) ^ p * ((2 : ℝ) ^ p) ^ k := by
  rw [show M * 2 ^ k / (2 * Δ) = (M / (2 * Δ)) * 2 ^ k by ring,
    Real.mul_rpow (by positivity : 0 ≤ M / (2 * Δ)) (by positivity : 0 ≤ (2 : ℝ) ^ k)]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (k : ℝ) * p = p * k by ring, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
  (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ) (θ G : Λ → ℝ)

/-- The geometric discrepancy estimate requires numerical inequalities at only
the initial scale. The dyadic growth conditions then supply every later scale. -/
theorem discrepancy_mass_le_from_base {d₀ ε₀ R₀ ε χ d : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hχ : 0 < χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 < θ l) (hG : ∀ l, 0 ≤ G l)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (hρ : ∀ l, S.ρ l * (M₀ / (2 * S.Δ)) ^ (-ε) ≤ θ l / 2)
    (hρgrow : (2 : ℝ) ^ (-ε) ≤ χ)
    (hΓ : ∀ l, G l / θ l ≤ (M₀ / (2 * S.Δ)) ^ (d₀ + ε))
    (hΓgrow : (2 : ℝ) ^ d ≤ χ * (2 : ℝ) ^ (d₀ + ε))
    (hband : ∀ i k, S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
        ENNReal.ofReal (G (S.lab i) * ((2 : ℝ) ^ d) ^ k)) :
    S.Pm {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖} ≤
        ENNReal.ofReal (4 *
          (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
            (1 - χ) * ∑ i, θ (S.lab i)) := by
  apply discrepancy_mass_le_geometric J S M₀ θ hmb hR₀ hε hεε₀ hM₀ hχ hχ1 hθ hR hC
    (Γ := fun l k => G l * ((2 : ℝ) ^ d) ^ k)
  · intro l k
    rw [dyadic_ratio_rpow hM₀ S.Δ_pos]
    calc _ = (S.ρ l * (M₀ / (2 * S.Δ)) ^ (-ε)) * ((2 : ℝ) ^ (-ε)) ^ k := by ring
      _ ≤ (θ l / 2) * χ ^ k :=
        mul_le_mul (hρ l) (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hρgrow k)
          (by positivity) (div_nonneg (hθ l).le (by norm_num))
      _ = θ l * χ ^ k / 2 := by ring
  · intro l k
    rw [dyadic_ratio_rpow hM₀ S.Δ_pos]
    have hpow : ((2 : ℝ) ^ d) ^ k / χ ^ k ≤ ((2 : ℝ) ^ (d₀ + ε)) ^ k := by
      apply (div_le_iff₀ (pow_pos hχ k)).mpr
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) d) hΓgrow k
      simpa only [mul_pow, mul_comm] using hh
    calc _ = (G l / θ l) * (((2 : ℝ) ^ d) ^ k / χ ^ k) := by ring
      _ ≤ (M₀ / (2 * S.Δ)) ^ (d₀ + ε) * ((2 : ℝ) ^ (d₀ + ε)) ^ k :=
        mul_le_mul (hΓ l) hpow (by positivity)
          (Real.rpow_nonneg (by have := S.Δ_pos; positivity) _)
  · exact hband

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
