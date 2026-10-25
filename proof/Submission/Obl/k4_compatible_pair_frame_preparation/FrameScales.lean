import Submission.Obl.k4_compatible_pair_frame_preparation.FrameInput

-- The lower-scale and dilation lemmas below are adapted from this LOT tree,
-- o206, session x0738, commit 8e9ffe1d,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Frame/Counts.lean.

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial
open Construction

namespace Construction.PrepData

variable {D : PrepData} {N : ℝ} {M₀ D₀ : ℕ} {L : ℝ}
    {E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}

theorem Hyp.R₂_le_S₂ (h : D.Hyp N M₀ D₀ L E) : D.R₂ ≤ D.S₂ := by
  unfold S₂
  have hs : (1 : ℝ) ≤ 2 ^ D.s := one_le_pow₀ (by norm_num)
  have hfit : D.R₂ ≤ fitR₂ (D.iso = true) D.R₁ D.R₂ := by
    unfold fitR₂
    split_ifs
    · exact h.R21
    · exact le_rfl
  have hm : D.R₂ ≤ max (fitR₂ (D.iso = true) D.R₁ D.R₂) (D.g * D.R₁) :=
    hfit.trans (le_max_left _ _)
  exact hm.trans (le_mul_of_one_le_left (h.R₂pos.le.trans hm) hs)

theorem Hyp.Afr_one (h : D.Hyp N M₀ D₀ L E) : 1 ≤ D.Afr := by
  unfold Afr
  linarith [h.κ₀one]

theorem Hyp.Afr_le (h : D.Hyp N M₀ D₀ L E) : D.Afr ≤ 626 * D.κ₀ := by
  unfold Afr
  linarith [h.κ₀one]

end Construction.PrepData

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

theorem narrow_scale_le (hN : 1 ≤ Nk) (ha : 0 ≤ a) :
    p.toPrep.S₂ ≤ 2 ^ p.s * (8 * Nk ^ a * p.R₂) := by
  have hNa : 1 ≤ Nk ^ a := Real.one_le_rpow hN ha
  have hR₁ : 0 < p.R₁ := p.hR₂pos.trans_le p.hR21
  change 2 ^ p.s * max (fitR₂ (decide (p.R₁ ≤ 8 * Nk ^ a * p.R₂) = true) p.R₁ p.R₂)
    (min (1 / 8) (Nk ^ a * p.R₂ / p.R₁) * p.R₁) ≤ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply max_le
  · by_cases hi : p.R₁ ≤ 8 * Nk ^ a * p.R₂
    · simpa only [fitR₂, decide_eq_true_eq, if_pos hi] using hi
    · simp only [fitR₂, decide_eq_true_eq, if_neg hi]
      nlinarith [p.hR₂pos]
  · have hm : min (1 / 8 : ℝ) (Nk ^ a * p.R₂ / p.R₁) * p.R₁ ≤ Nk ^ a * p.R₂ := by
      calc
        _ ≤ (Nk ^ a * p.R₂ / p.R₁) * p.R₁ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hR₁.le
        _ = _ := div_mul_cancel₀ _ hR₁.ne'
    nlinarith [p.hR₂pos]

/-- Native alignment bounds every frame determinant by the same scale product. -/
theorem determinant_le (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ) (ha : 0 ≤ a)
    (i : Fin p.toPrep.J) :
    |(p.toPrep.fQ i).det| ≤
      p.toPrep.Afr ^ 2 * ((2 : ℝ) ^ p.s) ^ 2 * (8 * Nk ^ a) * (p.R₁ * p.R₂) := by
  let hp := p.toPrep_hyp hN hB
  have hs := p.narrow_scale_le (by linarith) ha
  have hR₁ : 0 < p.R₁ := p.hR₂pos.trans_le p.hR21
  rw [(hp.frame_bounds i).2.2.2.1]
  calc
    p.toPrep.Afr * p.toPrep.S₁ * (p.toPrep.Afr * p.toPrep.S₂) =
        p.toPrep.Afr ^ 2 * (2 ^ p.s * p.R₁) * p.toPrep.S₂ := by
          change p.toPrep.Afr * (2 ^ p.s * p.R₁) * (p.toPrep.Afr * p.toPrep.S₂) = _
          ring
    _ ≤ p.toPrep.Afr ^ 2 * (2 ^ p.s * p.R₁) * (2 ^ p.s * (8 * Nk ^ a * p.R₂)) := by
      gcongr
    _ = _ := by ring

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
