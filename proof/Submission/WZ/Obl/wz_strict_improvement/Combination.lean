-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.Combination.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_strict_improvement.Comparison

namespace WangZahlLot.Obl.wz_strict_improvement

/-- Choose the common gain and the density margin for the final alternative. -/
theorem improvement_parameters {σ ω α η₀ : ℝ}
    (hσ : 0 ≤ σ) (hω : 0 < ω) (hα : 0 < α) (hη₀ : 0 < η₀) :
    ∃ g η : ℝ, 0 < g ∧ g ≤ ω ∧ g ≤ α ∧ g ≤ ω / 4 ∧
      0 < η ∧ η ≤ η₀ ∧ η * σ ≤ ω / 4 := by
  let η := min η₀ (ω / (4 * (σ + 1)))
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨min α (ω / 4), η, lt_min hα (by positivity), ?_, min_le_left _ _,
    min_le_right _ _, hη, min_le_left _ _, ?_⟩
  · exact (min_le_right _ _).trans (by linarith)
  · have hsmall : η ≤ ω / (4 * (σ + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (σ + 1))).mp hsmall
    nlinarith

/-- Numerical last step: both the improved branch and a sticky volume bound imply
the same strict gain. This lemma assumes the analytic alternative explicitly. -/
theorem combine_volume_alternative
    {σ ω α g η a b ε δ : ℝ} {n : ℕ} {U : ENNReal}
    (hσ : 0 ≤ σ) (ha : 0 < a) (hb : 0 < b)
    (hgα : g ≤ α) (hgω : g ≤ ω / 4) (hησ : η * σ ≤ ω / 4)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hn : 0 < n)
    (hcard : δ ^ η ≤ 8 * ((n : ℝ) * δ))
    (hAlt : ENNReal.ofReal (DLower σ (ω - α) a 0 δ n) ≤ U ∨
      ENNReal.ofReal (b * δ ^ (ω / 2) * ((n : ℝ) * δ ^ 2)) ≤ U) :
    ENNReal.ofReal
      (DLower σ (ω - g) (min a (b * (8 : ℝ) ^ (-σ))) ε δ n) ≤ U := by
  rcases hAlt with himproved | hsticky
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) himproved
    exact (dLower_mono_coefficient n hδ.le (min_le_left _ _)).trans
      (dLower_mono_exponent n ha.le hδ hδ₁ (by linarith))
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hsticky
    apply (dLower_mono_coefficient n hδ.le (min_le_right _ _)).trans
    have h := dLower_mono_sigma (σ₁ := 0) (σ₂ := σ) (ω := ω / 2)
      (a := b) (ε₁ := 0) (ε₂ := ω / 2 - g + ε) hσ hb.le hδ hδ₁ hn hcard
      (by simp only [sub_zero, zero_add]; linarith)
    have hexp : ω / 2 + (ω / 2 - g + ε) = ω - g + ε := by ring
    simpa only [DLower, sub_zero, add_zero, neg_zero, Real.rpow_zero, mul_one, hexp] using h

end WangZahlLot.Obl.wz_strict_improvement
