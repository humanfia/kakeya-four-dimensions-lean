-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/UniformMatching.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/UniformMatching.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.ScaledMatching

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- A common component cap is dominated by the uniform index prior whenever the
component count times that cap fits the original packet budget. -/
theorem common_cap_uniform_prior {n : ℕ} (hn : 0 < n) {H budget : ℝ}
    (hcap : (n : ℝ) * H ≤ budget) :
    (∀ _i : Fin n, 0 ≤ (n : ℝ)⁻¹) ∧
    (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 ∧ H ≤ budget * (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun _ => inv_nonneg.mpr hnR.le, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hnR.ne'
  · rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hnR).mpr (by simpa only [mul_comm] using hcap)

/-- Local graph matching with a common base cap retains its original unequal component
weights. The uniform prior is used solely for marginal domination. -/
theorem common_cap_graph_bad_mass (h : localGraph) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
      ∀ (n : ℕ) (f : Fin n → RealSheet D) (f₀ : Real3 → ℂ)
        (μ : Measure ((Fin n × Fin n) × Real3)) (lam H : ℝ),
      0 < n → 0 < lam → (n : ℝ) ≤ R ^ (d₀ + ε) →
      (∀ i (x : Real3), ‖x‖ ≤ 1 → ‖(f i).f (emb x) - f₀ x‖ ≤ M * R ^ ε) →
      μ univ ≤ ENNReal.ofReal lam → (n : ℝ) * H ≤ lam * R ^ ε →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal H * volume U) →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal H * volume U) →
      μ (badPairs (fun i => (f i).f) (fun i => (f i).f) R M ε) ≤
        ENNReal.ofReal (lam * R ^ (-ε)) := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmatch⟩ := scaled_graph_bad_mass h D d₀ hd₀ hd₀1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεbound n f f₀ μ lam H hn hlam hcount hband hmass hcap hfirst hsecond
  obtain ⟨hπ, hπsum, hcommon⟩ := common_cap_uniform_prior hn hcap
  have hcommon' : H ≤ lam * (R ^ ε * (n : ℝ)⁻¹) := by
    simpa only [mul_assoc] using hcommon
  apply hmatch R M ε hR hM hε hεbound n f f₀ (fun _ => (n : ℝ)⁻¹) μ lam
    hlam hcount hband hπ hπsum hmass
  · intro i U hU
    exact (hfirst i U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcommon') le_rfl)
  · intro i U hU
    exact (hsecond i U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcommon') le_rfl)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
