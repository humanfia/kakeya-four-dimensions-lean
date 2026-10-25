-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/ScaledMatching.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ScaledMatching.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Directional

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- Undoing a deterministic positive rescaling preserves an unnormalized event bound. -/
theorem measure_le_of_rescaled {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) {lam : ℝ} (hlam : 0 < lam) (A : ENNReal)
    (h : (ENNReal.ofReal lam⁻¹ • μ) S ≤ A) : μ S ≤ ENNReal.ofReal lam * A := by
  have hi : ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne']
    norm_num
  calc
    μ S = ENNReal.ofReal lam * (ENNReal.ofReal lam⁻¹ * μ S) := by rw [← mul_assoc, hi, one_mul]
    _ ≤ ENNReal.ofReal lam * A := by
      have hh : ENNReal.ofReal lam⁻¹ * μ S ≤ A := h
      gcongr

/-- Group-wise matching bounds are proportional to the original group scale. They can
therefore be summed using the original packet weights instead of the polynomial packet count. -/
theorem scaled_graph_bad_mass (h : localGraph) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
      ∀ (n : ℕ) (f : Fin n → RealSheet D) (f₀ : Real3 → ℂ) (π : Fin n → ℝ)
        (μ : Measure ((Fin n × Fin n) × Real3)) (lam : ℝ),
      0 < lam → (n : ℝ) ≤ R ^ (d₀ + ε) →
      (∀ i (x : Real3), ‖x‖ ≤ 1 → ‖(f i).f (emb x) - f₀ x‖ ≤ M * R ^ ε) →
      (∀ i, 0 ≤ π i) → (∑ i, π i) = 1 → μ univ ≤ ENNReal.ofReal lam →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (lam * (R ^ ε * π i)) * volume U) →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (lam * (R ^ ε * π i)) * volume U) →
      μ (badPairs (fun i => (f i).f) (fun i => (f i).f) R M ε) ≤
        ENNReal.ofReal (lam * R ^ (-ε)) := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hbound⟩ := graph_bad_mass h D d₀ hd₀ hd₀1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hε₀ n f f₀ π μ lam hlam hn hf hπ hπsum hμ hμ₁ hμ₂
  let ν := ENNReal.ofReal lam⁻¹ • μ
  have hν : ν univ ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam := by
        change ENNReal.ofReal lam⁻¹ * μ univ ≤ _
        gcongr
      _ = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le), inv_mul_cancel₀ hlam.ne']
        norm_num
  have hfam : SheetFamily D n R M ε f₀ (fun i => (f i).f) (fun i => (f i).P) := by
    intro i
    exact ⟨(f i).nonzero, (f i).degree, (f i).holomorphic, (f i).equation,
      fun x hx => ⟨(f i).real_on_real x hx, hf i x hx⟩⟩
  have hscale (i : Fin n) : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (lam * (R ^ ε * π i)) =
      ENNReal.ofReal (R ^ ε * π i) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le)]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
  have hν₁ i (U : Set Real3) (hU : MeasurableSet U) :
      ν {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π i) * volume U := by
    calc
      _ ≤ ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (lam * (R ^ ε * π i)) * volume U) := by
        change ENNReal.ofReal lam⁻¹ * μ _ ≤ _
        gcongr
        exact hμ₁ i U hU
      _ = _ := by rw [← mul_assoc, hscale]
  have hν₂ i (U : Set Real3) (hU : MeasurableSet U) :
      ν {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π i) * volume U := by
    calc
      _ ≤ ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (lam * (R ^ ε * π i)) * volume U) := by
        change ENNReal.ofReal lam⁻¹ * μ _ ≤ _
        gcongr
        exact hμ₂ i U hU
      _ = _ := by rw [← mul_assoc, hscale]
  have hb := hbound R M ε hR hM hε hε₀ n n (fun i => (f i).f) (fun i => (f i).f)
    (fun i => (f i).P) (fun i => (f i).P) f₀ π π ν hn hn hfam hfam hπ hπ hπsum hπsum
    hν hν₁ hν₂
  calc
    _ ≤ ENNReal.ofReal lam * ENNReal.ofReal (R ^ (-ε)) :=
      measure_le_of_rescaled μ _ hlam _ hb.le
    _ = _ := (ENNReal.ofReal_mul hlam.le).symm

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
