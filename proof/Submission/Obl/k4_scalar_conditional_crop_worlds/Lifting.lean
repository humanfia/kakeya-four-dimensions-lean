import Submission.Obl.k4_scalar_conditional_crop_worlds.Assembly
import Submission.Obl.k4_scalar_conditional_crop_worlds.Geometry

open MeasureTheory Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- The exact geometric lifting facts for any finite family of distinct scalar crops. -/
theorem liftFacts_conditional (N : ℕ → ℝ) (hN : ∀ k, 0 < N k) (u : ℝ) (W : ℕ → ℕ)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set State) (hν : ∀ k, SFinite (ν₀ k))
    (hE : ∀ k, MeasurableSet (E₀ k)) (z : (k : ℕ) → Fin (W k) → Label)
    (p : (k : ℕ) → Fin (W k) → ℝ) (hz : ∀ k, Function.Injective (z k))
    (hp : ∀ k γ, 0 < p k γ) :
    LiftFacts N u W ν₀ E₀
      (fun k γ => conditionalPrior (N k) u (ν₀ k) (z k γ) (p k γ))
      (fun k γ => conditionalEvent (N k) u (E₀ k) (z k γ)) p z := by
  refine ⟨fun k γ => measurableSet_scalarCell (N k) u (z k γ),
    fun k γ => measurable_scalarCropLine (N k) u (z k γ), ?_, ?_, ?_, ?_, ?_⟩
  · intro k γ γ' hγ
    exact scalarCell_disjoint (fun h => hγ (hz k h))
  · intro k γ Z hZ
    haveI := hν k
    exact selected_crop_eq (hN k) u (z k γ) (ν₀ k) (hE k) (hp k γ) hZ
  · intro k γ l hl t
    exact x_scalarCropLine (N k) u (z k γ) l t
  · intro k γ l hl t
    exact y_scalarCropLine (hN k) u (z k γ) l t
  · intro k γ l hl t ht
    exact abs_y_scalarCropLine_le hl ht

/-- The normalized restriction pushed through the scalar affine map is a probability prior. -/
lemma conditionalPrior_probability (N u : ℝ) (ν₀ : Measure Line) [IsProbabilityMeasure ν₀]
    (q : Label) {p : ℝ} (hp : 0 < p) (heq : p = priorMass N u ν₀ q) :
    IsProbabilityMeasure (conditionalPrior N u ν₀ q p) := by
  constructor
  change ((ENNReal.ofReal p)⁻¹ • Measure.map (scalarCropLine N u q)
    (ν₀.restrict (scalarCell N u q))) univ = 1
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_scalarCropLine N u q) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  have hreal : ENNReal.ofReal p = ν₀ (scalarCell N u q) := by
    rw [heq]
    exact ENNReal.ofReal_toReal (measure_ne_top ν₀ _)
  rw [← hreal]
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  exact ENNReal.inv_mul_cancel hp0 ENNReal.ofReal_ne_top

/-- The two normalized affine coefficients lie in `[0,1)`, and the other coefficients keep
the source bound. -/
lemma conditionalPrior_ae_bound (N u : ℝ) (ν₀ : Measure Line) (q : Label) (p : ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hν : ∀ᵐ l ∂ν₀, ∀ e, |l.2 e| ≤ R) :
    ∀ᵐ l ∂conditionalPrior N u ν₀ q p, ∀ e, |l.2 e| ≤ R := by
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_scalarCropLine N u q).aemeasurable (by measurability)).mpr
  filter_upwards [ae_restrict_of_ae hν, ae_restrict_mem (measurableSet_scalarCell N u q)] with l hl hc e
  obtain ⟨h0, h1⟩ := cropCoeff_mem_Ico hc
  fin_cases e
  · change |cropCoeff (N ^ (-u)) q l.2 0| ≤ R
    rw [abs_of_nonneg h0.1]
    exact h0.2.le.trans hR
  · change |cropCoeff (N ^ (-u)) q l.2 1| ≤ R
    rw [abs_of_nonneg h1.1]
    exact h1.2.le.trans hR
  · exact hl 2
  · exact hl 3
  · exact hl 4

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
