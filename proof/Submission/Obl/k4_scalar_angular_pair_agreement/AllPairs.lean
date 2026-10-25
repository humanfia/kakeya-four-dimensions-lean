import Mathlib

/-!
# Two-time pair sets and the all-pairs lower bound

For one-time sets `D₁ D₂ ⊆ X × ℝ` the two-time set `pairSet D₁ D₂` consists of the
`(l, s, t)` with `(l, s) ∈ D₁` and `(l, t) ∈ D₂`.  Its `ν ⊗ vol ⊗ vol` measure is the
`ν`-integral of the product of the slice volumes.  For probability priors `ν_w`, weights
`ω_w` summing to one and `K` blocks with normalization `K`, the weighted pair mass of the
diagonal pair sets is at least the square of the weighted one-time mass (Cauchy–Schwarz,
in the form of the tangent-line inequality `2θx ≤ x² + θ²`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open scoped ENNReal

section PairSets

variable {X : Type*}

/-- The two-time set of a pair of one-time sets. -/
def pairSet (D₁ D₂ : Set (X × ℝ)) : Set (X × (ℝ × ℝ)) :=
  {z | (z.1, z.2.1) ∈ D₁ ∧ (z.1, z.2.2) ∈ D₂}

lemma measurableSet_pairSet [MeasurableSpace X] {D₁ D₂ : Set (X × ℝ)} (h1 : MeasurableSet D₁)
    (h2 : MeasurableSet D₂) : MeasurableSet (pairSet D₁ D₂) := by
  have m1 : Measurable (fun z : X × (ℝ × ℝ) => (z.1, z.2.1)) := by fun_prop
  have m2 : Measurable (fun z : X × (ℝ × ℝ) => (z.1, z.2.2)) := by fun_prop
  exact (h1.preimage m1).inter (h2.preimage m2)

lemma pairSet_mono {D₁ D₂ D₁' D₂' : Set (X × ℝ)} (h1 : D₁ ⊆ D₁') (h2 : D₂ ⊆ D₂') :
    pairSet D₁ D₂ ⊆ pairSet D₁' D₂' :=
  fun _ hz => ⟨h1 hz.1, h2 hz.2⟩

lemma preimage_pairSet (D₁ D₂ : Set (X × ℝ)) (l : X) :
    Prod.mk l ⁻¹' pairSet D₁ D₂ = (Prod.mk l ⁻¹' D₁) ×ˢ (Prod.mk l ⁻¹' D₂) := by
  ext st; simp [pairSet]

/-- The pair measure is the integral of the product of the slice volumes. -/
lemma pairSet_measure [MeasurableSpace X] (ν : Measure X) [SFinite ν] {D₁ D₂ : Set (X × ℝ)}
    (h1 : MeasurableSet D₁) (h2 : MeasurableSet D₂) :
    (ν.prod (volume.prod volume)) (pairSet D₁ D₂) =
      ∫⁻ l, volume (Prod.mk l ⁻¹' D₁) * volume (Prod.mk l ⁻¹' D₂) ∂ν := by
  rw [Measure.prod_apply (measurableSet_pairSet h1 h2)]
  refine lintegral_congr (fun l => ?_)
  rw [preimage_pairSet, Measure.prod_prod]

end PairSets

/-- The tangent-line inequality in `ℝ≥0∞`. -/
lemma two_mul_mul_le_sq_add_sq (a b : ℝ≥0∞) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [ENNReal.top_pow]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.top_pow]
  lift a to NNReal using ha
  lift b to NNReal using hb
  have : (2 : NNReal) * a * b ≤ a ^ 2 + b ^ 2 := by
    rw [← NNReal.coe_le_coe]; push_cast; nlinarith [sq_nonneg ((a : ℝ) - b)]
  exact_mod_cast this

section AllPairs

variable {X : Type*} [MeasurableSpace X]

/-- One block: `2θ (ν ⊗ vol) D ≤ (ν ⊗ vol ⊗ vol)(D ⋈ D) + θ²` for a probability measure. -/
lemma tangent_block (ν : Measure X) [IsProbabilityMeasure ν] {D : Set (X × ℝ)}
    (hD : MeasurableSet D) (θ : ℝ≥0∞) :
    2 * θ * (ν.prod volume) D ≤ (ν.prod (volume.prod volume)) (pairSet D D) + θ ^ 2 := by
  rw [pairSet_measure ν hD hD, Measure.prod_apply hD]
  have hmeas : Measurable (fun l => volume (Prod.mk l ⁻¹' D)) :=
    measurable_measure_prodMk_left hD
  calc 2 * θ * ∫⁻ l, volume (Prod.mk l ⁻¹' D) ∂ν
      = ∫⁻ l, 2 * θ * volume (Prod.mk l ⁻¹' D) ∂ν := (lintegral_const_mul _ hmeas).symm
    _ ≤ ∫⁻ l, (volume (Prod.mk l ⁻¹' D) * volume (Prod.mk l ⁻¹' D) + θ ^ 2) ∂ν := by
        apply lintegral_mono
        intro l
        have := two_mul_mul_le_sq_add_sq θ (volume (Prod.mk l ⁻¹' D))
        rw [sq] at this
        calc 2 * θ * volume (Prod.mk l ⁻¹' D) ≤ _ := this
          _ = _ := by ring
    _ = ∫⁻ l, volume (Prod.mk l ⁻¹' D) * volume (Prod.mk l ⁻¹' D) ∂ν + θ ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- The all-pairs lower bound: with probability priors, weights summing to one and `K`
blocks normalized by `K`, the weighted diagonal pair mass is at least the square of any
lower bound `m₀` of the weighted one-time mass. -/
theorem all_pairs_lower {W K : ℕ} (hK : 0 < K) (ω : Fin W → ℝ≥0∞) (hω : ∑ w, ω w = 1)
    (ν : Fin W → Measure X) [∀ w, IsProbabilityMeasure (ν w)]
    (D : Fin W → Fin K → Set (X × ℝ)) (hD : ∀ w b, MeasurableSet (D w b))
    {m₀ : ℝ≥0∞} (hm₀ : m₀ ≠ ⊤)
    (hmass : m₀ ≤ ∑ w, ∑ b, ω w * ((ν w).prod volume) (D w b)) :
    m₀ ^ 2 ≤ ∑ w, ∑ b, ω w * (K : ℝ≥0∞) *
      ((ν w).prod (volume.prod volume)) (pairSet (D w b) (D w b)) := by
  set κ : ℝ≥0∞ := (K : ℝ≥0∞) with hκ
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact_mod_cast hK.ne'
  have hκt : κ ≠ ⊤ := ENNReal.natCast_ne_top K
  set θ : ℝ≥0∞ := m₀ / κ with hθ
  have hθκ : θ * κ = m₀ := ENNReal.div_mul_cancel hκ0 hκt
  set P := ∑ w, ∑ b, ω w * κ * ((ν w).prod (volume.prod volume)) (pairSet (D w b) (D w b))
  -- sum the one-block inequalities with weights `ω w * κ`
  have hsum : ∑ w, ∑ b, ω w * κ * (2 * θ * ((ν w).prod volume) (D w b)) ≤
      ∑ w, ∑ b, ω w * κ * (((ν w).prod (volume.prod volume)) (pairSet (D w b) (D w b)) +
        θ ^ 2) := by
    gcongr with w _ b _
    exact tangent_block (ν w) (hD w b) θ
  have hleft : ∑ w, ∑ b, ω w * κ * (2 * θ * ((ν w).prod volume) (D w b)) =
      2 * (θ * κ) * ∑ w, ∑ b, ω w * ((ν w).prod volume) (D w b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hright : ∑ w, ∑ b, ω w * κ * (((ν w).prod (volume.prod volume))
      (pairSet (D w b) (D w b)) + θ ^ 2) = P + (θ * κ) ^ 2 := by
    have : ∑ w, ∑ b : Fin K, ω w * κ * θ ^ 2 = (θ * κ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ∀ x, (K : ℝ≥0∞) * (ω x * κ * θ ^ 2) = ω x * (κ * κ * θ ^ 2) := fun x => by
        rw [hκ]; ring
      simp_rw [this]
      rw [← Finset.sum_mul, hω, one_mul]; ring
    rw [← this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hleft, hright, hθκ] at hsum
  have h2 : 2 * m₀ * m₀ ≤ P + m₀ ^ 2 :=
    le_trans (by gcongr) hsum
  have hsq : m₀ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hm₀
  have h3 : m₀ ^ 2 + m₀ ^ 2 ≤ P + m₀ ^ 2 := by
    calc m₀ ^ 2 + m₀ ^ 2 = 2 * m₀ * m₀ := by ring
      _ ≤ P + m₀ ^ 2 := h2
  exact (ENNReal.add_le_add_iff_right hsq).mp h3

end AllPairs

end Submission.Obl.k4_scalar_angular_pair_agreement
