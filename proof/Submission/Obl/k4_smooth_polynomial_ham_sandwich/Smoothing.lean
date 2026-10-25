import Mathlib

namespace Submission.Obl.k4_smooth_polynomial_ham_sandwich

open MeasureTheory Filter Set
open scoped Topology

/-- The integral of a scaled arctangent tends to zero when both strict signs carry
at most half the mass and the zero set is null. The absolute integral tends to
`pi / 2` times the total mass. -/
theorem arctan_integral_limits {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hzero : μ {x | f x = 0} = 0)
    (hpos : 2 * μ {x | 0 < f x} ≤ μ univ)
    (hneg : 2 * μ {x | f x < 0} ≤ μ univ) :
    Tendsto (fun r : ℕ => ∫ x, Real.arctan ((r : ℝ) * f x) ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun r : ℕ => ∫ x, |Real.arctan ((r : ℝ) * f x)| ∂μ) atTop
      (𝓝 ((μ univ).toReal * (Real.pi / 2))) := by
  classical
  let A : Set α := {x | 0 < f x}
  let B : Set α := {x | f x < 0}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hz : ∀ᵐ x ∂μ, f x ≠ 0 := by simpa only [ae_iff, not_not] using hzero
  have hcompl : μ Aᶜ = μ B := by
    apply measure_congr
    filter_upwards [hz] with x hx
    apply propext
    simp only [A, B, mem_compl_iff, mem_ofPred_eq]
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) hx,
      fun h => not_lt_of_ge h.le⟩
  have hsum : (μ A).toReal + (μ B).toReal = (μ univ).toReal := by
    rw [← hcompl, ← ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ Aᶜ),
      measure_add_measure_compl hA]
  have hp : 2 * (μ A).toReal ≤ (μ univ).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top μ univ) hpos
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using this
  have hn : 2 * (μ B).toReal ≤ (μ univ).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top μ univ) hneg
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using this
  have hsame : (μ A).toReal = (μ B).toReal := by linarith
  let L : α → ℝ := A.piecewise (fun _ => Real.pi / 2) (fun _ => -(Real.pi / 2))
  have hLint : (∫ x, L x ∂μ) = 0 := by
    dsimp only [L]
    rw [integral_piecewise hA (integrable_const _).integrableOn
      (integrable_const _).integrableOn]
    simp only [setIntegral_const, smul_eq_mul, Measure.real, hcompl, hsame]
    ring
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun r : ℕ => Real.arctan ((r : ℝ) * f x)) atTop
      (𝓝 (L x)) := by
    filter_upwards [hz] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · have h := Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
      have hs : Tendsto (fun r : ℕ => (r : ℝ) * f x) atTop atBot :=
        tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hx
      have hc : Tendsto (fun r : ℕ => Real.arctan ((r : ℝ) * f x)) atTop
          (𝓝 (-(Real.pi / 2))) := h.comp hs
      simpa only [L, A, Set.piecewise, mem_ofPred_eq,
        ite_eq_right (not_lt_of_ge hx.le)] using hc
    · have h := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
      have hs : Tendsto (fun r : ℕ => (r : ℝ) * f x) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hx
      have hc : Tendsto (fun r : ℕ => Real.arctan ((r : ℝ) * f x)) atTop
          (𝓝 (Real.pi / 2)) := h.comp hs
      simpa only [L, A, Set.piecewise, mem_ofPred_eq, ite_eq_left hx] using hc
  have hmeas : ∀ r : ℕ, AEStronglyMeasurable
      (fun x => Real.arctan ((r : ℝ) * f x)) μ := fun r =>
    (Real.continuous_arctan.measurable.comp (measurable_const.mul hf)).aestronglyMeasurable
  have hbound : ∀ r : ℕ, ∀ᵐ x ∂μ, ‖Real.arctan ((r : ℝ) * f x)‖ ≤ Real.pi / 2 := by
    intro r
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  constructor
  · simpa only [hLint] using tendsto_integral_of_dominated_convergence
      (fun _ => Real.pi / 2) hmeas (integrable_const _) hbound hlim
  · have habslim : ∀ᵐ x ∂μ, Tendsto (fun r : ℕ => |Real.arctan ((r : ℝ) * f x)|)
        atTop (𝓝 (Real.pi / 2)) := by
      filter_upwards [hlim] with x hx
      have habs : |L x| = Real.pi / 2 := by
        dsimp only [L, Set.piecewise]
        split_ifs <;> simp [abs_of_nonneg Real.pi_div_two_pos.le]
      simpa only [habs] using hx.abs
    have habsbound : ∀ r : ℕ, ∀ᵐ x ∂μ,
        ‖|Real.arctan ((r : ℝ) * f x)|‖ ≤ Real.pi / 2 := by
      intro r
      simpa only [Real.norm_eq_abs, abs_abs] using hbound r
    have h := tendsto_integral_of_dominated_convergence (fun _ => Real.pi / 2)
      (fun r => (hmeas r).norm) (integrable_const _) habsbound habslim
    simpa only [integral_const, smul_eq_mul, Measure.real, Real.norm_eq_abs] using h

/-- One common scaling works for a finite list of finite positive measures. -/
theorem exists_arctan_scale {α : Type*} [MeasurableSpace α] {k : ℕ}
    (μ : Fin k → Measure α) [∀ i, IsFiniteMeasure (μ i)]
    (hμ : ∀ i, 0 < μ i univ) (f : α → ℝ) (hf : Measurable f)
    (hzero : ∀ i, μ i {x | f x = 0} = 0)
    (hbisect : ∀ i, 2 * μ i {x | 0 < f x} ≤ μ i univ ∧
      2 * μ i {x | f x < 0} ≤ μ i univ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i,
      |∫ x, Real.arctan (R * f x) ∂(μ i)| ≤ (μ i univ).toReal / 2 ∧
      (μ i univ).toReal ≤ ∫ x, |Real.arctan (R * f x)| ∂(μ i) := by
  have hevent : ∀ i, ∀ᶠ r : ℕ in atTop,
      |∫ x, Real.arctan ((r : ℝ) * f x) ∂(μ i)| ≤ (μ i univ).toReal / 2 ∧
      (μ i univ).toReal ≤ ∫ x, |Real.arctan ((r : ℝ) * f x)| ∂(μ i) := by
    intro i
    obtain ⟨hmean, habs⟩ := arctan_integral_limits (μ i) f hf (hzero i)
      (hbisect i).1 (hbisect i).2
    have hm : 0 < (μ i univ).toReal :=
      ENNReal.toReal_pos (ne_of_gt (hμ i)) (measure_ne_top _ _)
    have hpi : 1 < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hmarg : (μ i univ).toReal < (μ i univ).toReal * (Real.pi / 2) := by
      nlinarith
    have he1 := (show Tendsto
        (fun r : ℕ => |∫ x, Real.arctan ((r : ℝ) * f x) ∂(μ i)|) atTop (𝓝 0) from
        by simpa only [abs_zero] using hmean.abs).eventually_le_const (half_pos hm)
    have he2 := habs.eventually_const_lt hmarg
    filter_upwards [he1, he2] with r h1 h2
    exact ⟨h1, h2.le⟩
  have hall := Filter.eventually_all.mpr hevent
  obtain ⟨r, hr, hrall⟩ := ((eventually_ge_atTop 1).and hall).exists
  exact ⟨(r : ℝ), by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr), hrall⟩

end Submission.Obl.k4_smooth_polynomial_ham_sandwich
