import Submission.Obl.k4_oss_dyadic_reduction.Basic

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_dyadic_reduction

noncomputable section

/-- Normalize a restricted measure and divide its coordinate by a signed scale. -/
def renorm (μ : Measure ℝ) (S : Set ℝ) (a : ℝ) : Measure ℝ :=
  (μ S)⁻¹ • (μ.restrict S).map (fun x => x / a)

lemma renorm_probability (μ : Measure ℝ) [IsFiniteMeasure μ] (S : Set ℝ)
    (a : ℝ) (hS : μ S ≠ 0) : IsProbabilityMeasure (renorm μ S a) := by
  constructor
  simp only [renorm, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (show Measurable (fun x : ℝ => x / a) by fun_prop)
      MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_cancel hS (measure_ne_top μ S)

lemma renorm_support (μ : Measure ℝ) (S : Set ℝ) (a : ℝ)
    (hs : ∀ x ∈ S, x / a ∈ Icc (1 : ℝ) 2) :
    renorm μ S a (Icc (1 : ℝ) 2)ᶜ = 0 := by
  rw [renorm, Measure.smul_apply,
    Measure.map_apply (by fun_prop) measurableSet_Icc.compl,
    Measure.restrict_apply (measurableSet_Icc.compl.preimage (by fun_prop))]
  have he : (fun x : ℝ => x / a) ⁻¹' (Icc (1 : ℝ) 2)ᶜ ∩ S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (hs x hx.2)
  simp only [he, measure_empty, smul_zero]

lemma restrict_eq_smul_map_renorm (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Set ℝ) (a : ℝ) (ha : a ≠ 0) (hS : μ S ≠ 0) :
    μ.restrict S = (μ S) • (renorm μ S a).map (fun x => a * x) := by
  rw [renorm, Measure.map_smul _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => a * x) ∘ (fun x => x / a) = id := by
    funext x
    dsimp
    field_simp
  rw [he, Measure.map_id, smul_smul,
    ENNReal.mul_inv_cancel hS (measure_ne_top μ S), one_smul]

/-- Rescaling a box factors the original masses out of its integral. -/
lemma integral_pi_restrict_rescale {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Fin n → Set ℝ) (a : Fin n → ℝ)
    (ha : ∀ j, a j ≠ 0) (hS : ∀ j, μ (S j) ≠ 0) (ξ : ℝ) :
    (∫ x, phase ξ x ∂Measure.pi (fun j => μ.restrict (S j))) =
      (∏ j, μ (S j)).toReal •
        ∫ x, phase (ξ * ∏ j, a j) x ∂Measure.pi (fun j => renorm μ (S j) (a j)) := by
  haveI (j : Fin n) : IsProbabilityMeasure (renorm μ (S j) (a j)) :=
    renorm_probability μ _ _ (hS j)
  have hμ : (fun j => μ.restrict (S j)) =
      (fun j => μ (S j) • (renorm μ (S j) (a j)).map (fun x => a j * x)) :=
    funext fun j => restrict_eq_smul_map_renorm μ _ _ (ha j) (hS j)
  rw [hμ, pi_smul _ _ (fun j => measure_ne_top μ (S j)), integral_smul_measure]
  congr 1
  rw [← Measure.pi_map_pi (fun j => (show Measurable (fun x : ℝ => a j * x) by
    fun_prop).aemeasurable), integral_map
      (show Measurable (fun x : Fin n → ℝ => fun j => a j * x j) by fun_prop).aemeasurable
      (continuous_phase ξ).aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (phase_mul a ξ)

lemma preimage_div_Icc_subset (a y u : ℝ) (ha : a ≠ 0) :
    (fun x : ℝ => x / a) ⁻¹' Icc (y - u) (y + u) ⊆
      Icc (a * y - |a| * u) (a * y + |a| * u) := by
  intro x hx
  have hxy : |x / a - y| ≤ u := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have he : x - a * y = a * (x / a - y) := by field_simp
  have h : |x - a * y| ≤ |a| * u := by
    rw [he, abs_mul]
    exact mul_le_mul_of_nonneg_left hxy (abs_nonneg a)
  have := abs_le.mp h
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma renorm_real_Icc_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Set ℝ) (a y u : ℝ) (ha : a ≠ 0) :
    (renorm μ S a).real (Icc (y - u) (y + u)) ≤
      (μ.real S)⁻¹ * μ.real (Icc (a * y - |a| * u) (a * y + |a| * u)) := by
  simp only [renorm, measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr measureReal_nonneg)
  rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Icc,
    Measure.restrict_apply (measurableSet_Icc.preimage (by fun_prop))]
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono
    (inter_subset_left.trans (preimage_div_Icc_subset a y u ha)))

def FrostmanCap (μ : Measure ℝ) (r s ε : ℝ) : Prop :=
  ∀ x u : ℝ, r ≤ u → u ≤ 1 →
    μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε) * u ^ s)

def UnitDecay (n : ℕ) (s ε τ δ₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ ν : Fin n → Measure ℝ,
    (∀ j, IsProbabilityMeasure (ν j)) →
    (∀ j, ν j (Icc (1 : ℝ) 2)ᶜ = 0) →
    (∀ j, FrostmanCap (ν j) δ s ε) →
    ∀ ξ : ℝ, δ⁻¹ ≤ |ξ| → |ξ| ≤ 2 * δ⁻¹ →
      ‖∫ x, phase ξ x ∂Measure.pi ν‖ ≤ δ ^ τ

lemma renorm_frostman (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Set ℝ) {r s ε₀ δ ε η a : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (hδ : 0 < δ) (hη : 0 < η)
    (ha : a ≠ 0) (ha1 : |a| ≤ 1) (hS : μ S ≠ 0)
    (hmass : η ≤ μ.real S) (hscale : r ≤ |a| * δ)
    (hcoef : η⁻¹ * r ^ (-ε₀) ≤ δ ^ (-ε))
    (hcap : FrostmanCap μ r s ε₀) : FrostmanCap (renorm μ S a) δ s ε := by
  haveI := renorm_probability μ S a hS
  intro y u hdu hu1
  have hu : 0 < u := lt_of_lt_of_le hδ hdu
  have hv0 : 0 ≤ |a| * u := mul_nonneg (abs_nonneg a) hu.le
  have hv : r ≤ |a| * u := hscale.trans (mul_le_mul_of_nonneg_left hdu (abs_nonneg a))
  have hvu : |a| * u ≤ u := mul_le_of_le_one_left hu.le ha1
  have hbound := hcap (a * y) (|a| * u) hv (hvu.trans hu1)
  have hreal : μ.real (Icc (a * y - |a| * u) (a * y + |a| * u)) ≤
      r ^ (-ε₀) * (|a| * u) ^ s :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  change (renorm μ S a).real _ ≤ _
  have hinv : (μ.real S)⁻¹ ≤ η⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hη hmass
  calc
    (renorm μ S a).real (Icc (y - u) (y + u)) ≤
        (μ.real S)⁻¹ * μ.real (Icc (a*y - |a| * u) (a*y + |a| * u)) :=
      renorm_real_Icc_le μ S a y u ha
    _ ≤ η⁻¹ * (r ^ (-ε₀) * (|a| * u) ^ s) := by
      exact mul_le_mul hinv hreal measureReal_nonneg (inv_nonneg.mpr hη.le)
    _ ≤ η⁻¹ * (r ^ (-ε₀) * u ^ s) := by
      gcongr
    _ = (η⁻¹ * r ^ (-ε₀)) * u ^ s := by ring
    _ ≤ δ ^ (-ε) * u ^ s := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu.le s)

lemma norm_heavy_box_le {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Fin n → Set ℝ) (a : Fin n → ℝ) {r s ε₀ δ ε τ δ₀ η A ξ : ℝ}
    (hcore : UnitDecay n s ε τ δ₀)
    (hr : 0 < r) (hs : 0 ≤ s) (hδ : 0 < δ) (hδ₀ : δ < δ₀) (hη : 0 < η)
    (ha : ∀ j, a j ≠ 0) (ha1 : ∀ j, |a j| ≤ 1)
    (hsupport : ∀ j x, x ∈ S j → x / a j ∈ Icc (1 : ℝ) 2)
    (hmass : ∀ j, η ≤ μ.real (S j)) (hscale : ∀ j, r ≤ |a j| * δ)
    (hcoef : η⁻¹ * r ^ (-ε₀) ≤ δ ^ (-ε))
    (hcap : FrostmanCap μ r s ε₀)
    (hξ1 : δ⁻¹ ≤ |ξ * ∏ j, a j|) (hξ2 : |ξ * ∏ j, a j| ≤ 2 * δ⁻¹)
    (hA : δ ^ τ ≤ A) :
    ‖∫ x, phase ξ x ∂Measure.pi (fun j => μ.restrict (S j))‖ ≤
      A * ∏ j, μ.real (S j) := by
  have hS (j : Fin n) : μ (S j) ≠ 0 := by
    intro hz
    have hm := hmass j
    simp only [measureReal_def, hz, ENNReal.toReal_zero] at hm
    linarith
  have h := hcore δ hδ hδ₀ (fun j => renorm μ (S j) (a j))
    (fun j => renorm_probability μ _ _ (hS j))
    (fun j => renorm_support μ _ _ (hsupport j))
    (fun j => renorm_frostman μ _ hr hs hδ hη (ha j) (ha1 j) (hS j)
      (hmass j) (hscale j) hcoef hcap) _ hξ1 hξ2
  rw [integral_pi_restrict_rescale μ S a ha hS ξ, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_prod]
  calc
    (∏ j, (μ (S j)).toReal) * ‖∫ x, phase (ξ * ∏ j, a j) x
        ∂Measure.pi (fun j => renorm μ (S j) (a j))‖ ≤
      (∏ j, (μ (S j)).toReal) * A := by
        exact mul_le_mul_of_nonneg_left (h.trans hA) (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    _ = A * ∏ j, μ.real (S j) := by rw [mul_comm]; rfl

end
end Submission.Obl.k4_oss_dyadic_reduction
