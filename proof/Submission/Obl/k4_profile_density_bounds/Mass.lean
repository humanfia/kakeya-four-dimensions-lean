import Submission.Obl.k4_profile_density_bounds.Common

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_profile_density_bounds

lemma mass_le_density_times_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ρ : Measure Y) {f : X → Y} (hf : Measurable f)
    {G : Y → ENNReal} (hG : Measurable G) (hlaw : μ.map f = ρ.withDensity G)
    {S : Set Y} (hS : MeasurableSet S) (hsupp : ∀ᵐ p ∂μ, f p ∈ S) (b : ENNReal) :
    μ univ ≤ b * ρ S + μ {p | b < G (f p)} := by
  let A : Set Y := S ∩ {x | G x ≤ b}
  have hA : MeasurableSet A := hS.inter (measurableSet_le hG measurable_const)
  have hgood : μ {p | G (f p) ≤ b} ≤ b * ρ S := by
    calc
      μ {p | G (f p) ≤ b} ≤ μ (f ⁻¹' A) := by
        apply measure_mono_ae
        filter_upwards [hsupp] with p hp hg
        exact ⟨hp, hg⟩
      _ = (ρ.withDensity G) A := by rw [← hlaw, Measure.map_apply hf hA]
      _ = ∫⁻ x in A, G x ∂ρ := withDensity_apply _ hA
      _ ≤ ∫⁻ x in A, b ∂ρ := setLIntegral_mono measurable_const fun x hx => hx.2
      _ = b * ρ A := setLIntegral_const _ _
      _ ≤ b * ρ S := by gcongr; exact inter_subset_left
  have htotal := measure_univ_le_add_compl (μ := μ) {p | G (f p) ≤ b}
  simp only [compl_setOf, not_le] at htotal
  exact htotal.trans (add_le_add hgood le_rfl)

lemma measurableSet_reference_project {H : Set Observation} (hH : MeasurableSet H) :
    MeasurableSet {x : Base | ∃ j : ℤ, ∃ v : Fin 2 → ℤ, ((x, j), v) ∈ H} := by
  have heq : {x : Base | ∃ j : ℤ, ∃ v : Fin 2 → ℤ, ((x, j), v) ∈ H} =
      ⋃ j : ℤ, ⋃ v : Fin 2 → ℤ, (fun x : Base => ((x, j), v)) ⁻¹' H := by ext x; simp
  rw [heq]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun v =>
    hH.preimage ((measurable_id.prodMk measurable_const).prodMk measurable_const)

lemma reference_high_density_le {μ : Measure State} {f : State → Observation}
    (hf : Measurable f) {G : Observation → ENNReal} (hG : Measurable G)
    (hlaw : μ.map f = reference.withDensity G) (hmass : μ univ ≤ 1)
    {b : ℝ} (hb : 0 < b) :
    reference {x | ENNReal.ofReal b ≤ G x} ≤ ENNReal.ofReal b⁻¹ := by
  have hint : (∫⁻ x, G x ∂reference) ≤ 1 := by
    calc
      _ = (reference.withDensity G) univ := by
        simpa only [Measure.restrict_univ] using (withDensity_apply G MeasurableSet.univ).symm
      _ = μ univ := by rw [← hlaw, Measure.map_apply hf MeasurableSet.univ, preimage_univ]
      _ ≤ 1 := hmass
  have h := (mul_meas_ge_le_lintegral hG (ENNReal.ofReal b)).trans hint
  rw [ENNReal.ofReal_inv_of_pos hb]
  exact ENNReal.le_inv_iff_mul_le.2 (by simpa [mul_comm] using h)

lemma ae_density_le_of_measure_bound {Y : Type*} [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] {G : Y → ENNReal} (hG : Measurable G)
    (c : ENNReal)
    (hbound : ∀ S : Set Y, MeasurableSet S → (ρ.withDensity G) S ≤ c * ρ S) :
    ∀ᵐ y ∂ρ, G y ≤ c := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hG
  intro S hS _
  calc
    ∫⁻ y in S, G y ∂ρ = (ρ.withDensity G) S := (withDensity_apply _ hS).symm
    _ ≤ c * ρ S := hbound S hS
    _ = ∫⁻ y in S, c ∂ρ := (setLIntegral_const _ _).symm

lemma ae_observed_density_le_of_measure_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ρ : Measure Y) [SigmaFinite ρ]
    {f : X → Y} (hf : Measurable f) {G : Y → ENNReal} (hG : Measurable G)
    (hlaw : μ.map f = ρ.withDensity G) (c : ENNReal)
    (hbound : ∀ S : Set Y, MeasurableSet S → (μ.map f) S ≤ c * ρ S) :
    ∀ᵐ p ∂μ, G (f p) ≤ c := by
  have hbase : ∀ᵐ y ∂ρ, G y ≤ c := ae_density_le_of_measure_bound ρ hG c (by
    intro S hS
    rw [← hlaw]
    exact hbound S hS)
  have hmap : ∀ᵐ y ∂μ.map f, G y ≤ c := by
    rw [hlaw]
    exact (withDensity_absolutelyContinuous ρ G).ae_le hbase
  exact (ae_map_iff hf.aemeasurable (measurableSet_le hG measurable_const)).mp hmap

end Submission.Obl.k4_profile_density_bounds
