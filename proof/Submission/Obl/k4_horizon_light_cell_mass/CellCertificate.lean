import Submission.Obl.k4_native_base_flattening.Charge

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_base_flattening

/-- A cellwise constant approximation controls light cells of the original law.
No equality of the original and approximate cell masses is required. -/
theorem partition_light_mass_le {X C : Type*} [MeasurableSpace X] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C]
    (σ : Measure X) (g : X → ℝ≥0∞) (hg : Measurable g)
    (code : X → C) (hcode : Measurable code) (tab : C → ℝ≥0∞)
    (V θ : ℝ≥0∞) (ht : θ * V ≠ ∞)
    (hvol : ∀ c, σ (code ⁻¹' {c}) = V) :
    (σ.withDensity g) {x | (σ.withDensity g) (code ⁻¹' {code x}) < θ * V} ≤
      3 * (∫⁻ x, ediff (g x) (tab (code x)) ∂σ) +
        (σ.withDensity g) {x | g x < 4 * θ} := by
  classical
  let μ := σ.withDensity g
  let H : X → ℝ≥0∞ := tab ∘ code
  have hH : Measurable H := (measurable_of_countable tab).comp hcode
  let δ := σ.withDensity (fun x => ediff (g x) (H x))
  let Bad : Set C := {c | μ (code ⁻¹' {c}) < θ * V ∧ 2 * θ ≤ tab c}
  have hc (c : C) : MeasurableSet (code ⁻¹' {c}) := hcode (measurableSet_singleton c)
  have hbad (c : Bad) : μ (code ⁻¹' {c.val}) ≤ δ (code ⁻¹' {c.val}) := by
    have hcfin : μ (code ⁻¹' {c.val}) ≠ ∞ :=
      ne_of_lt (c.property.1.trans_le le_top)
    have hcomp : tab c.val * V ≤ μ (code ⁻¹' {c.val}) + δ (code ⁻¹' {c.val}) := by
      rw [show μ (code ⁻¹' {c.val}) = ∫⁻ x in code ⁻¹' {c.val}, g x ∂σ from
          withDensity_apply _ (hc _),
        show δ (code ⁻¹' {c.val}) = ∫⁻ x in code ⁻¹' {c.val}, ediff (g x) (H x) ∂σ from
          withDensity_apply _ (hc _)]
      rw [← lintegral_add_left hg]
      calc
        _ = ∫⁻ _x in code ⁻¹' {c.val}, tab c.val ∂σ := by
          rw [lintegral_const, Measure.restrict_apply_univ, hvol]
        _ ≤ ∫⁻ x in code ⁻¹' {c.val}, g x + ediff (g x) (H x) ∂σ := by
          apply setLIntegral_mono' (hc _)
          intro x hx
          have hx' : code x = c.val := hx
          change tab c.val ≤ g x + ediff (g x) (tab (code x))
          rw [hx']
          exact (le_add_tsub : tab c.val ≤ g x + (tab c.val - g x)).trans
            (add_le_add le_rfl le_add_self)
    have htwice : μ (code ⁻¹' {c.val}) + μ (code ⁻¹' {c.val}) ≤ tab c.val * V := by
      calc
        _ = 2 * μ (code ⁻¹' {c.val}) := (two_mul _).symm
        _ ≤ 2 * (θ * V) := mul_le_mul_right c.property.1.le _
        _ = (2 * θ) * V := (mul_assoc ..).symm
        _ ≤ _ := by gcongr; exact c.property.2
    apply ENNReal.le_of_add_le_add_right hcfin
    simpa only [add_comm] using htwice.trans hcomp
  have hbadTotal : μ (code ⁻¹' Bad) ≤ ∫⁻ x, ediff (g x) (H x) ∂σ := by
    calc
      _ = ∑' c : Bad, μ (code ⁻¹' {c.val}) :=
        (tsum_measure_preimage_singleton (to_countable Bad) (fun c _ => hc c)).symm
      _ ≤ ∑' c : Bad, δ (code ⁻¹' {c.val}) := ENNReal.tsum_le_tsum hbad
      _ = δ (code ⁻¹' Bad) :=
        tsum_measure_preimage_singleton (to_countable Bad) (fun c _ => hc c)
      _ ≤ δ univ := measure_mono (subset_univ _)
      _ = _ := by change σ.withDensity _ univ = _; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  let S : Set X := {x | H x < 2 * θ ∧ 4 * θ ≤ g x}
  have hS : MeasurableSet S :=
    (measurableSet_lt hH measurable_const).inter (measurableSet_le measurable_const hg)
  have hlow : μ S ≤ 2 * (∫⁻ x, ediff (g x) (H x) ∂σ) := by
    rw [show μ S = ∫⁻ x in S, g x ∂σ from withDensity_apply _ hS]
    calc
      _ ≤ ∫⁻ x in S, 2 * ediff (g x) (H x) ∂σ := by
        apply setLIntegral_mono' hS
        intro x hx
        have hhigh : 2 * H x < g x := by
          calc
            _ < 2 * (2 * θ) := by gcongr; norm_num; exact hx.1
            _ = 4 * θ := by ring
            _ ≤ _ := hx.2
        have hh := bad_pointwise_le (ε := 0) (Or.inr (Or.inl hhigh))
        simpa using hh
      _ ≤ ∫⁻ x, 2 * ediff (g x) (H x) ∂σ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := lintegral_const_mul _ (measurable_ediff hg hH)
  have hsubset : {x | μ (code ⁻¹' {code x}) < θ * V} ⊆
      (code ⁻¹' Bad ∪ S) ∪ {x | g x < 4 * θ} := by
    intro x hx
    by_cases hgx : g x < 4 * θ
    · exact Or.inr hgx
    · apply Or.inl
      by_cases hHx : 2 * θ ≤ H x
      · exact Or.inl ⟨hx, hHx⟩
      · exact Or.inr ⟨lt_of_not_ge hHx, le_of_not_gt hgx⟩
  calc
    _ ≤ μ ((code ⁻¹' Bad ∪ S) ∪ {x | g x < 4 * θ}) := measure_mono hsubset
    _ ≤ μ (code ⁻¹' Bad) + μ S + μ {x | g x < 4 * θ} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (∫⁻ x, ediff (g x) (H x) ∂σ) +
        2 * (∫⁻ x, ediff (g x) (H x) ∂σ) + μ {x | g x < 4 * θ} := by
      exact add_le_add (add_le_add hbadTotal hlow) le_rfl
    _ = _ := by dsimp only [H, μ, Function.comp_def]; ring

end Submission.Obl.k4_horizon_light_cell_mass
