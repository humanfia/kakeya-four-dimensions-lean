import Submission.Lib.K4ModelReduction.DensityOperations

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set
open scoped ENNReal

/-- Domination of incidence laws gives domination of their observed densities
at almost every retained incidence, for any measurable density versions. -/
theorem ae_observed_density_mono {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] (μ μ₀ : Measure Ω) (hμ : μ₀ ≤ μ)
    (obs : Ω → Y) (hobs : Measurable obs) (G G₀ : Y → ℝ≥0∞)
    (hG : Measurable G) (hG₀ : Measurable G₀)
    (hlaw : μ.map obs = ρ.withDensity G)
    (hlaw₀ : μ₀.map obs = ρ.withDensity G₀) :
    ∀ᵐ p ∂μ₀, G₀ (obs p) ≤ G (obs p) := by
  have hbase : G₀ ≤ᵐ[ρ] G := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hG₀
    intro S hS _
    rw [← withDensity_apply G₀ hS, ← withDensity_apply G hS, ← hlaw₀, ← hlaw]
    exact Measure.map_mono hμ hobs S
  have hmap : ∀ᵐ y ∂μ₀.map obs, G₀ y ≤ G y := by
    rw [hlaw₀]
    exact (withDensity_absolutelyContinuous ρ G₀).ae_le hbase
  exact (ae_map_iff hobs.aemeasurable (measurableSet_le hG₀ hG)).mp hmap

/-- A retained density loses a factor `ε` relative to the original density
on at most `ε` times the original total mass. -/
theorem observed_density_ratio_bound {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) (μ μ₀ : Measure Ω)
    (obs : Ω → Y) (hobs : Measurable obs) (G G₀ : Y → ℝ≥0∞)
    (hG : Measurable G) (hG₀ : Measurable G₀)
    (hlaw : μ.map obs = ρ.withDensity G)
    (hlaw₀ : μ₀.map obs = ρ.withDensity G₀) (ε : ℝ≥0∞) :
    μ₀ {p | G₀ (obs p) < ε * G (obs p)} ≤ ε * μ univ := by
  have hS : MeasurableSet {y | G₀ y < ε * G y} :=
    measurableSet_lt hG₀ (measurable_const.mul hG)
  have hmass : ∫⁻ y, G y ∂ρ = μ univ := by
    calc
      ∫⁻ y, G y ∂ρ = (ρ.withDensity G) univ := by
        simp only [withDensity_apply G MeasurableSet.univ, Measure.restrict_univ]
      _ = μ univ := by
        rw [← hlaw, Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  calc
    μ₀ {p | G₀ (obs p) < ε * G (obs p)} =
        (ρ.withDensity G₀) {y | G₀ y < ε * G y} := by
      rw [← hlaw₀, Measure.map_apply hobs hS]
      rfl
    _ ≤ ε * ∫⁻ y, G y ∂ρ :=
      Submission.Lib.K4ModelReduction.lower_density_ratio_mass_bound ρ G₀ G hG₀ hG ε
    _ = ε * μ univ := by rw [hmass]

/-- Transfer a density band to a dominated incidence law. The lower band
costs a factor `ε` and adds `ε` times the old mass to the exceptional mass. -/
theorem observed_density_band_bound {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] (μ μ₀ : Measure Ω) (hμ : μ₀ ≤ μ)
    (obs : Ω → Y) (hobs : Measurable obs) (G G₀ : Y → ℝ≥0∞)
    (hG : Measurable G) (hG₀ : Measurable G₀)
    (hlaw : μ.map obs = ρ.withDensity G)
    (hlaw₀ : μ₀.map obs = ρ.withDensity G₀)
    (B : Set Ω) (lower upper ε : ℝ≥0∞)
    (hband : ∀ᵐ p ∂μ₀, p ∉ B → lower ≤ G (obs p) ∧ G (obs p) ≤ upper) :
    μ₀ {p | G₀ (obs p) < ε * lower ∨ upper < G₀ (obs p)} ≤
      μ B + ε * μ univ := by
  have hmono := ae_observed_density_mono ρ μ μ₀ hμ obs hobs G G₀ hG hG₀ hlaw hlaw₀
  have hcover : {p | G₀ (obs p) < ε * lower ∨ upper < G₀ (obs p)} ≤ᵐ[μ₀]
      B ∪ {p | G₀ (obs p) < ε * G (obs p)} := by
    filter_upwards [hmono, hband] with p hp hband
    intro hbad
    by_cases hpB : p ∈ B
    · exact Or.inl hpB
    · apply Or.inr
      rcases hbad with hlo | hhi
      · exact hlo.trans_le (mul_le_mul_right (hband hpB).1 ε)
      · exact ((not_lt_of_ge ((hband hpB).2)) (hhi.trans_le hp)).elim
  calc
    _ ≤ μ₀ (B ∪ {p | G₀ (obs p) < ε * G (obs p)}) := measure_mono_ae hcover
    _ ≤ μ₀ B + μ₀ {p | G₀ (obs p) < ε * G (obs p)} := measure_union_le _ _
    _ ≤ μ B + ε * μ univ := add_le_add (hμ B)
      (observed_density_ratio_bound ρ μ μ₀ obs hobs G G₀ hG hG₀ hlaw hlaw₀ ε)

end Submission.Obl.k4_tempered_grid_selection
