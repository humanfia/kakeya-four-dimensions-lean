import Submission.Lib.K4Homogenization.AngularCoarsening
import Submission.Lib.K4Homogenization.ObservationBounds
import Submission.Obl.k4_crop_angular_finite_tail.Transfer

namespace Submission.Obl.k4_remainder_angular_cap_transport
open MeasureTheory Set
open scoped ENNReal

/-- Restoring a discarded source law costs at most twice its mass in an upper density tail. -/
theorem upper_tail_of_split {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ good bad : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure X) [SigmaFinite ρ]
    (o : Ω → X) (ho : Measurable o) (G : X → ENNReal) (hG : Measurable G)
    (hlaw : μ.map o = ρ.withDensity G) (hsplit : μ = good + bad)
    (C : ENNReal) (hceil : good.map o ≤ C • ρ) :
    μ {p | 2 * C < G (o p)} ≤ 2 * bad univ := by
  have hg : good ≤ μ := by rw [hsplit]; exact le_add_of_nonneg_right bot_le
  have hb : bad ≤ μ := by rw [hsplit]; exact le_add_of_nonneg_left bot_le
  obtain ⟨g, hgm, hgl⟩ :=
    k4_crop_angular_finite_tail.exists_density_of_le ρ hg ho hlaw
  obtain ⟨b, hbm, hbl⟩ :=
    k4_crop_angular_finite_tail.exists_density_of_le ρ hb ho hlaw
  have hsum : μ.map o = ρ.withDensity (g + b) := by
    rw [hsplit, Measure.map_add _ _ ho, hgl, hbl, ← withDensity_add_left hgm b]
  have hgc : g ≤ᵐ[ρ] fun _ => C :=
    Submission.Lib.K4Homogenization.density_le_of_measure_bound ρ g hgm C (hgl ▸ hceil)
  calc
    _ = μ {p | 2 * C < g (o p) + b (o p)} := by
      exact Submission.Lib.K4Homogenization.observation_density_test_mass_eq
        μ ρ o ho hG (hgm.add hbm) hlaw hsum (fun _ z => 2 * C < z)
    _ ≤ 2 * ∫⁻ z, b z ∂ρ := by
      simpa only [Pi.add_apply, mul_one] using
        Submission.Lib.K4Homogenization.observation_upper_except_omitted
          μ ρ o ho (fun _ => 1) g b C measurable_const hgm hbm
          (by simpa only [mul_one] using hgc) hsum
    _ = 2 * bad univ := by
      congr 1
      rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hbl,
        Measure.map_apply ho MeasurableSet.univ, preimage_univ]


/-- Remove the upper density tail before transporting a source law. -/
theorem good_law_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ρ : Measure X) (o : Ω → X) (ho : Measurable o)
    (G : X → ENNReal) (hG : Measurable G) (hlaw : μ.map o = ρ.withDensity G)
    (C : ENNReal) :
    (μ.restrict {p | G (o p) ≤ C}).map o ≤ C • ρ := by
  have hS : MeasurableSet {z | G z ≤ C} := measurableSet_le hG measurable_const
  change (μ.restrict (o ⁻¹' {z | G z ≤ C})).map o ≤ _
  rw [← Measure.restrict_map ho hS, hlaw, restrict_withDensity hS,
    ← withDensity_indicator hS]
  calc
    _ ≤ ρ.withDensity (fun _ => C) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall fun z => by
        by_cases hz : G z ≤ C <;> simp [Set.indicator, hz]
    _ = _ := withDensity_const _


/-- A selected part of a normalized law inherits a ceiling away from the transported bad mass. -/
theorem pushforward_restriction_tail {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (ν : Measure Ω) (e : Ω → Ω') (he : Measurable e) (E : Set Ω')
    (μ : Measure Ω') [IsFiniteMeasure μ] (c : ENNReal)
    (hμ : μ = (c • ν.map e).restrict E)
    (ρ : Measure X) [SigmaFinite ρ] (o : Ω' → X) (ho : Measurable o)
    (G : X → ENNReal) (hG : Measurable G) (hlaw : μ.map o = ρ.withDensity G)
    (S : Set Ω) (hS : MeasurableSet S) (C : ENNReal)
    (hgood : ((ν.restrict S).map e).map o ≤ C • ρ) :
    μ {p | 2 * (c * C) < G (o p)} ≤ 2 * c * ν Sᶜ := by
  let good := (c • (ν.restrict S).map e).restrict E
  let bad := (c • (ν.restrict Sᶜ).map e).restrict E
  have hsplit : μ = good + bad := by
    have hm : (ν.restrict S).map e + (ν.restrict Sᶜ).map e = ν.map e := by
      rw [← Measure.map_add _ _ he, Measure.restrict_add_restrict_compl hS]
    rw [hμ, ← hm, smul_add, Measure.restrict_add]
  have hceil : good.map o ≤ (c * C) • ρ := by
    calc
      _ ≤ (c • (ν.restrict S).map e).map o :=
        Measure.map_mono Measure.restrict_le_self ho
      _ = c • ((ν.restrict S).map e).map o := Measure.map_smul c ho.aemeasurable
      _ ≤ c • (C • ρ) := by gcongr
      _ = _ := smul_smul c C ρ
  have hbad : bad univ ≤ c * ν Sᶜ := by
    calc
      _ ≤ (c • (ν.restrict Sᶜ).map e) univ := Measure.restrict_le_self univ
      _ = _ := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply he MeasurableSet.univ,
          preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  calc
    _ ≤ 2 * bad univ := upper_tail_of_split μ good bad ρ o ho G hG hlaw hsplit _ hceil
    _ ≤ 2 * (c * ν Sᶜ) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end Submission.Obl.k4_remainder_angular_cap_transport
