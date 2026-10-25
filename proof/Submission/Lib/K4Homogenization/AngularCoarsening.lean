/-
Adapted from: here:o018
-/
import Submission.Lib.K4Homogenization.DensityOperations

/-! Angular upper bounds under deterministic coarsening of the pure observation.
The estimates concern the sampled angular entry and charge omitted mass explicitly. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

/-- A joint-law ceiling relative to its pure law survives every measurable coarsening
of that pure observation. -/
theorem coarsened_joint_measure_le {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    (ν : Measure X) [SFinite ν] (κ : Measure I) [SFinite κ]
    (ξ : Measure (X × I)) (c : ℝ≥0∞) (hξ : ξ ≤ c • ν.prod κ)
    (q : X → Y) (hq : Measurable q) :
    ξ.map (Prod.map q id) ≤ c • (ν.map q).prod κ := by
  calc
    _ ≤ (c • ν.prod κ).map (Prod.map q id) :=
      Measure.map_mono hξ (hq.prodMap measurable_id)
    _ = c • (ν.prod κ).map (Prod.map q id) :=
      Measure.map_smul c (hq.prodMap measurable_id).aemeasurable
    _ = _ := by rw [← Measure.map_prod_map ν κ hq measurable_id, Measure.map_id]

/-- The measure comparison directly on incidence observations, before choosing any RN
densities. The good source and the pure denominator may use different measures. -/
theorem coarsened_observation_measure_le {Ω X Y I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    (ν ξ : Measure Ω) [SFinite ν] (κ : Measure I) [SFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (q : X → Y) (hq : Measurable q) (c : ℝ≥0∞)
    (hgood : ξ.map (fun p => (obs p, ang p)) ≤ c • (ν.map obs).prod κ) :
    ξ.map (fun p => (q (obs p), ang p)) ≤ c • (ν.map (q ∘ obs)).prod κ := by
  have h := coarsened_joint_measure_le (ν.map obs) κ
    (ξ.map (fun p => (obs p, ang p))) c hgood q hq
  rw [Measure.map_map (hq.prodMap measurable_id) (hobs.prodMk hang),
    Measure.map_map hq hobs] at h
  exact h

/-- In densities, the same ceiling is relative to the coarse pure density. -/
theorem coarsened_joint_density_le {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    (ν : Measure X) [SFinite ν] (κ : Measure I) [SigmaFinite κ]
    (ξ : Measure (X × I)) (c : ℝ≥0∞) (hξ : ξ ≤ c • ν.prod κ)
    (q : X → Y) (hq : Measurable q) (μ : Measure Y) [SigmaFinite μ]
    (f : Y → ℝ≥0∞) (hf : Measurable f) (hpure : ν.map q = μ.withDensity f)
    (g : Y × I → ℝ≥0∞) (hg : Measurable g)
    (hjoint : ξ.map (Prod.map q id) = (μ.prod κ).withDensity g) :
    g ≤ᵐ[μ.prod κ] fun p => c * f p.1 := by
  have hmeasure := coarsened_joint_measure_le ν κ ξ c hξ q hq
  rw [hjoint, hpure, prod_withDensity_left hf] at hmeasure
  have hscaled : c • (μ.prod κ).withDensity (fun p : Y × I => f p.1) =
      (μ.prod κ).withDensity (fun p => c * f p.1) := by
    have heq : (c • fun p : Y × I => f p.1) = fun p => c * f p.1 := by
      funext p
      exact smul_eq_mul _ _
    calc
      _ = (μ.prod κ).withDensity (c • fun p : Y × I => f p.1) :=
        (withDensity_smul (μ := μ.prod κ) (f := fun p : Y × I => f p.1)
          c (hf.comp measurable_fst)).symm
      _ = _ := congrArg (μ.prod κ).withDensity heq
  rw [hscaled] at hmeasure
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg
  intro A hA _
  rw [← withDensity_apply _ hA, ← withDensity_apply _ hA]
  exact hmeasure A

/-- Restoring an omitted part spoils a factor-two density ceiling on at most twice
the omitted mass. The ceiling need only hold almost everywhere for the good part. -/
theorem density_upper_except_omitted {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f good bad : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable good) (hb : Measurable bad)
    (hgood : good ≤ᵐ[μ] fun x => c * f x) :
    (∫⁻ x in {x | 2 * c * f x < good x + bad x}, good x + bad x ∂μ) ≤
      2 * ∫⁻ x, bad x ∂μ := by
  have hA : MeasurableSet {x | 2 * c * f x < good x + bad x} :=
    measurableSet_lt (measurable_const.mul hf) (hg.add hb)
  have hB : MeasurableSet {x | good x < bad x} := measurableSet_lt hg hb
  calc
    _ ≤ ∫⁻ x in {x | good x < bad x}, good x + bad x ∂μ := by
      rw [← lintegral_indicator hA, ← lintegral_indicator hB]
      apply lintegral_mono_ae
      filter_upwards [hgood] with x hx
      by_cases ha : 2 * c * f x < good x + bad x
      · have hb' : good x < bad x := by
          by_contra h
          have htotal : good x + bad x ≤ 2 * (c * f x) := by
            calc
              _ ≤ good x + good x := add_le_add (le_refl _) (le_of_not_gt h)
              _ = 2 * good x := (two_mul _).symm
              _ ≤ _ := mul_le_mul (le_refl 2) hx zero_le zero_le
          exact (not_lt_of_ge (by simpa only [mul_assoc] using htotal)) ha
        rw [indicator_of_mem (show x ∈ {x | 2 * c * f x < good x + bad x} from ha),
          indicator_of_mem (show x ∈ {x | good x < bad x} from hb')]
      · rw [indicator_of_notMem
          (show x ∉ {x | 2 * c * f x < good x + bad x} from ha)]
        exact zero_le
    _ ≤ _ := omitted_dominant_mass μ hg hb

/-- The omitted-mass estimate pulled back to the original incidence law. -/
theorem observation_upper_except_omitted {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (μ : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    (f good bad : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable good) (hb : Measurable bad)
    (hgood : good ≤ᵐ[μ] fun x => c * f x)
    (hlaw : ν.map obs = μ.withDensity (good + bad)) :
    ν {p | 2 * c * f (obs p) < good (obs p) + bad (obs p)} ≤
      2 * ∫⁻ x, bad x ∂μ := by
  have hA : MeasurableSet {x | 2 * c * f x < good x + bad x} :=
    measurableSet_lt (measurable_const.mul hf) (hg.add hb)
  change ν (obs ⁻¹' {x | 2 * c * f x < good x + bad x}) ≤ _
  rw [← Measure.map_apply hobs hA, hlaw, withDensity_apply _ hA]
  exact density_upper_except_omitted μ f good bad c hf hg hb hgood

/-- A further incidence restriction preserves the conditional angular ceiling, apart
from the old omitted mass and the explicit loss in the new pure denominator. The
multiplicative form avoids division and remains valid for extended densities. -/
theorem angular_bound_after_restriction {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    (ν : Measure Ω) (μ : Measure X) [SigmaFinite μ]
    (κ : Measure I) [SigmaFinite κ] (Z : Set Ω)
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (f F : X → ℝ≥0∞) (hf : Measurable f) (hF : Measurable F)
    (good bad current : X × I → ℝ≥0∞)
    (hg : Measurable good) (hb : Measurable bad) (hc : Measurable current)
    (c ε : ℝ≥0∞) (hgood : good ≤ᵐ[μ.prod κ] fun p => c * f p.1)
    (hpure : ν.map obs = μ.withDensity f)
    (hpure' : (ν.restrict Z).map obs = μ.withDensity F)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (μ.prod κ).withDensity (good + bad))
    (hjoint' : (ν.restrict Z).map (fun p => (obs p, ang p)) =
      (μ.prod κ).withDensity current) :
    ν.restrict Z {p | 2 * c * F (obs p) < ε * current (obs p, ang p)} ≤
      2 * (∫⁻ x, bad x ∂μ.prod κ) + ε * ν univ := by
  let o : Ω → X × I := fun p => (obs p, ang p)
  have ho : Measurable o := hobs.prodMk hang
  have hcurrent : current ≤ᵐ[μ.prod κ] good + bad :=
    observation_restriction_density_le ν (μ.prod κ) Z o ho hc hjoint hjoint'
  have habs : (ν.restrict Z).map o ≪ μ.prod κ := by
    rw [hjoint']
    exact withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ p ∂ν.restrict Z,
      current (o p) ≤ good (o p) + bad (o p) ∧ good (o p) ≤ c * f (obs p) := by
    exact ae_of_ae_map ho.aemeasurable (habs.ae_le (hcurrent.and hgood))
  have hsets : {p | 2 * c * F (obs p) < ε * current (o p)} ≤ᵐ[ν.restrict Z]
      (o ⁻¹' {x | good x < bad x}) ∪ (obs ⁻¹' lowDensity ε f F) := by
    filter_upwards [hae] with p hp
    intro hhigh
    by_cases hl : F (obs p) < ε * f (obs p)
    · exact Or.inr hl
    by_cases hb' : good (o p) < bad (o p)
    · exact Or.inl hb'
    have hnum : current (o p) ≤ 2 * c * f (obs p) := by
      calc
        _ ≤ good (o p) + bad (o p) := hp.1
        _ ≤ 2 * good (o p) := total_density_le_twice_good hb'
        _ ≤ 2 * (c * f (obs p)) := mul_le_mul (le_refl 2) hp.2 zero_le zero_le
        _ = _ := (mul_assoc _ _ _).symm
    have hbound : ε * current (o p) ≤ 2 * c * F (obs p) := by
      calc
        _ ≤ ε * (2 * c * f (obs p)) := mul_le_mul (le_refl ε) hnum zero_le zero_le
        _ = (2 * c) * (ε * f (obs p)) := by ring
        _ ≤ _ := mul_le_mul (le_refl (2 * c)) (le_of_not_gt hl) zero_le zero_le
    exact (not_lt_of_ge hbound hhigh).elim
  have hbadmass : ν.restrict Z (o ⁻¹' {x | good x < bad x}) ≤
      2 * ∫⁻ x, bad x ∂μ.prod κ := by
    calc
      _ ≤ ν (o ⁻¹' {x | good x < bad x}) := Measure.restrict_le_self _
      _ = ∫⁻ x in {x | good x < bad x}, good x + bad x ∂μ.prod κ := by
        rw [← Measure.map_apply ho (measurableSet_lt hg hb), hjoint,
          withDensity_apply _ (measurableSet_lt hg hb)]
        rfl
      _ ≤ _ := omitted_dominant_mass (μ.prod κ) hg hb
  calc
    _ ≤ ν.restrict Z ((o ⁻¹' {x | good x < bad x}) ∪ (obs ⁻¹' lowDensity ε f F)) :=
      measure_mono_ae hsets
    _ ≤ ν.restrict Z (o ⁻¹' {x | good x < bad x}) +
        ν.restrict Z (obs ⁻¹' lowDensity ε f F) := measure_union_le _ _
    _ ≤ _ := add_le_add hbadmass
      (observation_lowDensity_mass ν μ Z obs hobs ε hf hF hpure hpure')

end Submission.Lib.K4Homogenization
