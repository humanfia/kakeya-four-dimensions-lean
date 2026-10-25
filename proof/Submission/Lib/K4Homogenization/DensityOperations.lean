/-
Adapted from: here:o018
-/
import Mathlib

/-!
The fixed-tolerance measure estimates in Lemma `a01:density-operations`.
All densities and incidence masses are unnormalized, as in the paper.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

/-- The new observation states whose retained density is small relative to the old density. -/
def lowDensity {α : Type*} (ε : ℝ≥0∞) (f g : α → ℝ≥0∞) : Set α :=
  {x | g x < ε * f x}

theorem measurableSet_lowDensity {α : Type*} [MeasurableSpace α]
    (ε : ℝ≥0∞) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (lowDensity ε f g) :=
  measurableSet_lt hg (measurable_const.mul hf)

/-- Restriction loses a fixed density factor on at most that factor times the original mass. -/
theorem restriction_lowDensity_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ε : ℝ≥0∞) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in lowDensity ε f g, g x ∂μ) ≤ ε * ∫⁻ x, f x ∂μ := by
  rw [← lintegral_indicator (measurableSet_lowDensity ε hf hg)]
  calc
    (∫⁻ x, (lowDensity ε f g).indicator g x ∂μ) ≤ ∫⁻ x, ε * f x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ lowDensity ε f g
      · simpa only [indicator_of_mem hx] using (show g x < ε * f x from hx).le
      · simp only [indicator_of_notMem hx, zero_le]
    _ = ε * ∫⁻ x, f x ∂μ := lintegral_const_mul ε hf

/-- Refinement by `D` labels costs at most `D` times the one-label exceptional mass. -/
theorem refinement_lowDensity_mass {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (ε : ℝ≥0∞) {f : α → ℝ≥0∞} (g : ι → α → ℝ≥0∞)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i)) :
    (∑ i, ∫⁻ x in lowDensity ε f (g i), g i x ∂μ) ≤
      ε * (Fintype.card ι : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
  calc
    _ ≤ ∑ _ : ι, ε * ∫⁻ x, f x ∂μ :=
      Finset.sum_le_sum fun i _ => restriction_lowDensity_mass μ ε hf (hg i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The mass of states dominated by an omitted part is at most twice the omitted mass. -/
theorem omitted_dominant_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {good bad : α → ℝ≥0∞} (hg : Measurable good) (hb : Measurable bad) :
    (∫⁻ x in {x | good x < bad x}, good x + bad x ∂μ) ≤
      2 * ∫⁻ x, bad x ∂μ := by
  rw [← lintegral_indicator (measurableSet_lt hg hb)]
  calc
    (∫⁻ x, {x | good x < bad x}.indicator (fun x => good x + bad x) x ∂μ) ≤
        ∫⁻ x, 2 * bad x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : good x < bad x
      · rw [indicator_of_mem (show x ∈ {x | good x < bad x} from hx)]
        simpa only [two_mul] using add_le_add hx.le (le_refl (bad x))
      · rw [indicator_of_notMem (show x ∉ {x | good x < bad x} from hx)]
        exact zero_le
    _ = _ := lintegral_const_mul 2 hb

/-- Away from the omitted-dominant states, the full density is at most twice the good density. -/
theorem total_density_le_twice_good {α : Type*} {good bad : α → ℝ≥0∞}
    {x : α} (hx : x ∉ {x | good x < bad x}) :
    good x + bad x ≤ 2 * good x := by
  have h : bad x ≤ good x := le_of_not_gt hx
  simpa only [two_mul] using add_le_add (le_refl (good x)) h

/-- The density restriction estimate pulled back to the actual incidence space. -/
theorem observation_lowDensity_mass {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (ν : Measure Ω) (μ : Measure α) (Z : Set Ω) (obs : Ω → α) (hobs : Measurable obs)
    (ε : ℝ≥0∞) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hold : ν.map obs = μ.withDensity f)
    (hnew : (ν.restrict Z).map obs = μ.withDensity g) :
    ν.restrict Z (obs ⁻¹' lowDensity ε f g) ≤ ε * ν univ := by
  have hbad := measurableSet_lowDensity ε hf hg
  rw [← Measure.map_apply hobs hbad, hnew, withDensity_apply _ hbad]
  have hmass : (∫⁻ x, f x ∂μ) = ν univ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
      ← hold, Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  simpa only [hmass] using restriction_lowDensity_mass μ ε hf hg

/-- Restricting the incidence event decreases every observation density almost everywhere. -/
theorem observation_restriction_density_le {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (ν : Measure Ω) (μ : Measure α)
    [SigmaFinite μ] (Z : Set Ω) (obs : Ω → α) (hobs : Measurable obs)
    {f g : α → ℝ≥0∞} (hg : Measurable g)
    (hold : ν.map obs = μ.withDensity f)
    (hnew : (ν.restrict Z).map obs = μ.withDensity g) : g ≤ᵐ[μ] f := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg
  intro A hA _
  rw [← withDensity_apply _ hA, ← withDensity_apply _ hA, ← hnew, ← hold]
  exact Measure.map_mono Measure.restrict_le_self hobs A

/-- Every measurable version of the same observation density agrees at sampled
incidences almost surely, not just at almost every base point. -/
theorem observation_density_versions_aeEq {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (ν : Measure Ω) (μ : Measure α)
    [SigmaFinite μ] (obs : Ω → α) (hobs : Measurable obs)
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfLaw : ν.map obs = μ.withDensity f) (hgLaw : ν.map obs = μ.withDensity g) :
    ∀ᵐ p ∂ν, f (obs p) = g (obs p) := by
  have heq : f =ᵐ[μ] g := (withDensity_eq_iff_of_sigmaFinite
    hf.aemeasurable hg.aemeasurable).mp (hfLaw.symm.trans hgLaw)
  have habs : ν.map obs ≪ μ := by
    rw [hfLaw]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map hobs.aemeasurable (habs.ae_le heq)

/-- Exceptional masses defined by a density test are independent of the chosen
measurable RN version. This transfers typicality to every density in the frozen interface. -/
theorem observation_density_test_mass_eq {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (ν : Measure Ω) (μ : Measure α)
    [SigmaFinite μ] (obs : Ω → α) (hobs : Measurable obs)
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfLaw : ν.map obs = μ.withDensity f) (hgLaw : ν.map obs = μ.withDensity g)
    (P : α → ℝ≥0∞ → Prop) :
    ν {p | P (obs p) (f (obs p))} = ν {p | P (obs p) (g (obs p))} := by
  apply measure_congr
  filter_upwards [observation_density_versions_aeEq ν μ obs hobs hf hg hfLaw hgLaw] with p hp
  simp only [mem_ofPred_eq, hp]

/-- Several observation tests can be pruned simultaneously by summing their exceptional mass. -/
theorem observations_lowDensity_mass {Ω ι : Type*} {α : ι → Type*}
    [MeasurableSpace Ω] [Fintype ι] [∀ i, MeasurableSpace (α i)]
    (ν : Measure Ω) (μ : ∀ i, Measure (α i)) (Z : Set Ω)
    (obs : ∀ i, Ω → α i) (hobs : ∀ i, Measurable (obs i))
    (ε : ℝ≥0∞) (f g : ∀ i, α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hold : ∀ i, ν.map (obs i) = (μ i).withDensity (f i))
    (hnew : ∀ i, (ν.restrict Z).map (obs i) = (μ i).withDensity (g i)) :
    ν.restrict Z (⋃ i, (obs i) ⁻¹' lowDensity ε (f i) (g i)) ≤
      ε * (Fintype.card ι : ℝ≥0∞) * ν univ := by
  calc
    _ ≤ ∑ i, ν.restrict Z ((obs i) ⁻¹' lowDensity ε (f i) (g i)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : ι, ε * ν univ := Finset.sum_le_sum fun i _ =>
      observation_lowDensity_mass ν (μ i) Z (obs i) (hobs i) ε
        (hf i) (hg i) (hold i) (hnew i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- A large multiplicative discrepancy of finite nonnegative densities is charged to their
`L¹` difference. This is the error estimate used to transfer a flattened law back. -/
theorem density_discrepancy_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in {x | 2 * f x < g x}, ENNReal.ofReal (g x) ∂μ) ≤
      2 * ∫⁻ x, ENNReal.ofReal |g x - f x| ∂μ := by
  have hB : MeasurableSet {x | 2 * f x < g x} :=
    measurableSet_lt ((measurable_const : Measurable (fun _ : α => (2 : ℝ))).mul hf) hg
  rw [← lintegral_indicator hB]
  calc
    (∫⁻ x, {x | 2 * f x < g x}.indicator (fun x => ENNReal.ofReal (g x)) x ∂μ) ≤
        ∫⁻ x, 2 * ENNReal.ofReal |g x - f x| ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : 2 * f x < g x
      · rw [indicator_of_mem (show x ∈ {x | 2 * f x < g x} from hx)]
        calc
          ENNReal.ofReal (g x) ≤ ENNReal.ofReal (2 * |g x - f x|) :=
            ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (g x - f x)])
          _ = 2 * ENNReal.ofReal |g x - f x| := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
      · rw [indicator_of_notMem (show x ∉ {x | 2 * f x < g x} from hx)]
        exact zero_le
    _ = _ := lintegral_const_mul 2 ((hg.sub hf).abs.ennreal_ofReal)

/-- A retained refinement carrying positive mass cannot have all its fine densities too
small relative to its coarse density. This is the finite scale comparison behind the
Lipschitz bound for the homogeneous density profile. -/
theorem refinement_density_scale_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : α → ℝ≥0∞) (g : ι → α → ℝ≥0∞)
    (R : ι → Set α) (a b : ℝ≥0∞)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hR : ∀ i, MeasurableSet (R i))
    (hscale : ∀ i, ∀ x ∈ R i, a ≤ f x ∧ g i x ≤ b) :
    a * (∑ i, ∫⁻ x in R i, g i x ∂μ) ≤
      b * (Fintype.card ι : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
  have hi (i : ι) : a * (∫⁻ x in R i, g i x ∂μ) ≤ b * ∫⁻ x, f x ∂μ := by
    rw [← lintegral_indicator (hR i)]
    calc
      a * (∫⁻ x, (R i).indicator (g i) x ∂μ) =
          ∫⁻ x, a * (R i).indicator (g i) x ∂μ :=
        (lintegral_const_mul a ((hg i).indicator (hR i))).symm
      _ ≤ ∫⁻ x, b * f x ∂μ := by
        apply lintegral_mono
        intro x
        change a * (R i).indicator (g i) x ≤ b * f x
        by_cases hx : x ∈ R i
        · rw [indicator_of_mem hx]
          calc
            a * g i x ≤ f x * b :=
              mul_le_mul (hscale i x hx).1 (hscale i x hx).2 zero_le zero_le
            _ = b * f x := mul_comm _ _
        · rw [indicator_of_notMem hx, mul_zero]
          exact zero_le
      _ = b * ∫⁻ x, f x ∂μ := lintegral_const_mul b hf
  calc
    _ = ∑ i, a * (∫⁻ x in R i, g i x ∂μ) := Finset.mul_sum _ _ _
    _ ≤ ∑ _ : ι, b * ∫⁻ x, f x ∂μ := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Submission.Lib.K4Homogenization
