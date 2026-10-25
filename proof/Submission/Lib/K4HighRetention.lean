/- Adapted from: here:o266
   Original complementary state-retention and current breadth proof by
   session x0944, commit 287bb057,
   Submission/Obl/k4_narrow_original_potential_atlas/RetentionBreadth.lean.
   Broad is imported from the accepted K4ThreeBaseRows library. -/
import Submission.Lib.K4ThreeBaseRows.SupportedTriples
import Submission.Lib.K4StateFractionKeep

set_option maxHeartbeats 1000000

/-! High retention in the original cells.  The complementary estimate
charges the mass ACTUALLY deleted by a preceding cut, rather than a
fixed fraction of the whole earlier source. -/

namespace Submission.Lib.K4HighRetention

open Set MeasureTheory
open Submission.Lib.K4ThreeBaseRows
open Submission.Lib.K4StateFractionKeep
open scoped ENNReal

noncomputable section

namespace StateRetention

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]

/-- The part deleted by a state-fraction cut is paid for by the missing
mass of the preceding source.  This is useful when the fraction is
close to one and the preceding cut has very small loss. -/
theorem measure_diff_fractionKeep_le_deficit
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → I) (hstate : Measurable state)
    (R : Set Ω) (hRm : MeasurableSet R) {f : ℝ} (hf : 0 ≤ f) (hf1 : f < 1) :
    μ (R \ fractionKeep μ state R (ENNReal.ofReal f)) ≤
      ENNReal.ofReal (f/(1-f))*μ Rᶜ := by
  classical
  let bad : Set I := {i | i ∉ goodStates μ state R (ENNReal.ofReal f)}
  have hfiber (i : I) : MeasurableSet (state ⁻¹' {i}) := hstate (measurableSet_singleton i)
  have hden : 0 < 1-f := sub_pos.mpr hf1
  have hK : 0 ≤ f/(1-f) := div_nonneg hf hden.le
  have hcharge (i : bad) : μ (R ∩ state ⁻¹' {(i : I)}) ≤
      ENNReal.ofReal (f/(1-f))*μ ((state ⁻¹' {(i : I)}) \ R) := by
    have hi := i.property
    change ¬ ENNReal.ofReal f*μ (state ⁻¹' {(i : I)}) ≤ μ (R ∩ state ⁻¹' {(i : I)}) at hi
    have hsmall := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) (lt_of_not_ge hi).le
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hf] at hsmall
    change μ.real (R ∩ state ⁻¹' {(i : I)}) ≤ f*μ.real (state ⁻¹' {(i : I)}) at hsmall
    have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := state ⁻¹' {(i : I)}) hRm
    rw [inter_comm] at hsplit
    have hreal : μ.real (R ∩ state ⁻¹' {(i : I)}) ≤
        (f/(1-f))*μ.real ((state ⁻¹' {(i : I)}) \ R) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hden]
      rw [← hsplit] at hsmall
      nlinarith
    calc
      _ = ENNReal.ofReal (μ.real (R ∩ state ⁻¹' {(i : I)})) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((f/(1-f))*μ.real ((state ⁻¹' {(i : I)}) \ R)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul hK]
        congr 1
        exact ENNReal.ofReal_toReal (measure_ne_top μ _)
  have hsub : R \ fractionKeep μ state R (ENNReal.ofReal f) ⊆
      ⋃ i : bad, R ∩ state ⁻¹' {(i : I)} := by
    intro z hz
    have hzbad : state z ∈ bad := fun h => hz.2 ⟨hz.1, h⟩
    exact mem_iUnion.mpr ⟨⟨state z, hzbad⟩, hz.1, rfl⟩
  have hdisj : Pairwise (fun i j : bad =>
      Disjoint ((state ⁻¹' {(i : I)}) \ R) ((state ⁻¹' {(j : I)}) \ R)) := by
    intro i j hij
    apply ((Disjoint.preimage state (Set.disjoint_singleton.mpr
      (fun h => hij (Subtype.ext h)))).mono_left sdiff_subset).mono_right sdiff_subset
  calc
    _ ≤ μ (⋃ i : bad, R ∩ state ⁻¹' {(i : I)}) := measure_mono hsub
    _ ≤ ∑' i : bad, μ (R ∩ state ⁻¹' {(i : I)}) := measure_iUnion_le _
    _ ≤ ∑' i : bad, ENNReal.ofReal (f/(1-f))*μ ((state ⁻¹' {(i : I)}) \ R) :=
      ENNReal.tsum_le_tsum hcharge
    _ = ENNReal.ofReal (f/(1-f))*∑' i : bad, μ ((state ⁻¹' {(i : I)}) \ R) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (f/(1-f))*μ (⋃ i : bad, (state ⁻¹' {(i : I)}) \ R) := by
      rw [measure_iUnion hdisj (fun i => (hfiber i).diff hRm)]
    _ ≤ ENNReal.ofReal (f/(1-f))*μ Rᶜ := by
      apply mul_le_mul' le_rfl
      apply measure_mono
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hi.2

/-- The TOTAL complementary mass of the high-retention source is at
most the preceding loss divided by `1-f`. -/
theorem measure_compl_fractionKeep_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → I) (hstate : Measurable state)
    (R : Set Ω) (hRm : MeasurableSet R) {f : ℝ} (hf : 0 ≤ f) (hf1 : f < 1) :
    μ (fractionKeep μ state R (ENNReal.ofReal f))ᶜ ≤
      ENNReal.ofReal (1/(1-f))*μ Rᶜ := by
  have hsub : (fractionKeep μ state R (ENNReal.ofReal f))ᶜ ⊆
      Rᶜ ∪ (R \ fractionKeep μ state R (ENNReal.ofReal f)) := by
    intro z hz
    by_cases hzR : z ∈ R
    · exact Or.inr ⟨hzR, hz⟩
    · exact Or.inl hzR
  have hK : 0 ≤ f/(1-f) := div_nonneg hf (sub_pos.mpr hf1).le
  have hcoeff : (1 : ENNReal)+ENNReal.ofReal (f/(1-f)) = ENNReal.ofReal (1/(1-f)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hK]
    congr 1
    field_simp [(sub_pos.mpr hf1).ne']
    ring
  calc
    _ ≤ μ Rᶜ+μ (R \ fractionKeep μ state R (ENNReal.ofReal f)) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ μ Rᶜ+ENNReal.ofReal (f/(1-f))*μ Rᶜ :=
      add_le_add le_rfl (measure_diff_fractionKeep_le_deficit μ state hstate R hRm hf hf1)
    _ = ((1 : ENNReal)+ENNReal.ofReal (f/(1-f)))*μ Rᶜ := by ring
    _ = _ := by rw [hcoeff]

end StateRetention

/-- A set retaining all but at most half of the breadth fraction keeps
half the original breadth, at the same radius and in the original law. -/
theorem broad_restrict_of_mass_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (e : Ω → EuclideanSpace ℝ (Fin 3)) (he : Measurable e)
    {ρ c : ℝ} (hc : 0 ≤ c) (hbroad : Broad μ e ρ c)
    (R : Set Ω) (hRm : MeasurableSet R)
    (hmass : (1-c/2)*μ.real univ ≤ μ.real R) :
    Broad (μ.restrict R) e ρ (c/2) := by
  intro V hV
  let Far := {z | ρ ≤ Metric.infDist (e z) (V : Set (EuclideanSpace ℝ (Fin 3)))}
  have hFar : MeasurableSet Far := measurableSet_le measurable_const he.infDist
  have hcover : Far ⊆ (Far ∩ R) ∪ Rᶜ := by
    intro z hz
    by_cases hzR : z ∈ R
    · exact Or.inl ⟨hz, hzR⟩
    · exact Or.inr hzR
  have hfarMass : μ.real Far ≤ μ.real (Far ∩ R)+μ.real Rᶜ :=
    (measureReal_mono hcover).trans (measureReal_union_le _ _)
  have hsplit := measureReal_add_measureReal_compl (μ := μ) hRm
  have hmono : (c/2)*μ.real R ≤ (c/2)*μ.real univ :=
    mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ R)) (by positivity)
  have hold := hbroad V hV
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply hFar]
  change (c/2)*μ.real R ≤ μ.real (Far ∩ R)
  linarith

namespace StateRetention

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]

/-- A small arbitrary measurable deletion can be repaired in every
CURRENT cell law at cost `2/c` times that ACTUAL deletion.  No cell count,
new prior, or a tiny earlier strip ratio is assumed. -/
theorem restore_cell_breadth
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → I) (hstate : Measurable state)
    (e : Ω → EuclideanSpace ℝ (Fin 3)) (he : Measurable e) {ρ c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hbroad : ∀ i, Broad (μ.restrict (state ⁻¹' {i})) e ρ c)
    (R : Set Ω) (hRm : MeasurableSet R) :
    ∃ S : Set Ω, MeasurableSet S ∧ S ⊆ R ∧
      μ Sᶜ ≤ ENNReal.ofReal (2/c)*μ Rᶜ ∧
      ∀ i, Broad ((μ.restrict S).restrict (state ⁻¹' {i})) e ρ (c/2) := by
  classical
  let f := 1-c/2
  have hf : 0 ≤ f := by dsimp only [f]; linarith
  have hf1 : f < 1 := by dsimp only [f]; linarith
  let S := fractionKeep μ state R (ENNReal.ofReal f)
  have hSm : MeasurableSet S := measurableSet_fractionKeep hstate hRm _
  refine ⟨S, hSm, inter_subset_left, ?_, ?_⟩
  · have hh := measure_compl_fractionKeep_le μ state hstate R hRm hf hf1
    have heq : 1/(1-f)=2/c := by dsimp only [f]; field_simp [hc.ne']; ring
    simpa only [heq] using hh
  · intro i
    let cell : Set Ω := state ⁻¹' {i}
    have hcell : MeasurableSet cell := hstate (measurableSet_singleton i)
    by_cases hi : i ∈ goodStates μ state R (ENNReal.ofReal f)
    · have heq : S ∩ cell=R ∩ cell := by
        ext z
        constructor
        · exact fun hz => ⟨hz.1.1, hz.2⟩
        · intro hz
          refine ⟨⟨hz.1, ?_⟩, hz.2⟩
          change state z ∈ goodStates μ state R (ENNReal.ofReal f)
          have hzcode : state z=i := hz.2
          rw [hzcode]
          exact hi
      have hret := ENNReal.toReal_mono (measure_ne_top μ (R ∩ cell)) hi
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hf] at hret
      have hret' : (1-c/2)*(μ.restrict cell).real univ ≤ (μ.restrict cell).real R := by
        simpa only [Measure.real, Measure.restrict_apply_univ, Measure.restrict_apply hRm,
          f, cell] using hret
      have hh := broad_restrict_of_mass_floor (μ.restrict cell) e he hc.le (hbroad i) R hRm hret'
      have hlaw : (μ.restrict S).restrict cell=(μ.restrict cell).restrict R := by
        rw [Measure.restrict_restrict hcell, Measure.restrict_restrict hRm]
        congr 1
        exact (inter_comm cell S).trans heq
      rw [hlaw]
      exact hh
    · have heq : S ∩ cell=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzcode : state z=i := hz.2
        exact hi (by simpa only [mem_preimage, hzcode] using hz.1.2)
      rw [Measure.restrict_restrict hcell, inter_comm, heq, Measure.restrict_empty]
      intro V hV
      simp

end StateRetention

end

end Submission.Lib.K4HighRetention
