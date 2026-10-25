import Submission.Lib.K4Homogenization.AngularCoarsening

/-! Angular ceilings at sampled entries under deterministic coarsening. -/

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- A fine pure lower cutoff and a fine joint upper cutoff yield a conditional
ceiling after any measurable coarsening, with twice the omitted source mass. -/
theorem coarsened_angular_tail
    {Ω X Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (m : Measure Y) [SigmaFinite m]
    (o : Ω → X) (ho : Measurable o) (a : Ω → I) (ha : Measurable a)
    (q : X → Y) (hq : Measurable q)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (F : Y → ℝ≥0∞) (hF : Measurable F)
    (g : X × I → ℝ≥0∞) (hg : Measurable g)
    (G : Y × I → ℝ≥0∞) (hG : Measurable G)
    (hflaw : ν.map o = μ.withDensity f)
    (hFlaw : ν.map (q ∘ o) = m.withDensity F)
    (hglaw : ν.map (fun p => (o p, a p)) = (μ.prod Measure.count).withDensity g)
    (hGlaw : ν.map (fun p => (q (o p), a p)) =
      (m.prod Measure.count).withDensity G)
    (lo hi c : ℝ≥0∞) (hscale : hi ≤ c * lo) :
    ν {p | 2 * c * F (q (o p)) < G (q (o p), a p)} ≤
      2 * ν {p | f (o p) < lo ∨ hi < g (o p, a p)} := by
  classical
  let U : Set (X × I) := {z | lo ≤ f z.1 ∧ g z ≤ hi}
  have hU : MeasurableSet U :=
    (measurableSet_le measurable_const (hf.comp measurable_fst)).inter
      (measurableSet_le hg measurable_const)
  let fine : Ω → X × I := fun p => (o p, a p)
  have hfine : Measurable fine := ho.prodMk ha
  let S : Set Ω := fine ⁻¹' U
  have hS : MeasurableSet S := hfine hU
  let coarse : Ω → Y × I := fun p => (q (o p), a p)
  have hcoarse : Measurable coarse := (hq.comp ho).prodMk ha
  have hgood : (ν.restrict S).map fine ≤ c • (ν.map o).prod Measure.count := by
    rw [← Measure.restrict_map hfine hU, hglaw, restrict_withDensity hU,
      ← withDensity_indicator hU]
    rw [hflaw, prod_withDensity_left hf,
      ← withDensity_smul (μ := μ.prod Measure.count) c
        (show Measurable (fun z : X × I => f z.1) from hf.comp measurable_fst)]
    apply withDensity_mono
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp only [indicator_of_mem hz, Pi.smul_apply, smul_eq_mul]
        exact (hz.2.trans hscale).trans (mul_le_mul (le_refl c) hz.1 zero_le zero_le)
      · simp only [indicator_of_notMem hz, zero_le]
  have hfullac : ν.map coarse ≪ m.prod Measure.count := by
    rw [hGlaw]
    exact withDensity_absolutelyContinuous _ _
  have hac (T : Set Ω) : (ν.restrict T).map coarse ≪ m.prod Measure.count :=
    (Measure.absolutelyContinuous_of_le (Measure.map_mono Measure.restrict_le_self hcoarse)).trans
      hfullac
  let good := ((ν.restrict S).map coarse).rnDeriv (m.prod Measure.count)
  let bad := ((ν.restrict Sᶜ).map coarse).rnDeriv (m.prod Measure.count)
  have hgoodm : Measurable good := Measure.measurable_rnDeriv _ _
  have hbadm : Measurable bad := Measure.measurable_rnDeriv _ _
  have hgoodlaw : (ν.restrict S).map coarse = (m.prod Measure.count).withDensity good :=
    (Measure.withDensity_rnDeriv_eq _ _ (hac S)).symm
  have hbadlaw : (ν.restrict Sᶜ).map coarse = (m.prod Measure.count).withDensity bad :=
    (Measure.withDensity_rnDeriv_eq _ _ (hac Sᶜ)).symm
  have hsumlaw : ν.map coarse = (m.prod Measure.count).withDensity (good + bad) := by
    rw [withDensity_add_left hgoodm, ← hgoodlaw, ← hbadlaw,
      ← Measure.map_add _ _ hcoarse, Measure.restrict_add_restrict_compl hS]
  have hqgood : ((ν.restrict S).map fine).map (Prod.map q id) =
      (m.prod Measure.count).withDensity good := by
    rw [Measure.map_map (hq.prodMap measurable_id) hfine]
    exact hgoodlaw
  have hpure : (ν.map o).map q = m.withDensity F := by
    rw [Measure.map_map hq ho]
    exact hFlaw
  have hbound : good ≤ᵐ[m.prod Measure.count] fun p => c * F p.1 :=
    Submission.Lib.K4Homogenization.coarsened_joint_density_le (ν.map o)
      Measure.count ((ν.restrict S).map fine) c hgood q hq m F hF hpure good hgoodm hqgood
  have htail := Submission.Lib.K4Homogenization.observation_upper_except_omitted
    ν (m.prod Measure.count) coarse hcoarse (fun z => F z.1) good bad c
    (hF.comp measurable_fst) hgoodm hbadm hbound hsumlaw
  have heq := Submission.Lib.K4Homogenization.observation_density_test_mass_eq
    ν (m.prod Measure.count) coarse hcoarse hG (hgoodm.add hbadm) hGlaw hsumlaw
    (fun z t => 2 * c * F z.1 < t)
  change ν {p | 2 * c * F (coarse p).1 < G (coarse p)} ≤ _
  rw [heq]
  apply htail.trans
  have hbadmass : (∫⁻ z, bad z ∂m.prod Measure.count) = ν Sᶜ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hbadlaw,
      Measure.map_apply hcoarse MeasurableSet.univ]
    simp
  rw [hbadmass]
  apply mul_le_mul (le_refl 2) _ zero_le zero_le
  apply measure_mono
  intro p hp
  change p ∉ S at hp
  change ¬ (lo ≤ f (o p) ∧ g (o p, a p) ≤ hi) at hp
  simpa only [Set.mem_ofPred_eq, not_and_or, not_le] using hp

end Submission.Obl.k4_coarsened_outer_horizon_composition
