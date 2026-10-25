/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/CountedRefinement.lean. Earlier source attributions are retained below.
-/

import Mathlib

/-!
# Densities under a finite refinement of counting labels

The continuous coordinates are retained. A map on the discrete labels groups
fine densities by its fibers. This gives both density monotonicity and the
low-density tail estimate, with the maximal fiber size as the only loss.
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set MeasureTheory
open scoped ENNReal

section
variable {X B C : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]

/-- Summing a density over the fibers of a discrete label map. -/
noncomputable def fiberDensity (h : B → C) (g : X × B → ℝ≥0∞) (p : X × C) : ℝ≥0∞ :=
  ∑' b : h ⁻¹' {p.2}, g (p.1, b)

theorem measurable_fiberDensity (h : B → C) (g : X × B → ℝ≥0∞)
    (hg : Measurable g) : Measurable (fiberDensity h g) := by
  apply measurable_from_prod_countable_left
  intro c
  change Measurable (fun x : X => ∑' b : h ⁻¹' {c}, g (x, b))
  exact Measurable.tsum fun b : h ⁻¹' {c} =>
    hg.comp (measurable_id.prodMk (measurable_const (a := (b : B))))

/-- Discrete coarsening leaves the continuous reference measure unchanged. -/
theorem map_labels_withDensity (ν : Measure X) (h : B → C)
    (g : X × B → ℝ≥0∞) (hg : Measurable g) :
    ((ν.prod Measure.count).withDensity g).map (fun p => (p.1, h p.2)) =
      (ν.prod Measure.count).withDensity (fiberDensity h g) := by
  classical
  have hh : Measurable h := measurable_of_countable _
  have hT : Measurable (fun p : X × B => (p.1, h p.2)) :=
    measurable_fst.prodMk (hh.comp measurable_snd)
  ext S hS
  rw [Measure.map_apply hT hS, withDensity_apply _ (hT hS),
    ← lintegral_indicator (hT hS),
    lintegral_prod _ (hg.indicator (hT hS)).aemeasurable,
    withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ ((measurable_fiberDensity h g hg).indicator hS).aemeasurable]
  apply lintegral_congr
  intro x
  simp only [lintegral_count]
  rw [← ENNReal.tsum_fiberwise
    (fun b => ((fun p : X × B => (p.1, h p.2)) ⁻¹' S).indicator g (x, b)) h]
  apply tsum_congr
  intro c
  by_cases hc : (x, c) ∈ S
  · simp only [Set.indicator_apply, mem_preimage]
    simp only [show ∀ b : h ⁻¹' {c}, h b = c from fun b => b.property, hc, ite_true,
      fiberDensity]
  · simp only [Set.indicator_apply, mem_preimage]
    simp only [show ∀ b : h ⁻¹' {c}, h b = c from fun b => b.property, hc, ite_false,
      tsum_zero]

/-- A fine density is at most its coarsened density almost everywhere for the
fine law. This statement is independent of the chosen density representatives. -/
theorem counted_refinement_density_le (ν : Measure X) [SigmaFinite ν]
    (h : B → C) (f : X × C → ℝ≥0∞) (g : X × B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hmap : ((ν.prod Measure.count).withDensity g).map (fun p => (p.1, h p.2)) =
      (ν.prod Measure.count).withDensity f) :
    ∀ᵐ p ∂(ν.prod Measure.count).withDensity g, g p ≤ f (p.1, h p.2) := by
  have heq : fiberDensity h g =ᵐ[ν.prod Measure.count] f := by
    apply (withDensity_eq_iff_of_sigmaFinite
      (measurable_fiberDensity h g hg).aemeasurable hf.aemeasurable).mp
    exact (map_labels_withDensity ν h g hg).symm.trans hmap
  have heq' : ∀ᵐ p ∂(ν.prod Measure.count).withDensity f, fiberDensity h g p = f p :=
    (withDensity_absolutelyContinuous _ _) heq
  have hh : Measurable h := measurable_of_countable _
  have hT : Measurable (fun p : X × B => (p.1, h p.2)) :=
    measurable_fst.prodMk (hh.comp measurable_snd)
  rw [← hmap] at heq'
  have hgood := (ae_map_iff hT.aemeasurable
    (measurableSet_le (measurable_fiberDensity h g hg) hf |>.inter
      (measurableSet_le hf (measurable_fiberDensity h g hg)))).mp
    (heq'.mono fun _ hp => ⟨hp.le, hp.ge⟩)
  filter_upwards [hgood] with p hp
  exact (ENNReal.le_tsum (⟨p.2, rfl⟩ : h ⁻¹' {h p.2})).trans hp.1

/-- Uniformly bounded discrete fibers control the sum of a pulled-back function. -/
theorem tsum_comp_le_of_count_fiber_le (h : B → C) (D : ℝ≥0∞)
    (hD : ∀ c, Measure.count {b : B | h b = c} ≤ D) (f : C → ℝ≥0∞) :
    (∑' b, f (h b)) ≤ D * ∑' c, f c := by
  classical
  rw [← ENNReal.tsum_fiberwise (fun b => f (h b)) h, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro c
  calc
    (∑' b : {b : B // h b = c}, f (h b)) =
        (∑' _b : {b : B // h b = c}, (1 : ℝ≥0∞)) * f c := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro b
      simp only [b.property, one_mul]
    _ ≤ D * f c := mul_le_mul' ((Measure.le_count_apply).trans (hD c)) le_rfl

/-- A refinement with at most `D` labels per coarse label has at most
`ε * D * total mass` in entries of density below `ε` times the coarse density. -/
theorem counted_refinement_low_density_mass (ν : Measure X)
    (h : B → C) (ε D : ℝ≥0∞)
    (hD : ∀ c, Measure.count {b : B | h b = c} ≤ D)
    (f : X × C → ℝ≥0∞) (g : X × B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (ν.prod Measure.count).withDensity g {p | g p < ε * f (p.1, h p.2)} ≤
      ε * D * ∫⁻ p, f p ∂(ν.prod Measure.count) := by
  classical
  have hh : Measurable h := measurable_of_countable _
  let A : Set (X × B) := {p | g p < ε * f (p.1, h p.2)}
  have hA : MeasurableSet A := measurableSet_lt hg
    (measurable_const.mul (hf.comp (measurable_fst.prodMk (hh.comp measurable_snd))))
  rw [withDensity_apply _ hA, ← lintegral_indicator hA,
    lintegral_prod _ (hg.indicator hA).aemeasurable,
    lintegral_prod _ hf.aemeasurable]
  simp only [lintegral_count]
  calc
    (∫⁻ x, ∑' b, A.indicator g (x, b) ∂ν) ≤
        ∫⁻ x, ε * (D * ∑' c, f (x, c)) ∂ν := by
      apply lintegral_mono
      intro x
      calc
        (∑' b, A.indicator g (x, b)) ≤ ∑' b, ε * f (x, h b) := by
          apply ENNReal.tsum_le_tsum
          intro b
          by_cases hb : (x, b) ∈ A
          · exact (Set.indicator_of_mem hb _).trans_le hb.le
          · rw [Set.indicator_of_notMem hb]
            exact zero_le
        _ = ε * ∑' b, f (x, h b) := ENNReal.tsum_mul_left
        _ ≤ ε * (D * ∑' c, f (x, c)) :=
          mul_le_mul' le_rfl (tsum_comp_le_of_count_fiber_le h D hD (fun c => f (x, c)))
    _ = ε * D * ∫⁻ x, ∑' c, f (x, c) ∂ν := by
      simp only [← mul_assoc]
      exact lintegral_const_mul _ (Measurable.tsum fun c =>
        hf.comp (measurable_id.prodMk measurable_const))

end

section Observation
variable {A X B C : Type*} [MeasurableSpace A] [MeasurableSpace X]
  [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]

/-- Refining only the discrete part of an observation decreases its density
almost everywhere on the original probability space. -/
theorem observation_refinement_density_le (μ : Measure A) (ν : Measure X) [SigmaFinite ν]
    (Q : A → X × B) (hQ : Measurable Q) (h : B → C)
    (f : X × C → ℝ≥0∞) (g : X × B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map (fun a => ((Q a).1, h (Q a).2)) =
      (ν.prod Measure.count).withDensity f)
    (hgmap : μ.map Q = (ν.prod Measure.count).withDensity g) :
    ∀ᵐ a ∂μ, g (Q a) ≤ f ((Q a).1, h (Q a).2) := by
  have hh : Measurable h := measurable_of_countable _
  have hT : Measurable (fun p : X × B => (p.1, h p.2)) :=
    measurable_fst.prodMk (hh.comp measurable_snd)
  have hm : ((ν.prod Measure.count).withDensity g).map (fun p => (p.1, h p.2)) =
      (ν.prod Measure.count).withDensity f := by
    rw [← hgmap, Measure.map_map hT hQ]
    exact hfmap
  have ha := counted_refinement_density_le ν h f g hf hg hm
  rw [← hgmap] at ha
  exact (ae_map_iff hQ.aemeasurable (measurableSet_le hg (hf.comp hT))).mp ha

/-- The low-tail refinement estimate expressed directly on the state space. -/
theorem observation_refinement_low_density_mass (μ : Measure A) (ν : Measure X)
    (Q : A → X × B) (hQ : Measurable Q) (h : B → C) (ε D : ℝ≥0∞)
    (hD : ∀ c, Measure.count {b : B | h b = c} ≤ D)
    (f : X × C → ℝ≥0∞) (g : X × B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map (fun a => ((Q a).1, h (Q a).2)) =
      (ν.prod Measure.count).withDensity f)
    (hgmap : μ.map Q = (ν.prod Measure.count).withDensity g) :
    μ {a | g (Q a) < ε * f ((Q a).1, h (Q a).2)} ≤ ε * D * μ Set.univ := by
  have hh : Measurable h := measurable_of_countable _
  have hT : Measurable (fun p : X × B => (p.1, h p.2)) :=
    measurable_fst.prodMk (hh.comp measurable_snd)
  have hA : MeasurableSet {p : X × B | g p < ε * f (p.1, h p.2)} :=
    measurableSet_lt hg (measurable_const.mul (hf.comp hT))
  have hm : ∫⁻ p, f p ∂(ν.prod Measure.count) = μ Set.univ := by
    calc
      _ = (ν.prod Measure.count).withDensity f Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = μ.map (fun a => ((Q a).1, h (Q a).2)) Set.univ := by rw [hfmap]
      _ = μ Set.univ := by
        simpa only [Function.comp_def, preimage_univ] using
          (Measure.map_apply (μ := μ) (hT.comp hQ) MeasurableSet.univ)
  calc
    μ {a | g (Q a) < ε * f ((Q a).1, h (Q a).2)} =
        (ν.prod Measure.count).withDensity g {p | g p < ε * f (p.1, h p.2)} := by
      rw [← hgmap, Measure.map_apply hQ hA]
      rfl
    _ ≤ ε * D * ∫⁻ p, f p ∂(ν.prod Measure.count) :=
      counted_refinement_low_density_mass ν h ε D hD f g hf hg
    _ = ε * D * μ Set.univ := by rw [hm]

end Observation
end Submission.Obl.k4_native_grid_profile_extension
