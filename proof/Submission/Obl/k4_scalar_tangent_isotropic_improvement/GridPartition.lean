import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridCells

/-! Full original-mass finite grid partitions with pointwise good representatives. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory
open Submission.Obl.k4_matching_endpoint_volume (gridTag)
open scoped BigOperators Classical

/-- An almost-everywhere bounded law has a finite measurable grid partition on
a full-measure core where any given almost-everywhere property holds pointwise.
Every restriction to that core preserves the original measure of every event. -/
theorem exists_positive_grid_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (P : Ω → Prop) {n : ℕ}
    (f : Ω → Fin n → ℝ) (hf : Measurable f) {B ξ : ℝ} (hξ : 0 < ξ)
    (hgood : ∀ᵐ ω ∂μ, P ω ∧ ∀ i, |f ω i| ≤ B) :
    ∃ (G : Set Ω) (S : Finset (Fin n → ℤ)),
      MeasurableSet G ∧ μ Gᶜ = 0 ∧
      (∀ ω ∈ G, P ω ∧ ∀ i, |f ω i| ≤ B) ∧
      (∀ E : Set Ω, μ (G ∩ E) = μ E) ∧
      (∀ q, MeasurableSet (G ∩ {ω | gridTag ξ (f ω) = q})) ∧
      (Pairwise fun q q' : Fin n → ℤ =>
        Disjoint (G ∩ {ω | gridTag ξ (f ω) = q}) (G ∩ {ω | gridTag ξ (f ω) = q'})) ∧
      (∀ q ∈ S, 0 < μ (G ∩ {ω | gridTag ξ (f ω) = q})) ∧
      (∑ q ∈ S, (μ (G ∩ {ω | gridTag ξ (f ω) = q})).toReal) = (μ Set.univ).toReal ∧
      (∀ q ∈ S, ∀ ω ∈ G ∩ {ω | gridTag ξ (f ω) = q},
        ∀ ω' ∈ G ∩ {ω | gridTag ξ (f ω) = q}, dist (f ω) (f ω') ≤ ξ) := by
  let Bad : Set Ω := {ω | ¬ (P ω ∧ ∀ i, |f ω i| ≤ B)}
  have hbad : μ Bad = 0 := (ae_iff).mp hgood
  let G : Set Ω := (toMeasurable μ Bad)ᶜ
  have hGmeas : MeasurableSet G := (measurableSet_toMeasurable μ Bad).compl
  have hGfull : μ Gᶜ = 0 := by simpa only [G, compl_compl, measure_toMeasurable] using hbad
  have hGgood (ω : Ω) (hω : ω ∈ G) : P ω ∧ ∀ i, |f ω i| ≤ B := by
    by_contra h
    exact hω (subset_toMeasurable μ Bad h)
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := (ae_iff).mpr hGfull
  have hpreserve (E : Set Ω) : μ (G ∩ E) = μ E := by
    apply measure_congr
    filter_upwards [hGae] with ω hω
    simp only [Set.mem_inter_iff, hω, true_and]
  let Cells : (Fin n → ℤ) → Set Ω := fun q => G ∩ {ω | gridTag ξ (f ω) = q}
  have htag : Measurable (fun ω => gridTag ξ (f ω)) := by
    apply Measurable.of_eval
    intro i
    dsimp only [gridTag]
    fun_prop
  have hCells (q : Fin n → ℤ) : MeasurableSet (Cells q) :=
    hGmeas.inter (measurableSet_eq_fun htag measurable_const)
  have hdisj : Pairwise fun q q' : Fin n → ℤ => Disjoint (Cells q) (Cells q') := by
    intro q q' hne
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hne (hω.2.symm.trans hω'.2)
  let Q : Finset (Fin n → ℤ) := Fintype.piFinset
    (fun _ => Finset.Icc (⌊-B / ξ⌋ : ℤ) (⌊B / ξ⌋ : ℤ))
  have hcover : G = ⋃ q ∈ Q, Cells q := by
    apply Set.Subset.antisymm
    · intro ω hω
      refine Set.mem_iUnion₂.mpr ⟨gridTag ξ (f ω), ?_, hω, rfl⟩
      apply Fintype.mem_piFinset.mpr
      intro i
      have hb := abs_le.mp ((hGgood ω hω).2 i)
      exact Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hb.1 hξ.le),
        Int.floor_mono (div_le_div_of_nonneg_right hb.2 hξ.le)⟩
    · intro ω hω
      obtain ⟨q, hq, hω⟩ := Set.mem_iUnion₂.mp hω
      exact hω.1
  have hdisjQ : (↑Q : Set (Fin n → ℤ)).PairwiseDisjoint Cells :=
    fun i hi j hj hij => hdisj hij
  have hsum : (∑ q ∈ Q, (μ (Cells q)).toReal) = (μ Set.univ).toReal := by
    rw [← ENNReal.toReal_sum (fun q hq => measure_ne_top μ _),
      ← measure_biUnion_finset hdisjQ (fun q hq => hCells q), ← hcover]
    have h := hpreserve Set.univ
    simpa only [Set.inter_univ] using congrArg ENNReal.toReal h
  let S := Q.filter (fun q => 0 < μ (Cells q))
  have hsumS : (∑ q ∈ S, (μ (Cells q)).toReal) = (μ Set.univ).toReal := by
    rw [← hsum]
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hpos : 0 < μ (Cells q)
    · simp only [ite_eq_left hpos]
    · have hz : μ (Cells q) = 0 := le_antisymm (le_of_not_gt hpos) bot_le
      simp only [hz, ENNReal.toReal_zero, ite_self]
  refine ⟨G, S, hGmeas, hGfull, hGgood, hpreserve, hCells, hdisj,
    (fun q hq => (Finset.mem_filter.mp hq).2), hsumS, ?_⟩
  intro q hq ω hω ω' hω'
  exact Submission.Obl.k4_matching_endpoint_volume.dist_le_mesh_of_gridTag_eq hξ (hω.2.trans hω'.2.symm)

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
