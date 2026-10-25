import Mathlib

/-
Adapted from this LOT tree, o178, session x0596, `PairBound.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Union bound for the paired law of two times on the same trajectory

The paired law `ν ⊗ (dt ⊗ dt)` of a set of pairs whose first time lies in a
block and whose second incidence lies in a measurable set `W` is at most
`|block| · (ν ⊗ dt)(W)`.  A bad-pair set covered by finitely many such
products is bounded by the corresponding sum.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory

noncomputable section

variable {L : Type*} [MeasurableSpace L]

theorem pair_block_le (ν : Measure L) [SFinite ν]
    (blk : Set ℝ) (W : Set (L × ℝ)) (hW : MeasurableSet W) :
    (ν.prod (volume.prod volume)) {z : L × (ℝ × ℝ) | z.2.1 ∈ blk ∧ (z.1, z.2.2) ∈ W} ≤
      volume blk * (ν.prod volume) W := by
  -- reduce to a measurable block
  set blk' := toMeasurable volume blk with hblk'
  have hb'm : MeasurableSet blk' := measurableSet_toMeasurable _ _
  have hsub : {z : L × (ℝ × ℝ) | z.2.1 ∈ blk ∧ (z.1, z.2.2) ∈ W} ⊆
      {z : L × (ℝ × ℝ) | z.2.1 ∈ blk' ∧ (z.1, z.2.2) ∈ W} := by
    intro z hz
    exact ⟨subset_toMeasurable _ _ hz.1, hz.2⟩
  have hm : MeasurableSet {z : L × (ℝ × ℝ) | z.2.1 ∈ blk' ∧ (z.1, z.2.2) ∈ W} := by
    refine (hb'm.preimage (measurable_fst.comp measurable_snd)).inter ?_
    exact hW.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  refine (measure_mono hsub).trans ?_
  rw [Measure.prod_apply hm, Measure.prod_apply hW, ← measure_toMeasurable blk, ← hblk',
    ← lintegral_const_mul _ (measurable_measure_prodMk_left hW)]
  apply le_of_eq
  congr 1
  funext l
  have hsec : Prod.mk l ⁻¹' {z : L × (ℝ × ℝ) | z.2.1 ∈ blk' ∧ (z.1, z.2.2) ∈ W} =
      blk' ×ˢ (Prod.mk l ⁻¹' W) := by
    ext ⟨t₁, t₂⟩
    simp
  rw [hsec, Measure.prod_prod]

/-- **Union bound over first labels.** -/
theorem pair_bad_le_sum {ι : Type*} [Fintype ι] (ν : Measure L) [SFinite ν]
    (E : Set (L × ℝ)) (Bad : Set (L × (ℝ × ℝ)))
    (blk : ι → Set ℝ) (Z : ι → Set (L × ℝ)) (hZ : ∀ i, MeasurableSet (Z i))
    (hE : MeasurableSet E)
    (hcover : ∀ z ∈ Bad, ∃ i, z.2.1 ∈ blk i ∧ (z.1, z.2.2) ∈ Z i ∧ (z.1, z.2.2) ∈ E) :
    (ν.prod (volume.prod volume)) Bad ≤
      ∑ i, volume (blk i) * ((ν.prod volume).restrict E) (Z i) := by
  have hsub : Bad ⊆ ⋃ i, {z : L × (ℝ × ℝ) | z.2.1 ∈ blk i ∧ (z.1, z.2.2) ∈ Z i ∩ E} := by
    intro z hz
    obtain ⟨i, h1, h2, h3⟩ := hcover z hz
    exact Set.mem_iUnion.2 ⟨i, h1, h2, h3⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  gcongr with i
  rw [Measure.restrict_apply (hZ i)]
  exact pair_block_le ν (blk i) (Z i ∩ E) ((hZ i).inter hE)

end

end Submission.Obl.k4_raw_localized_native_systems.C
