/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/FinitePairLaw.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Mathlib

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.FinitePairLaw

open MeasureTheory Set

variable {ι X : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace X]

def row (H : ι → ι → Set X) (i : ι) : Set X := ⋃ j, H i j

def active (H : ι → ι → Set X) : Set (ι × X) := {p | p.2 ∈ row H p.1}

theorem measurableSet_row (H : ι → ι → Set X) (hH : ∀ i j, MeasurableSet (H i j))
    (i : ι) : MeasurableSet (row H i) := MeasurableSet.iUnion (hH i)

theorem measurableSet_active (H : ι → ι → Set X) (hH : ∀ i j, MeasurableSet (H i j)) :
    MeasurableSet (active H) := by
  have heq : active H = ⋃ i, {i} ×ˢ row H i := by
    ext p
    simp [active]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod
    (measurableSet_row H hH i))

/-- Each source retains its original measure and scalar weight. -/
noncomputable def law (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X) :
    Measure (ι × X) :=
  ∑ i, ENNReal.ofReal (a i) • ((μ i).restrict (row H i)).map (fun x => (i, x))

theorem law_apply (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (A : Set (ι × X)) :
    law μ a H A = ∑ i, ENNReal.ofReal (a i) * μ i
      ((fun x => (i, x)) ⁻¹' A ∩ row H i) := by
  simp only [law, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(measurableEmbedding_prodMk_left i).map_apply,
    Measure.restrict_apply' (measurableSet_row H hH i)]

/-- The same finite law, with its pointwise support built into the type. -/
noncomputable def supportedLaw (μ : ι → Measure X) (a : ι → ℝ)
    (H : ι → ι → Set X) : Measure (active H) :=
  (law μ a H).comap (Subtype.val : active H → ι × X)

theorem supportedLaw_apply (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (A : Set (active H)) :
    supportedLaw μ a H A = ∑ i, ENNReal.ofReal (a i) *
      μ i ((fun x => (i, x)) ⁻¹' (Subtype.val '' A)) := by
  rw [supportedLaw, comap_subtype_coe_apply (measurableSet_active H hH),
    law_apply μ a H hH]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply inter_eq_left.mpr
  rintro x ⟨p, hp, heq⟩
  have hmem := p.property
  change p.val.2 ∈ row H p.val.1 at hmem
  rw [heq] at hmem
  exact hmem

theorem supportedLaw_univ (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) :
    supportedLaw μ a H univ = ∑ i, ENNReal.ofReal (a i) * μ i (row H i) := by
  rw [supportedLaw_apply μ a H hH]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext x
  simp [Subtype.range_coe, active]

theorem supportedLaw_finite (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (hfinite : ∀ i, μ i (row H i) ≠ ⊤) :
    IsFiniteMeasure (supportedLaw μ a H) := by
  constructor
  rw [supportedLaw_univ μ a H hH]
  exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (hfinite i)))

theorem supportedLaw_bound (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (A : Set (active H)) (K : ι → Set X)
    (hK : ∀ p ∈ A, p.val.2 ∈ K p.val.1) :
    supportedLaw μ a H A ≤ ∑ i, ENNReal.ofReal (a i) * μ i (K i) := by
  rw [supportedLaw_apply μ a H hH]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro x ⟨p, hp, heq⟩
  have := hK p hp
  simpa only [heq] using this

def source (H : ι → ι → Set X) (p : active H) : ι := p.val.1

def point (H : ι → ι → Set X) (p : active H) : X := p.val.2

theorem measurable_source (H : ι → ι → Set X) : Measurable (source H) :=
  measurable_fst.comp measurable_subtype_coe

theorem measurable_point (H : ι → ι → Set X) : Measurable (point H) :=
  measurable_snd.comp measurable_subtype_coe

theorem source_bound (μ : ι → Measure X) (a : ι → ℝ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (i : ι) (U : Set X) :
    supportedLaw μ a H {p | source H p = i ∧ point H p ∈ U} ≤
      ENNReal.ofReal (a i) * μ i (row H i ∩ U) := by
  classical
  have hb := supportedLaw_bound μ a H hH {p | source H p = i ∧ point H p ∈ U}
    (fun j => if j = i then row H i ∩ U else ∅) (by
      intro p hp
      rw [show p.val.1 = i from hp.1, if_pos rfl]
      exact ⟨by simpa only [source] using hp.1 ▸ p.property, hp.2⟩)
  simpa [apply_ite] using hb

/-- Source masks in one frame are charged as a union under that frame's
unchanged measure. -/
theorem frame_bound {Φ : Type*} (ν : Φ → Measure X) (b : Φ → ℝ)
    (frame : ι → Φ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j))
    (hdisj : ∀ i i', i ≠ i' → frame i = frame i' → Disjoint (row H i) (row H i'))
    (f : Φ) (U : Set X) (hU : MeasurableSet U) :
    supportedLaw (fun i => ν (frame i)) (fun i => b (frame i)) H
      {p | frame (source H p) = f ∧ point H p ∈ U} ≤
      ENNReal.ofReal (b f) * ν f ((⋃ i, ⋃ (_ : frame i = f), row H i) ∩ U) := by
  classical
  let I : Finset ι := Finset.univ.filter (fun i => frame i = f)
  have hb := supportedLaw_bound (fun i => ν (frame i)) (fun i => b (frame i)) H hH
    {p | frame (source H p) = f ∧ point H p ∈ U}
    (fun i => if frame i = f then row H i ∩ U else ∅) (by
      intro p hp
      have hpf : frame p.val.1 = f := hp.1
      rw [if_pos hpf]
      exact ⟨p.property, hp.2⟩)
  refine hb.trans (le_of_eq ?_)
  have heq : (∑ i, ENNReal.ofReal (b (frame i)) *
      ν (frame i) (if frame i = f then row H i ∩ U else ∅)) =
      ∑ i ∈ I, ENNReal.ofReal (b f) * ν f (row H i ∩ U) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [hi]
    · simp
  rw [heq, ← Finset.mul_sum]
  congr 1
  have hdi : Set.PairwiseDisjoint (↑I) (fun i => row H i ∩ U) := by
    intro i hi i' hi' hii'
    have hfi := (Finset.mem_filter.mp hi).2
    have hfi' := (Finset.mem_filter.mp hi').2
    exact (hdisj i i' hii' (hfi.trans hfi'.symm)).mono inter_subset_left inter_subset_left
  rw [← measure_biUnion_finset hdi (fun i _ => (measurableSet_row H hH i).inter hU)]
  congr 1
  ext x
  simp only [mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_inter_iff]
  aesop

section Witness

variable [LinearOrder ι]

noncomputable def witness (H : ι → ι → Set X) (p : active H) : ι := by
  classical
  exact (Finset.univ.filter (fun j => point H p ∈ H (source H p) j)).min' (by
    have hp := p.property
    change p.val.2 ∈ ⋃ j, H p.val.1 j at hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

theorem witness_mem (H : ι → ι → Set X) (p : active H) :
    point H p ∈ H (source H p) (witness H p) := by
  classical
  let J := Finset.univ.filter (fun j => point H p ∈ H (source H p) j)
  have hJ : J.Nonempty := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp p.property
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem J hJ)).2

theorem witness_le (H : ι → ι → Set X) (p : active H) {j : ι}
    (hj : point H p ∈ H (source H p) j) : witness H p ≤ j := by
  classical
  exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

theorem witness_eq_iff (H : ι → ι → Set X) (p : active H) (j : ι) :
    witness H p = j ↔ point H p ∈ H (source H p) j ∧
      ∀ k, k < j → point H p ∉ H (source H p) k := by
  constructor
  · intro heq
    refine ⟨heq ▸ witness_mem H p, ?_⟩
    intro k hkj hk
    have := witness_le H p hk
    rw [heq] at this
    exact (not_le_of_gt hkj) this
  · rintro ⟨hj, hmin⟩
    apply le_antisymm (witness_le H p hj)
    by_contra h
    exact hmin (witness H p) (lt_of_not_ge h) (witness_mem H p)

theorem measurableSet_witness_eq (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j)) (j : ι) :
    MeasurableSet {p : active H | witness H p = j} := by
  have heq : {p : active H | witness H p = j} = ⋃ i,
      {p | source H p = i} ∩ ((point H) ⁻¹' H i j ∩
        ⋂ k, ⋂ (_ : k < j), ((point H) ⁻¹' H i k)ᶜ) := by
    ext p
    simp only [mem_setOf_eq, witness_eq_iff, mem_iUnion, mem_inter_iff,
      mem_preimage, mem_iInter, mem_compl_iff]
    constructor
    · rintro ⟨hj, hmin⟩
      exact ⟨source H p, rfl, hj, hmin⟩
    · rintro ⟨i, hi, hj, hmin⟩
      simpa only [hi] using (And.intro hj hmin)
  rw [heq]
  refine MeasurableSet.iUnion (fun i => ?_)
  exact ((measurable_source H) (measurableSet_singleton i)).inter
    (((hH i j).preimage (measurable_point H)).inter
      (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
        ((hH i k).preimage (measurable_point H)).compl))))

/-- The witness marginal uses the original union over source masks. Pairwise
disjoint source assignments remove the source count from this estimate. -/
theorem witness_bound {Φ : Type*} (ν : Φ → Measure X) (b : Φ → ℝ)
    (frame : ι → Φ) (H : ι → ι → Set X)
    (hH : ∀ i j, MeasurableSet (H i j))
    (hcompat : ∀ i j x, x ∈ H i j → frame i = frame j)
    (hdisj : ∀ j, Pairwise (fun i i' => Disjoint (H i j) (H i' j)))
    (j : ι) (U : Set X) (hU : MeasurableSet U) :
    supportedLaw (fun i => ν (frame i)) (fun i => b (frame i)) H
      {p | witness H p = j ∧ point H p ∈ U} ≤
      ENNReal.ofReal (b (frame j)) * ν (frame j) ((⋃ i, H i j) ∩ U) := by
  classical
  have hb := supportedLaw_bound (fun i => ν (frame i)) (fun i => b (frame i)) H hH
    {p | witness H p = j ∧ point H p ∈ U} (fun i => H i j ∩ U) (by
      intro p hp
      exact ⟨hp.1 ▸ witness_mem H p, hp.2⟩)
  refine hb.trans (le_of_eq ?_)
  have hterm (i : ι) : ENNReal.ofReal (b (frame i)) * ν (frame i) (H i j ∩ U) =
      ENNReal.ofReal (b (frame j)) * ν (frame j) (H i j ∩ U) := by
    by_cases heq : frame i = frame j
    · rw [heq]
    · have hempty : H i j = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact heq (hcompat i j x hx)
      simp [hempty]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hdi : Pairwise (fun i i' => Disjoint (H i j ∩ U) (H i' j ∩ U)) := by
    intro i i' hii'
    exact (hdisj j hii').mono inter_subset_left inter_subset_left
  have hsum : ν (frame j) (⋃ i ∈ (Finset.univ : Finset ι), H i j ∩ U) =
      ∑ i ∈ (Finset.univ : Finset ι), ν (frame j) (H i j ∩ U) := by
    apply measure_biUnion_finset
    · intro i _ i' _ hii'
      exact hdi hii'
    · intro i _
      exact (hH i j).inter hU
  simp only [Finset.mem_univ, iUnion_true] at hsum
  rw [← hsum]
  congr 1
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  aesop

end Witness

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.FinitePairLaw
