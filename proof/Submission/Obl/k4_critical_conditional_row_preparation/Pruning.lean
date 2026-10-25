import Submission.Lib.K4ReferencePruning
import Submission.Lib.K4ScalarActualSwitching.GridPalette

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section
open MeasureTheory Set
open scoped ENNReal

local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤

/-- Select a member of a finite disjoint measurable cover, with `none` off the cover. -/
def coverLabel {Ω ι : Type*} (E : ι → Set Ω) (p : Ω) : Option ι := by
  classical
  exact if h : ∃ i, p ∈ E i then some (Classical.choose h) else none

theorem coverLabel_eq_some {Ω ι : Type*} (E : ι → Set Ω)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (p : Ω) (i : ι) :
    coverLabel E p = some i ↔ p ∈ E i := by
  classical
  unfold coverLabel
  split_ifs with h
  · constructor
    · intro hi
      have heq := Option.some.inj hi
      simpa only [heq] using Classical.choose_spec h
    · intro hp
      congr 1
      by_contra hn
      exact (Set.disjoint_left.mp (hdisj hn)) (Classical.choose_spec h) hp
  · constructor
    · intro hn; cases hn
    · intro hp; exact (h ⟨i, hp⟩).elim

theorem coverLabel_eq_none {Ω ι : Type*} (E : ι → Set Ω) (p : Ω) :
    coverLabel E p = none ↔ ¬ ∃ i, p ∈ E i := by
  classical
  unfold coverLabel
  split_ifs <;> simp_all

theorem measurable_coverLabel {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Measurable (coverLabel E) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
      have heq : {p | coverLabel E p = none} = (⋃ i, E i)ᶜ := by
        ext p
        simp only [mem_ofPred_eq, coverLabel_eq_none, mem_compl_iff, mem_iUnion]
      simp only [Set.preimage, mem_singleton_iff]
      rw [heq]
      exact (MeasurableSet.iUnion hE).compl
  | some i =>
      have heq : {p | coverLabel E p = some i} = E i := by
        ext p
        exact coverLabel_eq_some E hdisj p i
      simp only [Set.preimage, mem_singleton_iff]
      rw [heq]
      exact hE i

/-- Atom caps against an arbitrary earlier weight give the rectangular cap
needed by original-reference pruning. -/
theorem palette_cap_of_atoms {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (control : Ω → V) (hv : Measurable control) (π : Measure V)
    (w : Q → ENNReal) (C : ENNReal)
    (hcap : ∀ q v, μ {p | state p = q ∧ control p = v} ≤ C * w q * π {v}) :
    ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A := by
  intro q A hA
  have hle : (μ.restrict (state ⁻¹' {q})).map control ≤ (C * w q) • π := by
    apply Submission.Lib.K4ScalarActualSwitching.measure_le_of_countable_atoms
    intro v
    rw [Measure.map_apply hv (measurableSet_singleton v),
      Measure.restrict_apply (hv (measurableSet_singleton v)), Measure.smul_apply, smul_eq_mul]
    convert hcap q v using 1
    congr 1
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, and_comm]
  have hh := hle A
  rw [Measure.map_apply hv hA, Measure.restrict_apply (hv hA),
    Measure.smul_apply, smul_eq_mul] at hh
  convert hh using 1
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, and_comm]

/-- Forgetting any part of a countable state preserves its conditional
palette ceiling. No change of the underlying incidence law is made. -/
theorem coarsen_palette_cap {Ω Q V R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [MeasurableSpace R] [MeasurableSingletonClass R]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (control : Ω → V) (hv : Measurable control) (π : Measure V)
    (f : Q → R) (hf : Measurable f) (C : ENNReal)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * μ (state ⁻¹' {q}) * π A) :
    ∀ r (A : Set V), MeasurableSet A →
      μ {p | f (state p) = r ∧ control p ∈ A} ≤
        C * μ {p | f (state p) = r} * π A := by
  intro r A hA
  have hle : (μ.restrict (control ⁻¹' A)).map state ≤ (C * π A) • μ.map state := by
    apply Submission.Lib.K4ScalarActualSwitching.measure_le_of_countable_atoms
    intro q
    rw [Measure.map_apply hs (measurableSet_singleton q),
      Measure.restrict_apply (hs (measurableSet_singleton q)),
      Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hs (measurableSet_singleton q)]
    simpa only [Set.preimage, Set.inter_def, mem_singleton_iff, mem_ofPred_eq, mul_assoc, mul_left_comm, mul_comm] using hcap q A hA
  have hh := hle (f ⁻¹' {r})
  rw [Measure.map_apply hs (hf (measurableSet_singleton r)),
    Measure.restrict_apply (hs (hf (measurableSet_singleton r))),
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hs (hf (measurableSet_singleton r))] at hh
  simpa only [Set.preimage, Set.inter_def, mem_singleton_iff, mem_ofPred_eq, mul_assoc, mul_left_comm, mul_comm] using hh


/-- A finite family of earlier references, charged only on its possible cells. -/
def historyReference {m : ℕ} {Q : Type*} (options : Fin m → Finset Q)
    (reference : Fin m → ENNReal) (a : Option (Fin m) × Q) : ENNReal := by
  classical
  exact a.1.elim 0 (fun i => if a.2 ∈ options i then reference i else 0)

theorem tsum_historyReference {m : ℕ} {Q : Type*}
    (options : Fin m → Finset Q) (reference : Fin m → ENNReal) :
    ∑' a, historyReference options reference a = ∑ i, (options i).card * reference i := by
  classical
  have hp : (∑' a, historyReference options reference a) =
      ∑' i, ∑' q, historyReference options reference (i, q) := by
    simpa only [historyReference] using (ENNReal.tsum_prod
      (f := fun (i : Option (Fin m)) (q : Q) => historyReference options reference (i, q)))
  rw [hp, tsum_fintype, Fintype.sum_option]
  simp only [historyReference, Option.elim_none, tsum_zero, zero_add, Option.elim_some]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_eq_sum (s := options i) (by intro q hq; simp only [hq, ite_false])]
  simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]

/-- A measurable selector from countably many measurable functions. -/
theorem measurable_select {Ω H X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace H] [Countable H] [MeasurableSingletonClass H] [MeasurableSpace X]
    (label : Ω → H) (hl : Measurable label) (f : H → Ω → X)
    (hf : ∀ h, Measurable (f h)) : Measurable (fun p => f (label p) p) := by
  have hh : Measurable (fun a : Ω × H => f a.2 a.1) :=
    measurable_from_prod_countable_left hf
  exact hh.comp (measurable_id.prodMk hl)

/-- Delete light earlier-history cells, then forget the history while keeping
its conditional palette ceiling and its original mass accounting. -/
theorem prune_and_forget {Ω Q V R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (control : Ω → V) (hv : Measurable control) (π : Measure V)
    (w : Q → ENNReal) (C delta : ENNReal) (hd0 : delta ≠ 0) (hdt : delta ≠ ⊤)
    (f : Q → R) (hf : Measurable f)
    (hcap : ∀ q v, μ {p | state p = q ∧ control p = v} ≤ C * w q * π {v}) :
    ∃ τ : Measure Ω, τ ≤ μ ∧ μ univ ≤ τ univ + delta * ∑' q, w q ∧
      ∀ r v, τ {p | f (state p) = r ∧ control p = v} ≤
        (C / delta) * π {v} * τ {p | f (state p) = r} := by
  let τ := μ.restrict (Submission.Lib.K4ReferencePruning.referenceKeep μ state w delta)
  refine ⟨τ, Measure.restrict_le_self,
    Submission.Lib.K4ReferencePruning.reference_pruning_mass_budget μ state hs w delta, ?_⟩
  have hc := palette_cap_of_atoms μ state hs control hv π w C hcap
  have hp := Submission.Lib.K4ReferencePruning.reference_pruned_palette_cap μ state hs
    control π w C delta hd0 hdt hc
  have hforget := coarsen_palette_cap τ state hs control hv π f hf (C / delta) hp
  intro r v
  simpa only [mem_singleton_iff, mul_assoc, mul_left_comm, mul_comm] using
    hforget r {v} (measurableSet_singleton v)

end
end Submission.Obl.k4_critical_conditional_row_preparation
