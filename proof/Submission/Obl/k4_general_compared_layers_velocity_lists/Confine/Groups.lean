-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Groups; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Support
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.PoolSetup

/-!
# Physical native-signal groups at one intermediate depth

Given two groups `E i 0`, `E i 1` on every true block `i` of one depth `s`, a physical
incidence gets the group `1` when it lies in a group `1` of some block, and `0` otherwise.
The physical bad set collects the dyadic times of level `T k s`, the incidences outside
every true block and the incidences of a block outside both of its groups. Off the bad set,
an incidence of the trajectory class and dyadic interval of a block `h` lies in the group of
`h` named by its physical group.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation (dyadic_Ico_disjoint)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- The dyadic times of level `T`. -/
def dyadicTimes (T : ℕ) : Set ℝ := range (fun n : ℕ => (n : ℝ) / 2 ^ T)

theorem countable_dyadicTimes (T : ℕ) : (dyadicTimes T).Countable := countable_range _

/-- A time of a dyadic block which is not a dyadic time lies before the end of the block. -/
theorem mem_Ico_of_mem_block {T : ℕ} {j : Fin (2 ^ T)} {τ : ℝ} (hτ : τ ∈ block T j)
    (hD : τ ∉ dyadicTimes T) :
    τ ∈ Ico (((j : ℕ) : ℝ) / 2 ^ T) ((((j : ℕ) : ℝ) + 1) / 2 ^ T) := by
  have h1 : ((j : ℕ) : ℝ) / 2 ^ T ≤ τ ∧ τ ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := hτ
  refine ⟨h1.1, lt_of_le_of_ne h1.2 ?_⟩
  intro heq
  apply hD
  refine ⟨(j : ℕ) + 1, ?_⟩
  rw [heq]
  push_cast
  ring

omit [MeasurableSpace α] in
/-- Two true blocks of one depth sharing a trajectory and a non-dyadic time coincide. -/
theorem block_eq_of_mem {n T : ℕ} {A : Fin n → Set α} {j : Fin n → Fin (2 ^ T)}
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    {i i' : Fin n} {l : α} {τ : ℝ} (hl : l ∈ A i) (hl' : l ∈ A i')
    (hτ : τ ∈ block T (j i)) (hτ' : τ ∈ block T (j i')) (hD : τ ∉ dyadicTimes T) :
    i = i' := by
  by_contra hne
  by_cases hj : j i = j i'
  · exact Set.disjoint_left.mp (hdisj i i' hne hj) hl hl'
  · have hj' : ((j i : ℕ)) ≠ (j i' : ℕ) := fun h => hj (Fin.ext h)
    exact Set.disjoint_left.mp (dyadic_Ico_disjoint (T := T) hj')
      (mem_Ico_of_mem_block hτ hD) (mem_Ico_of_mem_block hτ' hD)

/-- The physical group of an incidence: `1` when it lies in a group `1` of some block. -/
def physGrp {ι : Type} (E : ι → Fin 2 → Set (α × ℝ)) (z : α × ℝ) : Fin 2 := by
  classical
  exact if z ∈ ⋃ i, E i 1 then 1 else 0

/-- The physical bad set at depth `s`: dyadic times of level `T k s`, incidences outside
every true block, and incidences of a block outside both of its groups. -/
def physBad (p : Parent α) (k : ℕ) (s : ℝ) (E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)) :
    Set (α × ℝ) :=
  ({z | z.2 ∈ dyadicTimes (p.T k s)} ∪
    (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) ∪
    ⋃ i, ((p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e)

theorem measurable_physGrp {ι : Type} [Countable ι] {E : ι → Fin 2 → Set (α × ℝ)}
    (hE : ∀ i e, MeasurableSet (E i e)) : Measurable (physGrp E) := by
  classical
  unfold physGrp
  exact Measurable.ite (MeasurableSet.iUnion fun i => hE i 1) measurable_const measurable_const

theorem measurableSet_dyadic (T : ℕ) :
    MeasurableSet {z : α × ℝ | z.2 ∈ dyadicTimes T} :=
  measurable_snd (countable_dyadicTimes T).measurableSet

theorem measurableSet_physBad {p : Parent α} {k : ℕ} {s : ℝ}
    {E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)} (hB : ∀ i, MeasurableSet (p.B k s i))
    (hE : ∀ i e, MeasurableSet (E i e)) : MeasurableSet (p.physBad k s E) := by
  have hP : ∀ i, MeasurableSet (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) :=
    fun i => (hB i).prod measurableSet_Icc
  exact ((measurableSet_dyadic _).union (MeasurableSet.iUnion hP).compl).union
    (MeasurableSet.iUnion fun i => (hP i).diff (MeasurableSet.iUnion fun e => hE i e))

/-- **The group property.** Off the physical bad set, an incidence in the trajectory class
and the dyadic interval of a block `h` lies in the group of `h` named by its physical
group. -/
theorem mem_physGrp {p : Parent α} {k : ℕ} {s : ℝ}
    {E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)}
    (hBA : ∀ i, p.B k s i ⊆ p.A k s i)
    (hdisj : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' → Disjoint (p.A k s i) (p.A k s i'))
    (hEsub : ∀ i e, E i e ⊆ p.B k s i ×ˢ block (p.T k s) (p.j k s i))
    {h : Fin (p.n k s)} {z : α × ℝ} (hzA : z.1 ∈ p.A k s h)
    (hzI : z.2 ∈ block (p.T k s) (p.j k s h)) (hz : z ∉ p.physBad k s E) :
    z ∈ E h (physGrp E z) := by
  classical
  have hD : z.2 ∉ dyadicTimes (p.T k s) := fun hd => hz (Or.inl (Or.inl hd))
  have hcov : z ∈ ⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i) := by
    by_contra hc
    exact hz (Or.inl (Or.inr hc))
  have hL : ∀ i, z ∉ (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e :=
    fun i hi => hz (Or.inr (mem_iUnion.mpr ⟨i, hi⟩))
  have huniq : ∀ i, z ∈ p.B k s i ×ˢ block (p.T k s) (p.j k s i) → i = h := fun i hi =>
    block_eq_of_mem hdisj (hBA i hi.1) hzA hi.2 hzI hD
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcov
  have hih := huniq i hi
  subst hih
  have hE : ∃ e, z ∈ E i e := by
    by_contra hne
    refine hL i ⟨hi, fun hU => ?_⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hU
    exact hne ⟨e, he⟩
  unfold physGrp
  split_ifs with h1
  · obtain ⟨i', hi'⟩ := mem_iUnion.mp h1
    have := huniq i' (hEsub i' 1 hi')
    subst this
    exact hi'
  · obtain ⟨e, he⟩ := hE
    fin_cases e
    · exact he
    · exact absurd (mem_iUnion.mpr ⟨i, he⟩) h1

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
