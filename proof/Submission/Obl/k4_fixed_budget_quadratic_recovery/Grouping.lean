import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarFormat
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- A finite union concatenates the polynomial tests in its members. -/
theorem fmt_iUnion_fin {k D : ℕ} {B : ℝ} :
    ∀ (n : ℕ) (A : Fin n → Set (Fin k → ℝ)),
      (∀ i, fmt k B D (A i)) → fmt k ((n : ℝ) * B) D (⋃ i, A i) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    simpa only [fmt, Submission.Obl.k4_quadratic_atlas_normalization.fmt, Nat.cast_zero, zero_mul, iUnion_of_empty] using
      Submission.Obl.k4_quadratic_atlas_normalization.fmt_empty k D (H := 0) le_rfl
  | succ n ih =>
    intro A hA
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
    have h := Submission.Obl.k4_quadratic_atlas_normalization.format_union
      (hA 0) (ih (fun i => A i.succ) (fun i => hA i.succ))
    change fmt k (B + (n : ℝ) * B) (max D D) (A 0 ∪ ⋃ i : Fin n, A i.succ) at h
    have hEq : ((n + 1 : ℕ) : ℝ) * B = B + (n : ℝ) * B := by push_cast; ring
    rw [hEq]
    simpa only [max_self, Function.comp_def] using h

/-- Grouping assignments by a fixed finite label map preserves their format budget. -/
theorem fmt_group {k n D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {β : Type*} (label : Fin n → β) (q : β)
    (A : Fin n → Set (Fin k → ℝ)) (hA : ∀ i, fmt k B D (A i)) :
    fmt k ((n : ℝ) * B) D {z | ∃ i, label i = q ∧ z ∈ A i} := by
  classical
  have hselect : ∀ i, fmt k B D (if label i = q then A i else ∅) := by
    intro i
    split_ifs
    · exact hA i
    · exact Submission.Obl.k4_quadratic_atlas_normalization.fmt_empty k D hB
  have h := fmt_iUnion_fin n _ hselect
  convert h using 1
  ext z
  simp

/-- Clipping to the original coefficient bound prevents coefficient rounding from
amplifying the fitting error on trajectories outside the input support. -/
def coefficientBox (R : ℝ) : Set (Fin 5 → ℝ) := {z | ∀ i, |z i| ≤ R}

theorem coefficientBox_format (R : ℝ) : fmt 5 10 1 (coefficientBox R) := by
  have h := Submission.Obl.k4_dk4_smoothed_problem.HasBoolPolynomialFormat.coordinate_box
    (id : (Fin 5 → ℝ) → Fin 5 → ℝ) (fun _ => -R) (fun _ => R)
  have heq : coefficientBox R = Icc (fun _ : Fin 5 => -R) (fun _ => R) := by
    ext z
    simp only [coefficientBox, mem_ofPred_eq, mem_Icc, Pi.le_def, abs_le]
    exact forall_and
  rw [heq]
  exact fmt_of_hasBoolFormat h

def groupedAssignment {n : ℕ} {β : Type*} (R : ℝ)
    (label : Fin n → β) (A : Fin n → Set (Fin 5 → ℝ)) (q : β) : Set (Fin 5 → ℝ) :=
  coefficientBox R ∩ {z | ∃ i, label i = q ∧ z ∈ A i}

theorem groupedAssignment_format {n D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {β : Type*} (R : ℝ) (label : Fin n → β)
    (A : Fin n → Set (Fin 5 → ℝ)) (hA : ∀ i, fmt 5 B D (A i)) (q : β) :
    fmt 5 (10 + (n : ℝ) * B) (max 1 D) (groupedAssignment R label A q) := by
  exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
    (coefficientBox_format R) (fmt_group hB label q A hA)

theorem groupedAssignment_measurable {n D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {β : Type*} (R : ℝ) (label : Fin n → β)
    (A : Fin n → Set (Fin 5 → ℝ)) (hA : ∀ i, fmt 5 B D (A i)) (q : β) :
    MeasurableSet (groupedAssignment R label A q) :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.measurableSet
    (groupedAssignment_format hB R label A hA q)

theorem groupedAssignment_disjoint {n : ℕ} {β : Type*} (R : ℝ)
    (label : Fin n → β) (A : Fin n → Set (Fin 5 → ℝ))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Pairwise (fun q q' => Disjoint (groupedAssignment R label A q)
      (groupedAssignment R label A q')) := by
  intro q q' hqq'
  apply Set.disjoint_left.mpr
  rintro z ⟨_, i, hi, hz⟩ ⟨_, j, hj, hz'⟩
  by_cases hij : i = j
  · subst j
    exact hqq' (hi.symm.trans hj)
  · exact Set.disjoint_left.mp (hA hij) hz hz'

/-- The occupied labels can be enumerated without increasing the number of tests. -/
theorem enumerate_occupied_labels {n : ℕ} {β : Type*} (label : Fin n → β) :
    ∃ (k : ℕ) (q : Fin k → β), k ≤ n ∧ Function.Injective q ∧
      ∀ b, (∃ i, label i = b) ↔ ∃ j, q j = b := by
  classical
  let S := Finset.univ.image label
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun j => (e j).val, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := label))
  · exact Subtype.val_injective.comp e.injective
  · intro b
    constructor
    · rintro ⟨i, rfl⟩
      let b : S := ⟨label i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      exact ⟨e.symm b, congrArg Subtype.val (e.apply_symm_apply b)⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e j).property
      exact ⟨i, hi⟩

/-- Pulling lists back along an injective finite label enumeration keeps their size. -/
theorem reindex_lists {β X : Type*} [DecidableEq β] [MeasurableSpace X]
    {k M : ℕ} (q : Fin k → β) (hq : Function.Injective q) (L : X → Finset β)
    (hL : ∀ x, (L x).card ≤ M) (hLm : ∀ b, MeasurableSet {x | b ∈ L x}) :
    ∃ K : X → Finset (Fin k),
      (∀ x i, i ∈ K x ↔ q i ∈ L x) ∧ (∀ x, (K x).card ≤ M) ∧
      ∀ i, MeasurableSet {x | i ∈ K x} := by
  classical
  let K : X → Finset (Fin k) := fun x => Finset.univ.filter (fun i => q i ∈ L x)
  refine ⟨K, fun x i => by simp [K], ?_, ?_⟩
  · intro x
    have hsub : (K x).image q ⊆ L x := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact (Finset.mem_filter.mp hi).2
    calc
      _ = ((K x).image q).card := (Finset.card_image_of_injective _ hq).symm
      _ ≤ (L x).card := Finset.card_le_card hsub
      _ ≤ M := hL x
  · intro i
    simpa only [K, Finset.mem_filter, Finset.mem_univ, true_and] using hLm (q i)

end Submission.Obl.k4_fixed_budget_quadratic_recovery
