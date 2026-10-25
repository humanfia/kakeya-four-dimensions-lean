import Submission.Obl.k4_paired_full_time_binning.Geometry

namespace Submission.Obl.k4_paired_full_time_binning

noncomputable section

open Finset

/-- The coordinate cube with integer radius three. -/
def cube (q : Code) : Finset Code :=
  Fintype.piFinset (fun k => Finset.Icc (q k - 3) (q k + 3))

def nearby (q : Code) : Finset Code := cube q ∪ cube (-q)

lemma card_cube (q : Code) : (cube q).card = 2401 := by
  have h (k : Fin 4) : (Finset.Icc (q k - 3) (q k + 3)).card = 7 := by
    rw [Int.card_Icc]
    omega
  simp [cube, h]

lemma card_nearby (q : Code) : (nearby q).card ≤ 4802 := by
  exact (Finset.card_union_le _ _).trans (by rw [card_cube, card_cube])

lemma floor_error (G x : ℝ) : |(⌊x / G⌋ : ℝ) - x / G| ≤ 1 :=
  Submission.Obl.k4_scalar_lift_plank.abs_floor_sub _

lemma floor_sub_bound {G x y : ℝ} (hG : 0 < G) (h : |x - y| ≤ G) :
    |(⌊x / G⌋ : ℝ) - (⌊y / G⌋ : ℝ)| ≤ 3 := by
  have hxy : |x / G - y / G| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hG]
    exact (div_le_one hG).mpr h
  calc
    _ = |((⌊x / G⌋ : ℝ) - x / G) + (x / G - y / G) -
        ((⌊y / G⌋ : ℝ) - y / G)| := by congr 1; ring
    _ ≤ |(⌊x / G⌋ : ℝ) - x / G| + |x / G - y / G| +
        |(⌊y / G⌋ : ℝ) - y / G| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 := by linarith [floor_error G x, floor_error G y]

lemma floor_add_bound {G x y : ℝ} (hG : 0 < G) (h : |x + y| ≤ G) :
    |(⌊x / G⌋ : ℝ) + (⌊y / G⌋ : ℝ)| ≤ 3 := by
  have hxy : |x / G + y / G| ≤ 1 := by
    rw [← add_div, abs_div, abs_of_pos hG]
    exact (div_le_one hG).mpr h
  calc
    _ = |((⌊x / G⌋ : ℝ) - x / G) + (x / G + y / G) +
        ((⌊y / G⌋ : ℝ) - y / G)| := by congr 1; ring
    _ ≤ |(⌊x / G⌋ : ℝ) - x / G| + |x / G + y / G| +
        |(⌊y / G⌋ : ℝ) - y / G| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 := by linarith [floor_error G x, floor_error G y]

lemma code_mem_nearby {G : ℝ} (hG : 0 < G) {x y : Record}
    (h : (∀ k, |x k - y k| ≤ G) ∨ (∀ k, |x k + y k| ≤ G)) :
    code G x ∈ nearby (code G y) := by
  rcases h with h | h
  · apply Finset.mem_union.mpr; left
    apply Fintype.mem_piFinset.mpr
    intro k
    have hh := abs_le.mp (floor_sub_bound hG (h k))
    change ⌊x k / G⌋ ∈ Finset.Icc (⌊y k / G⌋ - 3) (⌊y k / G⌋ + 3)
    rw [Finset.mem_Icc]
    have hh' : -(3 : ℤ) ≤ ⌊x k / G⌋ - ⌊y k / G⌋ ∧
        ⌊x k / G⌋ - ⌊y k / G⌋ ≤ 3 := by exact_mod_cast hh
    omega
  · apply Finset.mem_union.mpr; right
    apply Fintype.mem_piFinset.mpr
    intro k
    have hh := abs_le.mp (floor_add_bound hG (h k))
    change ⌊x k / G⌋ ∈ Finset.Icc (-⌊y k / G⌋ - 3) (-⌊y k / G⌋ + 3)
    rw [Finset.mem_Icc]
    have hh' : -(3 : ℤ) ≤ ⌊x k / G⌋ + ⌊y k / G⌋ ∧
        ⌊x k / G⌋ + ⌊y k / G⌋ ≤ 3 := by exact_mod_cast hh
    omega

lemma card_codes {n : ℕ} (x : Fin n → Record) {G K : ℝ}
    (hG : 0 < G) (hG1 : G ≤ 1) (hK : 1 ≤ K)
    (hx : ∀ i k, |x i k| ≤ K) :
    ((Finset.univ.image (fun i => code G (x i))).card : ℝ) ≤ (7 * K / G) ^ 4 := by
  let Q := Submission.Obl.k4_scalar_lift_plank.coordinateBins G K
  have hsub : Finset.univ.image (fun i => code G (x i)) ⊆
      Fintype.piFinset (fun _ : Fin 4 => Q) := by
    rintro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact Fintype.mem_piFinset.mpr fun k =>
      Submission.Obl.k4_scalar_lift_plank.mem_coordinateBins hG hG1 hK (hx i k)
  calc
    _ ≤ ((Fintype.piFinset (fun _ : Fin 4 => Q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = (Q.card : ℝ) ^ 4 := by simp
    _ ≤ _ := by
      gcongr
      exact Submission.Obl.k4_scalar_lift_plank.card_coordinateBins_le hG hG1 hK

/-- Choose exactly one original label in each occupied bin. -/
lemma representatives {n : ℕ} (f : Fin n → Code) :
    ∃ (m : ℕ) (rep : Fin m → Fin n),
      m = (Finset.univ.image f).card ∧
      Function.Injective (fun i => f (rep i)) ∧ ∀ j, ∃ i, f (rep i) = f j := by
  classical
  let Q := Finset.univ.image f
  let e : Fin Q.card ≃ Q := Q.equivFin.symm
  have hex (i : Fin Q.card) : ∃ j, f j = (e i).1 := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (e i).2
    exact ⟨j, hj⟩
  let rep : Fin Q.card → Fin n := fun i => Classical.choose (hex i)
  have hrep (i : Fin Q.card) : f (rep i) = (e i).1 := Classical.choose_spec (hex i)
  refine ⟨Q.card, rep, rfl, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext (by simpa only [← hrep] using hij)
  · intro j
    let q : Q := ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    refine ⟨e.symm q, ?_⟩
    rw [hrep, e.apply_symm_apply]

/-- Filter a finite enumeration of distinct bins using the original observation list. -/
def observationList {m n : ℕ} (f : Fin m → Code) (label : Fin n → Code)
    (s : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ j ∈ s, f i ∈ nearby (label j))

lemma mem_observationList {m n : ℕ} (f : Fin m → Code) (label : Fin n → Code)
    (s : Finset (Fin n)) (i : Fin m) :
    i ∈ observationList f label s ↔ ∃ j ∈ s, f i ∈ nearby (label j) := by
  simp [observationList]

lemma card_observationList {m n : ℕ} (f : Fin m → Code) (label : Fin n → Code)
    (hf : Function.Injective f) (s : Finset (Fin n)) :
    (observationList f label s).card ≤ 4802 * s.card := by
  classical
  calc
    _ ≤ (s.biUnion (fun j => nearby (label j))).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        obtain ⟨j, hj, hi⟩ := (mem_observationList f label s i).mp hi
        exact Finset.mem_biUnion.mpr ⟨j, hj, hi⟩
      · exact hf.injOn
    _ ≤ ∑ j ∈ s, (nearby (label j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ s, 4802 := Finset.sum_le_sum (fun j _ => card_nearby (label j))
    _ = _ := by simp [Nat.mul_comm]

lemma measurable_observationList {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (f : Fin m → Code) (label : Fin n → Code) (lst : Ω → Finset (Fin n))
    (hlst : ∀ j, MeasurableSet {o | j ∈ lst o}) (i : Fin m) :
    MeasurableSet {o | i ∈ observationList f label (lst o)} := by
  simp_rw [mem_observationList, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun j => (hlst j).inter
    (MeasurableSet.const _))

end

end Submission.Obl.k4_paired_full_time_binning
