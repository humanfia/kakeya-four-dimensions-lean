import Submission.Obl.k4_scalar_pair_atlas_assembly.Interface
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

def width (T : ℕ) : ℝ := ((2 : ℝ) ^ T)⁻¹
lemma width_pos (T : ℕ) : 0 < width T := by unfold width; positivity
lemma I_eq (T : ℕ) (j : Fin (2 ^ T)) :
    I T j = Icc ((j : ℝ) * width T) (((j : ℝ) + 1) * width T) := by
  rfl
lemma volume_I (T : ℕ) (j : Fin (2 ^ T)) : volume (I T j) = ENNReal.ofReal (width T) := by
  rw [I_eq, Real.volume_Icc]
  congr 1
  ring
lemma mem_I_left (T : ℕ) (j : Fin (2 ^ T)) : (j : ℝ) * width T ∈ I T j := by
  rw [I_eq]
  exact ⟨le_rfl, by nlinarith [width_pos T]⟩
lemma mem_I_right (T : ℕ) (j : Fin (2 ^ T)) : ((j : ℝ) + 1) * width T ∈ I T j := by
  rw [I_eq]
  exact ⟨by nlinarith [width_pos T], le_rfl⟩
lemma pow_split {t T : ℕ} (ht : t ≤ T) :
    2 ^ T = 2 ^ t * 2 ^ (T - t) := by
  rw [← pow_add, Nat.add_sub_of_le ht]

def child {t T : ℕ} (ht : t ≤ T) (b : Fin (2 ^ t)) (r : Fin (2 ^ (T-t))) :
    Fin (2 ^ T) :=
  ⟨b.val * 2 ^ (T-t) + r.val, by
    rw [pow_split ht]
    nlinarith [b.isLt, r.isLt, Nat.two_pow_pos (T-t)]⟩
lemma width_split {t T : ℕ} (ht : t ≤ T) :
    (2 : ℝ) ^ (T-t) * width T = width t := by
  unfold width
  rw [show (2 : ℝ) ^ T = 2 ^ t * 2 ^ (T-t) by rw [← pow_add, Nat.add_sub_of_le ht]]
  field_simp
lemma child_interval_subset {t T : ℕ} (ht : t ≤ T)
    (b : Fin (2 ^ t)) (r : Fin (2 ^ (T-t))) : I T (child ht b r) ⊆ I t b := by
  rw [I_eq, I_eq]
  apply Icc_subset_Icc
  · change (b : ℝ) * width t ≤ ((b.val * 2 ^ (T-t) + r.val : ℕ) : ℝ) * width T
    push_cast
    rw [← width_split ht]
    nlinarith [show (0 : ℝ) ≤ (r.val : ℝ) from Nat.cast_nonneg _, width_pos T]
  · change (((b.val * 2 ^ (T-t) + r.val : ℕ) : ℝ) + 1) * width T ≤
      ((b : ℝ) + 1) * width t
    push_cast
    rw [← width_split ht]
    have hr : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (T-t) := by exact_mod_cast r.isLt
    nlinarith [width_pos T]

lemma exists_child_of_subset {t T : ℕ} (ht : t ≤ T) (b : Fin (2 ^ t))
    (j : Fin (2 ^ T)) (hj : I T j ⊆ I t b) :
    ∃ r : Fin (2 ^ (T-t)), j = child ht b r := by
  have hl := (hj (mem_I_left T j)).1
  have hu := (hj (mem_I_right T j)).2
  change (b : ℝ) * width t ≤ (j : ℝ) * width T at hl
  change ((j : ℝ) + 1) * width T ≤ ((b : ℝ) + 1) * width t at hu
  have hw := width_pos T
  rw [← width_split ht] at hl hu
  have hl' : b.val * 2 ^ (T-t) ≤ j.val := by
    have : (b : ℝ) * (2 : ℝ) ^ (T-t) ≤ (j : ℝ) := by nlinarith
    exact_mod_cast this
  have hu' : j.val < (b.val + 1) * 2 ^ (T-t) := by
    have : (j : ℝ) + 1 ≤ ((b : ℝ) + 1) * (2 : ℝ) ^ (T-t) := by nlinarith
    exact_mod_cast this
  rw [Nat.add_mul, one_mul] at hu'
  refine ⟨⟨j.val - b.val * 2 ^ (T-t), by omega⟩, ?_⟩
  apply Fin.ext
  dsimp [child]
  omega

def halfI (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Ico ((j : ℝ) * width T) (((j : ℝ) + 1) * width T)
lemma measurable_halfI (T : ℕ) (j : Fin (2 ^ T)) : MeasurableSet (halfI T j) :=
  measurableSet_Ico
lemma halfI_subset (T : ℕ) (j : Fin (2 ^ T)) : halfI T j ⊆ I T j := by
  rw [I_eq]
  exact Ico_subset_Icc_self
lemma halfI_disjoint (T : ℕ) : Pairwise (fun i j => Disjoint (halfI T i) (halfI T j)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro t hi hj
  have hc := width_pos T
  change (i : ℝ) * width T ≤ t ∧ t < ((i : ℝ) + 1) * width T at hi
  change (j : ℝ) * width T ≤ t ∧ t < ((j : ℝ) + 1) * width T at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have h' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    nlinarith
  · have h' : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    nlinarith

lemma time_singleton_null {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (t : ℝ) :
    (ν.prod volume) {q : α × ℝ | q.2 = t} = 0 := by
  have heq : {q : α × ℝ | q.2 = t} = univ ×ˢ {t} := by ext q; simp
  rw [heq]
  rw [Measure.prod_prod, Real.volume_singleton, mul_zero]

lemma trim_halfI_measure {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {T : ℕ} {j : Fin (2 ^ T)} {S : Set (α × ℝ)}
    (hS : S ⊆ {q | q.2 ∈ I T j}) :
    (ν.prod volume) (S ∩ {q | q.2 ∈ halfI T j}) = (ν.prod volume) S := by
  apply measure_congr
  have hz : ∀ᵐ q : α × ℝ ∂ν.prod volume, q.2 ≠ ((j : ℝ) + 1) * width T := by
    apply ae_iff.mpr
    simpa using time_singleton_null ν (((j : ℝ) + 1) * width T)
  filter_upwards [hz] with q hq
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    have ht := hS h
    rw [I_eq] at ht
    exact ⟨h, ht.1, lt_of_le_of_ne ht.2 hq⟩

lemma coarse_unique {T t : ℕ} (j : Fin (2 ^ T)) (b b' : Fin (2 ^ t))
    (h : I T j ⊆ I t b) (h' : I T j ⊆ I t b') : b = b' := by
  by_contra hne
  have hlo := h (mem_I_left T j)
  have hhi := h (mem_I_right T j)
  have hlo' := h' (mem_I_left T j)
  have hhi' := h' (mem_I_right T j)
  rw [I_eq] at hlo hhi hlo' hhi'
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hstep : ((b : ℝ) + 1) * width t ≤ (b' : ℝ) * width t := by
      apply mul_le_mul_of_nonneg_right _ (width_pos t).le
      exact_mod_cast hh
    nlinarith [width_pos T, hlo'.1, hhi.2]
  · have hstep : ((b' : ℝ) + 1) * width t ≤ (b : ℝ) * width t := by
      apply mul_le_mul_of_nonneg_right _ (width_pos t).le
      exact_mod_cast hh
    nlinarith [width_pos T, hlo.1, hhi'.2]
end
end Submission.Obl.k4_scalar_pair_atlas_assembly
