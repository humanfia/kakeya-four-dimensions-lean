import Submission.Obl.k4_scalar_true_terminal_lifting.Interface

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open Set
open k4_scalar_linear_critical_extremizers.Split

/-- The two integer depths of nested dyadic time intervals add. -/
def composeDyadicLabel (T S : ℕ) (j : Fin (2 ^ T)) (l : Fin (2 ^ S)) : Fin (2 ^ (T + S)) :=
  Fin.cast (pow_add 2 T S).symm (finProdFinEquiv (j, l))

theorem composeDyadicLabel_val (T S : ℕ) (j : Fin (2 ^ T)) (l : Fin (2 ^ S)) :
    (composeDyadicLabel T S j l).val = j.val * 2 ^ S + l.val := by
  change l.val + 2 ^ S * j.val = _
  ac_rfl

theorem composeDyadicLabel_injective (T S : ℕ) :
    Function.Injective (fun p : Fin (2 ^ T) × Fin (2 ^ S) => composeDyadicLabel T S p.1 p.2) := by
  intro x y h
  apply finProdFinEquiv.injective
  exact Fin.cast_injective (pow_add 2 T S).symm h

theorem composeDyadicLabel_eq_iff (T S : ℕ) (j j' : Fin (2 ^ T)) (l l' : Fin (2 ^ S)) :
    composeDyadicLabel T S j l = composeDyadicLabel T S j' l' ↔ j = j' ∧ l = l' := by
  constructor
  · intro h
    exact Prod.mk.inj ((composeDyadicLabel_injective T S) h)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem normalized_time_mem_Icc {dt : ℝ} (hdt : 0 < dt) (t₀ a b t : ℝ) :
    (t - t₀) / dt ∈ Icc a b ↔ t ∈ Icc (t₀ + dt * a) (t₀ + dt * b) := by
  rw [mem_Icc, mem_Icc, le_div_iff₀ hdt, div_le_iff₀ hdt]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

/-- Membership in a composed interval is exactly membership in the child
interval after the parent's affine time normalization. -/
theorem normalized_time_mem_composed_interval
    (T S : ℕ) (j : Fin (2 ^ T)) (l : Fin (2 ^ S)) (t : ℝ) :
    (t - (j.val : ℝ) * ((2 : ℝ) ^ T)⁻¹) / ((2 : ℝ) ^ T)⁻¹ ∈ I S l ↔
      t ∈ I (T + S) (composeDyadicLabel T S j l) := by
  have hdt : 0 < ((2 : ℝ) ^ T)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) _)
  have hc : ((composeDyadicLabel T S j l).val : ℝ) =
      (j.val : ℝ) * (2 : ℝ) ^ S + (l.val : ℝ) := by
    rw [composeDyadicLabel_val]
    push_cast
    rfl
  have hlo : (j.val : ℝ) * ((2 : ℝ) ^ T)⁻¹ +
      ((2 : ℝ) ^ T)⁻¹ * ((l.val : ℝ) / (2 : ℝ) ^ S) =
        ((composeDyadicLabel T S j l).val : ℝ) / (2 : ℝ) ^ (T + S) := by
    rw [hc, pow_add]
    field_simp
  have hup : (j.val : ℝ) * ((2 : ℝ) ^ T)⁻¹ +
      ((2 : ℝ) ^ T)⁻¹ * (((l.val : ℝ) + 1) / (2 : ℝ) ^ S) =
        (((composeDyadicLabel T S j l).val : ℝ) + 1) / (2 : ℝ) ^ (T + S) := by
    rw [hc, pow_add]
    field_simp
    ring
  have h := normalized_time_mem_Icc hdt ((j.val : ℝ) * ((2 : ℝ) ^ T)⁻¹)
    ((l.val : ℝ) / (2 : ℝ) ^ S) (((l.val : ℝ) + 1) / (2 : ℝ) ^ S) t
  rw [hlo, hup] at h
  exact h

/-- A time belongs to at most two closed intervals at one dyadic depth. -/
theorem dyadic_label_mem_two (T : ℕ) (j : Fin (2 ^ T)) (t : ℝ) (ht : t ∈ I T j) :
    (j.val : ℤ) ∈ ({⌊(2 : ℝ) ^ T * t⌋, ⌊(2 : ℝ) ^ T * t⌋ - 1} : Finset ℤ) := by
  have hp : 0 < (2 : ℝ) ^ T := pow_pos (by norm_num) _
  have hlo : (j.val : ℝ) ≤ (2 : ℝ) ^ T * t := by
    have h := (div_le_iff₀ hp).mp ht.1
    nlinarith
  have hup : (2 : ℝ) ^ T * t ≤ (j.val : ℝ) + 1 := by
    have h := (le_div_iff₀ hp).mp ht.2
    nlinarith
  have hil : (j.val : ℤ) ≤ ⌊(2 : ℝ) ^ T * t⌋ := Int.le_floor.mpr (by simpa using hlo)
  have hiu : ⌊(2 : ℝ) ^ T * t⌋ ≤ (j.val : ℤ) + 1 := by
    calc
      _ ≤ ⌊(j.val : ℝ) + 1⌋ := Int.floor_mono hup
      _ = _ := by simp
  have h : (j.val : ℤ) = ⌊(2 : ℝ) ^ T * t⌋ ∨ (j.val : ℤ) = ⌊(2 : ℝ) ^ T * t⌋ - 1 := by omega
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

open Classical in
/-- The full assignment rectangles have pointwise multiplicity at most two
inside one original world, including dyadic endpoints. -/
theorem parent_assignment_multiplicity_le_two
    {X ι Γ : Type*} [Fintype ι] (T : ℕ) (γ : ι → Γ)
    (j : ι → Fin (2 ^ T)) (A : ι → Set X)
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (a : Γ) (l : X) (t : ℝ) :
    (Finset.univ.filter (fun i => γ i = a ∧ l ∈ A i ∧ t ∈ I T (j i))).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun i => γ i = a ∧ l ∈ A i ∧ t ∈ I T (j i))
  let label := fun i : ι => ((j i).val : ℤ)
  have hinj : Set.InjOn label (S : Set ι) := by
    intro i hi i' hi' he
    have hi₀ := (Finset.mem_filter.mp hi).2
    have hi₁ := (Finset.mem_filter.mp hi').2
    change ((j i).val : ℤ) = ((j i').val : ℤ) at he
    have hj : j i = j i' := Fin.ext (by exact_mod_cast he)
    by_contra hne
    exact Set.disjoint_left.mp
      (hdisj i i' hne (hi₀.1.trans hi₁.1.symm) hj) hi₀.2.1 hi₁.2.1
  calc
    _ = (S.image label).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({⌊(2 : ℝ) ^ T * t⌋, ⌊(2 : ℝ) ^ T * t⌋ - 1} : Finset ℤ).card := by
      apply Finset.card_le_card
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact dyadic_label_mem_two T (j i) t (Finset.mem_filter.mp hi).2.2.2
    _ ≤ 2 := Finset.card_le_two

end Submission.Obl.k4_scalar_true_terminal_lifting
