import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.Defs

/-!
# Dyadic time blocks

Nesting of the closed dyadic intervals `I T j` in coarser ones, the number of fine blocks
in a coarse block, the choice of the coarsened depth `T₁`, and the fact that distinct
coarse blocks meet in a null set.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

lemma two_pow_split {T T₁ : ℕ} (h : T₁ ≤ T) :
    (2 : ℝ) ^ T = (2 : ℝ) ^ T₁ * (2 : ℝ) ^ (T - T₁) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

lemma I_left_mem (T : ℕ) (j : Fin (2 ^ T)) : ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ∈ I T j := by
  refine ⟨le_rfl, ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

lemma I_nonempty (T : ℕ) (j : Fin (2 ^ T)) : (I T j).Nonempty := ⟨_, I_left_mem T j⟩

/-- A fine dyadic block lies in the coarse block `b` exactly when `b` is its quotient. -/
lemma I_subset_iff {T T₁ : ℕ} (h : T₁ ≤ T) (j : Fin (2 ^ T)) (b : Fin (2 ^ T₁)) :
    I T j ⊆ I T₁ b ↔ (j : ℕ) / 2 ^ (T - T₁) = b := by
  have hsplit := two_pow_split (T := T) (T₁ := T₁) h
  have hR : (0 : ℝ) < (2 : ℝ) ^ (T - T₁) := by positivity
  have h1 : (0 : ℝ) < (2 : ℝ) ^ T₁ := by positivity
  have hRn : 0 < 2 ^ (T - T₁) := by positivity
  have hle : ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := by
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  unfold I
  rw [Set.Icc_subset_Icc_iff hle]
  constructor
  · rintro ⟨hlo, hhi⟩
    rw [hsplit, div_le_div_iff₀ h1 (by positivity)] at hlo
    rw [hsplit, div_le_div_iff₀ (by positivity) h1] at hhi
    have hlo' : (b : ℕ) * 2 ^ (T - T₁) ≤ (j : ℕ) := by
      have : ((b : ℕ) : ℝ) * (2 : ℝ) ^ (T - T₁) ≤ ((j : ℕ) : ℝ) := by nlinarith
      exact_mod_cast this
    have hhi' : (j : ℕ) < ((b : ℕ) + 1) * 2 ^ (T - T₁) := by
      have : ((j : ℕ) : ℝ) + 1 ≤ (((b : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (T - T₁) := by nlinarith
      have : (j : ℕ) + 1 ≤ ((b : ℕ) + 1) * 2 ^ (T - T₁) := by exact_mod_cast this
      omega
    exact Nat.div_eq_of_lt_le hlo' hhi'
  · intro hb
    have hlo' : (b : ℕ) * 2 ^ (T - T₁) ≤ (j : ℕ) := by
      rw [← hb]; exact Nat.div_mul_le_self _ _
    have hhi' : (j : ℕ) + 1 ≤ ((b : ℕ) + 1) * 2 ^ (T - T₁) := by
      rw [← hb]
      have := Nat.lt_div_mul_add (a := (j : ℕ)) hRn
      rw [add_mul, one_mul]; omega
    have hlo'' : ((b : ℕ) : ℝ) * (2 : ℝ) ^ (T - T₁) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlo'
    have hhi'' : ((j : ℕ) : ℝ) + 1 ≤ (((b : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (T - T₁) := by
      exact_mod_cast hhi'
    constructor
    · rw [hsplit, div_le_div_iff₀ h1 (by positivity)]; nlinarith
    · rw [hsplit, div_le_div_iff₀ (by positivity) h1]; nlinarith

/-- Every fine block lies in some coarse block. -/
lemma exists_coarse {T T₁ : ℕ} (h : T₁ ≤ T) (j : Fin (2 ^ T)) :
    ∃ b : Fin (2 ^ T₁), I T j ⊆ I T₁ b := by
  have hlt : (j : ℕ) / 2 ^ (T - T₁) < 2 ^ T₁ := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' h]
    exact j.2
  exact ⟨⟨_, hlt⟩, (I_subset_iff h j _).2 rfl⟩

/-- A fine block lies in at most one coarse block. -/
lemma coarse_unique {T T₁ : ℕ} (h : T₁ ≤ T) (j : Fin (2 ^ T)) {b b' : Fin (2 ^ T₁)}
    (hb : I T j ⊆ I T₁ b) (hb' : I T j ⊆ I T₁ b') : b = b' := by
  rw [I_subset_iff h] at hb hb'
  exact Fin.ext (hb.symm.trans hb')

open scoped Classical in
/-- A coarse block contains at most `2 ^ (T - T₁)` fine blocks. -/
lemma card_fine_le {T T₁ : ℕ} (h : T₁ ≤ T) (b : Fin (2 ^ T₁)) :
    (Finset.univ.filter (fun j : Fin (2 ^ T) => I T j ⊆ I T₁ b)).card ≤ 2 ^ (T - T₁) := by
  have hRn : 0 < 2 ^ (T - T₁) := by positivity
  calc (Finset.univ.filter (fun j : Fin (2 ^ T) => I T j ⊆ I T₁ b)).card
      ≤ (Finset.range (2 ^ (T - T₁))).card := by
        apply Finset.card_le_card_of_injOn (fun j : Fin (2 ^ T) => (j : ℕ) % 2 ^ (T - T₁))
        · intro j _
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.mod_lt _ hRn
        · intro j₁ hj₁ j₂ hj₂ heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
            I_subset_iff h] at hj₁ hj₂
          apply Fin.ext
          rw [← Nat.div_add_mod (j₁ : ℕ) (2 ^ (T - T₁)),
            ← Nat.div_add_mod (j₂ : ℕ) (2 ^ (T - T₁)), hj₁, hj₂]
          simp only at heq
          rw [heq]
    _ = 2 ^ (T - T₁) := Finset.card_range _

lemma volume_I (T : ℕ) (j : Fin (2 ^ T)) :
    volume (I T j) = ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
  unfold I
  rw [Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- Two distinct dyadic blocks of the same depth meet in at most one point. -/
lemma I_inter_subsingleton (T : ℕ) {b b' : Fin (2 ^ T)} (hne : b ≠ b') :
    (I T b ∩ I T b').Subsingleton := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · intro s hs t ht
    have h1 : ((b : ℕ) : ℝ) + 1 ≤ ((b' : ℕ) : ℝ) := by exact_mod_cast hlt
    have h2 : (((b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((b' : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    obtain ⟨⟨_, hs1⟩, ⟨hs2, _⟩⟩ := hs
    obtain ⟨⟨_, ht1⟩, ⟨ht2, _⟩⟩ := ht
    linarith
  · intro s hs t ht
    have h1 : ((b' : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hlt
    have h2 : (((b' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((b : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    obtain ⟨⟨hs2, _⟩, ⟨_, hs1⟩⟩ := hs
    obtain ⟨⟨ht2, _⟩, ⟨_, ht1⟩⟩ := ht
    linarith

lemma volume_I_inter (T : ℕ) {b b' : Fin (2 ^ T)} (hne : b ≠ b') :
    volume (I T b ∩ I T b') = 0 :=
  (I_inter_subsingleton T hne).measure_zero _

lemma measurableSet_I (T : ℕ) (j : Fin (2 ^ T)) : MeasurableSet (I T j) := measurableSet_Icc

/-- Choice of the coarsened depth: `2 ^ (T - T₁) ≤ X` and `2 ^ T₁ ≤ 2 max 1 (2 ^ T / X)`. -/
lemma exists_T₁ (T : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ∃ T₁ : ℕ, T₁ ≤ T ∧ (2 : ℝ) ^ (T - T₁) ≤ X ∧
      (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T / X) := by
  set m := Nat.log 2 ⌊X⌋₊ with hm
  have hfl : ⌊X⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
    omega
  have hm1 : 2 ^ m ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 hfl
  have hm2 : ⌊X⌋₊ < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hm1' : (2 : ℝ) ^ m ≤ X := by
    have : ((2 ^ m : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hm1
    push_cast at this
    exact this.trans (Nat.floor_le (by linarith))
  have hm2' : X < 2 * (2 : ℝ) ^ m := by
    have h3 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h4 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hm2
    push_cast at h4
    rw [pow_succ] at h4
    linarith
  refine ⟨T - m, Nat.sub_le _ _, ?_, ?_⟩
  · calc (2 : ℝ) ^ (T - (T - m)) ≤ (2 : ℝ) ^ m :=
          pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ X := hm1'
  · rcases le_or_gt m T with hmT | hmT
    · have hX0 : 0 < X := by linarith
      have hsplit : (2 : ℝ) ^ T = (2 : ℝ) ^ (T - m) * (2 : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hmT]
      have hpm : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have : (2 : ℝ) ^ (T - m) ≤ 2 * ((2 : ℝ) ^ T / X) := by
        rw [← mul_div_assoc, le_div_iff₀ hX0, hsplit]
        nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (T - m)]
      exact this.trans (by gcongr; exact le_max_right _ _)
    · have : T - m = 0 := by omega
      rw [this, pow_zero]
      have := le_max_left (1 : ℝ) ((2 : ℝ) ^ T / X)
      linarith

end Submission.Obl.k4_scalar_angular_pair_agreement
