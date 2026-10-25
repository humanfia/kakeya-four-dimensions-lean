import Mathlib

/-!
# Dyadic blocks inside a parent block

A dyadic block `[j / 2^T, (j + 1) / 2^T]` inside the parent block
`[j₀ / 2^T₀, (j₀ + 1) / 2^T₀]` has `T₀ ≤ T` and offset
`0 ≤ j - j₀ * 2^(T - T₀) < 2^(T - T₀)`. In parent time `τ = 2^T₀ * t - j₀` it is
the dyadic block of exponent `T - T₀` and index `j - j₀ * 2^(T - T₀)`.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set

/-- The closed dyadic block. -/
def dyadicBlock (T j : ℕ) : Set ℝ := Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T)

theorem dyadic_exponent_le {T₀ j₀ T j : ℕ}
    (h : dyadicBlock T j ⊆ dyadicBlock T₀ j₀) : T₀ ≤ T := by
  have hl : (j : ℝ) / 2 ^ T ∈ dyadicBlock T j :=
    ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have hr : ((j : ℝ) + 1) / 2 ^ T ∈ dyadicBlock T j :=
    ⟨div_le_div_of_nonneg_right (by linarith) (by positivity), le_rfl⟩
  have h1 := (h hl).1
  have h2 := (h hr).2
  by_contra hlt
  push_neg at hlt
  have hpow : (2 : ℝ) ^ T < 2 ^ T₀ := pow_lt_pow_right₀ (by norm_num) hlt
  have hlen : 1 / (2 : ℝ) ^ T ≤ 1 / 2 ^ T₀ := by
    have : ((j : ℝ) + 1) / 2 ^ T - (j : ℝ) / 2 ^ T ≤
        ((j₀ : ℝ) + 1) / 2 ^ T₀ - (j₀ : ℝ) / 2 ^ T₀ := by linarith
    rw [← sub_div, ← sub_div] at this
    simpa using this
  have : 1 / (2 : ℝ) ^ T₀ < 1 / 2 ^ T := one_div_lt_one_div_of_lt (by positivity) hpow
  linarith

/-- The offset of a dyadic block inside its parent block. -/
theorem dyadic_offset {T₀ j₀ T j : ℕ}
    (h : dyadicBlock T j ⊆ dyadicBlock T₀ j₀) :
    j₀ * 2 ^ (T - T₀) ≤ j ∧ j - j₀ * 2 ^ (T - T₀) < 2 ^ (T - T₀) := by
  have hT := dyadic_exponent_le h
  have hl : (j : ℝ) / 2 ^ T ∈ dyadicBlock T j :=
    ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have hr : ((j : ℝ) + 1) / 2 ^ T ∈ dyadicBlock T j :=
    ⟨div_le_div_of_nonneg_right (by linarith) (by positivity), le_rfl⟩
  have h1 := (h hl).1
  have h2 := (h hr).2
  have hsplit : (2 : ℝ) ^ T = 2 ^ T₀ * 2 ^ (T - T₀) := by
    rw [← pow_add, Nat.add_sub_cancel' hT]
  rw [hsplit] at h1 h2
  have hA : (j₀ : ℝ) * 2 ^ (T - T₀) ≤ j := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
    have h3 : (j₀ : ℝ) * (2 ^ (T - T₀)) * 2 ^ T₀ ≤ (j : ℝ) * 2 ^ T₀ := by nlinarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hB : (j : ℝ) + 1 ≤ ((j₀ : ℝ) + 1) * 2 ^ (T - T₀) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
    have h3 : ((j : ℝ) + 1) * 2 ^ T₀ ≤ ((j₀ : ℝ) + 1) * 2 ^ (T - T₀) * 2 ^ T₀ := by nlinarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hA' : j₀ * 2 ^ (T - T₀) ≤ j := by exact_mod_cast hA
  have hB' : j + 1 ≤ (j₀ + 1) * 2 ^ (T - T₀) := by exact_mod_cast hB
  refine ⟨hA', ?_⟩
  have : (j₀ + 1) * 2 ^ (T - T₀) = j₀ * 2 ^ (T - T₀) + 2 ^ (T - T₀) := by ring
  omega

/-- In parent time a nested dyadic block is the dyadic block of the residual
exponent and offset. -/
theorem dyadic_parent_time {T₀ j₀ T j : ℕ}
    (h : dyadicBlock T j ⊆ dyadicBlock T₀ j₀) (t : ℝ) :
    t ∈ dyadicBlock T j ↔
      (2 : ℝ) ^ T₀ * t - j₀ ∈ dyadicBlock (T - T₀) (j - j₀ * 2 ^ (T - T₀)) := by
  have hT := dyadic_exponent_le h
  have hoff := (dyadic_offset h).1
  have hsplit : (2 : ℝ) ^ T = 2 ^ T₀ * 2 ^ (T - T₀) := by
    rw [← pow_add, Nat.add_sub_cancel' hT]
  have hcast : ((j - j₀ * 2 ^ (T - T₀) : ℕ) : ℝ) = (j : ℝ) - j₀ * 2 ^ (T - T₀) := by
    rw [Nat.cast_sub hoff]
    push_cast
    ring
  simp only [dyadicBlock, mem_Icc, hcast]
  have h0 : (0 : ℝ) < 2 ^ T₀ := by positivity
  have h1 : (0 : ℝ) < 2 ^ (T - T₀) := by positivity
  rw [hsplit]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · rw [div_le_iff₀ h1]
      rw [div_le_iff₀ (by positivity)] at ha
      nlinarith
    · rw [le_div_iff₀ h1]
      rw [le_div_iff₀ (by positivity)] at hb
      nlinarith
  · rintro ⟨ha, hb⟩
    constructor
    · rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ h1] at ha
      nlinarith
    · rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ h1] at hb
      nlinarith

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
