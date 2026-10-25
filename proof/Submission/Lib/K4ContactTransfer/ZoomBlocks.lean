import Mathlib
import Submission.Lib.K4ContactTransfer.RowParent

/-!
# Dyadic blocks inside a zoomed parent block

A dyadic block `I(T, j)` inside the parent block `I(T_Q, j_Q)` is, after the
time zoom `t ↦ (t - t₀)/q_Q`, the dyadic block `I(T - T_Q, j - j_Q 2^(T - T_Q))`
of the unit interval. This gives the zoomed instance its time labels.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set
open scoped ENNReal

noncomputable section

open PreparedModel

/-- A contained dyadic block has a level at least the parent level. -/
theorem level_le_of_interval_subset {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) : TQ ≤ T := by
  rw [interval_eq, interval_eq] at h
  have hne : blockStart T j ≤ blockStart T j + (2 : ℝ) ^ (-(T : ℤ)) := by
    have : (0 : ℝ) < (2 : ℝ) ^ (-(T : ℤ)) := by positivity
    linarith
  obtain ⟨h1, h2⟩ := (Icc_subset_Icc_iff hne).mp h
  have hle : (2 : ℝ) ^ (-(T : ℤ)) ≤ (2 : ℝ) ^ (-(TQ : ℤ)) := by linarith
  by_contra hlt
  push Not at hlt
  have : (2 : ℝ) ^ (-(TQ : ℤ)) < (2 : ℝ) ^ (-(T : ℤ)) := by
    apply zpow_lt_zpow_right₀ (by norm_num)
    omega
  linarith

/-- The index of a contained block relative to the parent block. -/
def relIndex (T TQ : ℕ) (j : Fin (2 ^ T)) (jQ : Fin (2 ^ TQ)) : ℕ :=
  (j : ℕ) - (jQ : ℕ) * 2 ^ (T - TQ)

theorem relIndex_spec {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) :
    (jQ : ℕ) * 2 ^ (T - TQ) ≤ (j : ℕ) ∧ relIndex T TQ j jQ < 2 ^ (T - TQ) := by
  have hTQ := level_le_of_interval_subset h
  obtain ⟨h1, h2⟩ := interval_subset_iff.mp h
  have hpow : (2 : ℝ) ^ T = (2 : ℝ) ^ (T - TQ) * (2 : ℝ) ^ TQ := by
    rw [← pow_add, Nat.sub_add_cancel hTQ]
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hTQ' : (0 : ℝ) < (2 : ℝ) ^ TQ := by positivity
  have hm : (0 : ℝ) < (2 : ℝ) ^ (T - TQ) := by positivity
  -- clear denominators
  have e1 : ((jQ : ℕ) : ℝ) * (2 : ℝ) ^ (T - TQ) ≤ ((j : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hTQ' hT, hpow] at h1
    nlinarith
  have e2 : ((j : ℕ) : ℝ) + 1 ≤ (((jQ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (T - TQ) := by
    rw [div_le_div_iff₀ hT hTQ', hpow] at h2
    nlinarith
  have n1 : (jQ : ℕ) * 2 ^ (T - TQ) ≤ (j : ℕ) := by exact_mod_cast e1
  have n2 : (j : ℕ) + 1 ≤ ((jQ : ℕ) + 1) * 2 ^ (T - TQ) := by exact_mod_cast e2
  refine ⟨n1, ?_⟩
  unfold relIndex
  have : ((jQ : ℕ) + 1) * 2 ^ (T - TQ) = (jQ : ℕ) * 2 ^ (T - TQ) + 2 ^ (T - TQ) := by ring
  omega

/-- The relative dyadic index as an element of `Fin (2 ^ (T - TQ))`. -/
def relFin {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) : Fin (2 ^ (T - TQ)) :=
  ⟨relIndex T TQ j jQ, (relIndex_spec h).2⟩

/-- **Zoomed blocks.** The time zoom maps a contained block onto the relative
dyadic block. -/
theorem zoom_interval {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) (t : ℝ) :
    t ∈ interval T j ↔
      (t - blockStart TQ jQ) / (2 : ℝ) ^ (-(TQ : ℤ)) ∈ interval (T - TQ) (relFin h) := by
  have hTQ := level_le_of_interval_subset h
  obtain ⟨n1, _⟩ := relIndex_spec h
  have hpow : (2 : ℝ) ^ T = (2 : ℝ) ^ (T - TQ) * (2 : ℝ) ^ TQ := by
    rw [← pow_add, Nat.sub_add_cancel hTQ]
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hTQ' : (0 : ℝ) < (2 : ℝ) ^ TQ := by positivity
  have hm : (0 : ℝ) < (2 : ℝ) ^ (T - TQ) := by positivity
  have hrel : ((relFin h : ℕ) : ℝ) = ((j : ℕ) : ℝ) - ((jQ : ℕ) : ℝ) * (2 : ℝ) ^ (T - TQ) := by
    simp only [relFin, relIndex]
    rw [Nat.cast_sub n1]
    push_cast
    ring
  have hq : (2 : ℝ) ^ (-(TQ : ℤ)) = ((2 : ℝ) ^ TQ)⁻¹ := by rw [zpow_neg, zpow_natCast]
  set A : ℝ := (2 : ℝ) ^ (T - TQ)
  set B : ℝ := (2 : ℝ) ^ TQ
  have key : (t - ((jQ : ℕ) : ℝ) / B) / B⁻¹ * A = t * (A * B) - ((jQ : ℕ) : ℝ) * A := by
    field_simp
  simp only [interval, mem_Icc, blockStart, hrel, hq]
  rw [hpow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < A * B), le_div_iff₀ (by positivity : (0 : ℝ) < A * B),
    div_le_iff₀ hm, le_div_iff₀ hm, key]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The relative block length is the ratio of the block lengths. -/
theorem rel_length {T TQ : ℕ} (h : TQ ≤ T) :
    (2 : ℝ) ^ (-((T - TQ : ℕ) : ℤ)) = (2 : ℝ) ^ (-(T : ℤ)) / (2 : ℝ) ^ (-(TQ : ℤ)) := by
  rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast [Nat.cast_sub h]
  ring

end

end Submission.Lib.K4ContactTransfer
