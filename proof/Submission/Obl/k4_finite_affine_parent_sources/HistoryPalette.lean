-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/HistoryPalette.lean.
import Submission.Obl.k4_finite_affine_parent_sources.ConditionalPalette

/-! Conditional palette bounds after forgetting the reference history. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Hist Sf Pal : Type*} [Fintype Ω] [Fintype Hist]
  [DecidableEq Hist] [DecidableEq Sf] [DecidableEq Pal]

theorem finite_fiberMass_pair_sum_left
    (P : Ω → ℝ) (history : Ω → Hist) (key : Ω → Sf) (s : Sf) :
    (∑ h, fiberMass P (fun e => (history e, key e)) (h, s)) = fiberMass P key s := by
  unfold fiberMass
  simp only [sum_filter, Prod.mk.injEq]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases hs : key e = s <;> simp [hs]

theorem finite_fiberMass_le_of_subset
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (key₁ : Ω → A) (key₂ : Ω → B) (a : A) (b : B)
    (hsub : ∀ e, key₁ e = a → key₂ e = b) :
    fiberMass P key₁ a ≤ fiberMass P key₂ b := by
  unfold fiberMass
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hP e)
  intro e he
  exact mem_filter.mpr ⟨mem_univ e, hsub e (mem_filter.mp he).2⟩

/-- Original reference numerators and current history--state floors bound
the palette conditioned only on the aggregate state. The history is forgotten
without renormalizing its reference weights. -/
theorem conditional_palette_cap_of_history_floors
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (history : Ω → Hist) (key : Ω → Sf) (Z : Ω → Pal)
    (reference : Hist → ℝ) (π : Pal → ℝ) (K L : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hπ : ∀ z, 0 ≤ π z)
    (hfloor : ∀ h s, fiberMass P (fun e => (history e, key e)) (h, s) ≠ 0 →
      reference h ≤ L * fiberMass P (fun e => (history e, key e)) (h, s))
    (hnum : ∀ h z, fiberMass P (fun e => (history e, Z e)) (h, z) ≤ K * reference h * π z) :
    ∀ e z, (∑ er ∈ univ.filter (fun er => Z er = z), condKey P key e er) ≤ (K * L) * π z := by
  have hentry (h : Hist) (s : Sf) (z : Pal) :
      fiberMass P (fun e => (history e, (key e, Z e))) (h, (s, z)) ≤
        ((K * L) * π z) * fiberMass P (fun e => (history e, key e)) (h, s) := by
    have hsmall := finite_fiberMass_le_of_subset P hP
      (fun e => (history e, (key e, Z e))) (fun e => (history e, key e)) (h, (s, z)) (h, s)
      (by
        intro e he
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.1⟩)
    by_cases hd : fiberMass P (fun e => (history e, key e)) (h, s) = 0
    · rw [hd, mul_zero]
      exact hsmall.trans_eq hd
    have hwhole := finite_fiberMass_le_of_subset P hP
      (fun e => (history e, (key e, Z e))) (fun e => (history e, Z e)) (h, (s, z)) (h, z)
      (by
        intro e he
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩)
    calc
      _ ≤ K * reference h * π z := hwhole.trans (hnum h z)
      _ ≤ K * (L * fiberMass P (fun e => (history e, key e)) (h, s)) * π z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfloor h s hd) hK) (hπ z)
      _ = _ := by ring
  have haggregate (s : Sf) (z : Pal) :
      fiberMass P (fun e => (key e, Z e)) (s, z) ≤ (K * L) * fiberMass P key s * π z := by
    calc
      _ = ∑ h, fiberMass P (fun e => (history e, (key e, Z e))) (h, (s, z)) :=
        (finite_fiberMass_pair_sum_left P history (fun e => (key e, Z e)) (s, z)).symm
      _ ≤ ∑ h, ((K * L) * π z) * fiberMass P (fun e => (history e, key e)) (h, s) :=
        sum_le_sum fun h _ => hentry h s z
      _ = ((K * L) * π z) * fiberMass P key s := by
        rw [← mul_sum, finite_fiberMass_pair_sum_left]
      _ = _ := by ring
  exact conditional_palette_cap_of_original_floor P hP key Z (fiberMass P key) π (K * L)
    (mul_nonneg hK hL) hπ (fun _ _ => le_rfl) haggregate

end

end Submission.Obl.k4_finite_affine_parent_sources
