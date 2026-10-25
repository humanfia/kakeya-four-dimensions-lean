/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/HistoryCore.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ReferenceFloors
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.NestedEntries
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set
open scoped BigOperators

def HistoryNode (n : ℕ → ℕ) (M m : ℕ) :=
  (h : Fin (m + 1)) × (Fin (n h) × EntryHistory M h)

scoped instance instFintypeHistoryNode (n : ℕ → ℕ) (M m : ℕ) : Fintype (HistoryNode n M m) :=
  inferInstanceAs (Fintype ((h : Fin (m + 1)) × (Fin (n h) × EntryHistory M h)))

def historyIncidence {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (I : (h : ℕ) → Fin (n h) → Set ℝ)
    (h : ℕ) (i : Fin (n h)) (u : EntryHistory M h) : Set (α × ℝ) :=
  historyAssignment n A entry parent h i u ×ˢ I h i

theorem historyIncidence_subset_parent {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (I : (h : ℕ) → Fin (n h) → Set ℝ)
    (hI : ∀ h i, I (h + 1) i ⊆ I h (parent h i))
    (h : ℕ) (i : Fin (n (h + 1))) (u : EntryHistory M h) (v : Fin M) :
    historyIncidence n A entry parent I (h + 1) i (u, v) ⊆
      historyIncidence n A entry parent I h (parent h i) u := by
  intro p hp
  exact ⟨historyAssignment_subset_parent n A entry parent h i u v hp.1, hI h i hp.2⟩

/-- Actual simultaneous successful entries fit the fixed ancestor chain.
Uniqueness is required only at the observed incidence, so null dyadic
endpoints can be removed before applying this deterministic statement. -/
theorem exists_historyIncidence {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (I : (h : ℕ) → Fin (n h) → Set ℝ)
    (hnest : ∀ h i, A (h + 1) i ⊆ A h (parent h i) ∧
      I (h + 1) i ⊆ I h (parent h i))
    (p : α × ℝ) (m : ℕ)
    (hunique : ∀ h ≤ m, ∀ i i', p ∈ A h i ×ˢ I h i →
      p ∈ A h i' ×ˢ I h i' → i = i')
    (hsuccess : ∀ h ≤ m, ∃ i u, p ∈ (A h i ∩ entry h i u) ×ˢ I h i) :
    ∃ i u, p ∈ historyIncidence n A entry parent I m i u := by
  induction m with
  | zero =>
    obtain ⟨i, u, hp⟩ := hsuccess 0 le_rfl
    exact ⟨i, u, hp⟩
  | succ m ih =>
    obtain ⟨ip, u, hp⟩ := ih
      (fun h hh => hunique h (Nat.le_succ_of_le hh))
      (fun h hh => hsuccess h (Nat.le_succ_of_le hh))
    obtain ⟨i, v, hi⟩ := hsuccess (m + 1) le_rfl
    have hpar : parent m i = ip := hunique m (Nat.le_succ m) _ _
      ⟨(hnest m i).1 hi.1.1, (hnest m i).2 hi.2⟩
      ⟨historyAssignment_subset n A entry parent m ip u hp.1, hp.2⟩
    refine ⟨i, (u, v), ?_⟩
    change ((p.1 ∈ A (m + 1) i ∧
      p.1 ∈ historyAssignment n A entry parent m (parent m i) u) ∧
        p.1 ∈ entry (m + 1) i v) ∧ p.2 ∈ I (m + 1) i
    exact ⟨⟨⟨hi.1.1, by simpa only [hpar] using hp.1⟩, hi.1.2⟩, hi.2⟩

/-- Each depth charges only its entry histories against the original
reference budget. The time partition does not introduce another factor. -/
theorem finite_history_reference_sum_le (n : ℕ → ℕ) (M m : ℕ) (hM : 1 ≤ M)
    (w : (h : ℕ) → Fin (n h) → ℝ)
    (hbudget : ∀ h ≤ m, ∑ i, w h i ≤ 1) :
    (∑ a : HistoryNode n M m, w a.1 a.2.1) ≤
      (m + 1 : ℝ) * (M : ℝ) ^ (m + 1) := by
  change (∑ a : (h : Fin (m + 1)) × (Fin (n h) × EntryHistory M h),
    w a.1 a.2.1) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _h : Fin (m + 1), (M : ℝ) ^ (m + 1) := by
      apply Finset.sum_le_sum
      intro h _
      change (∑ a : Fin (n h) × EntryHistory M h, w h a.1) ≤ _
      rw [sum_history_references, nsmul_eq_mul]
      simp only [Nat.cast_pow]
      have hpow : M ^ (h.val + 1) ≤ M ^ (m + 1) :=
        Nat.pow_le_pow_right hM (Nat.add_le_add_right (Nat.le_of_lt_succ h.isLt) 1)
      calc
        _ ≤ (M : ℝ) ^ (h.val + 1) * 1 :=
          mul_le_mul_of_nonneg_left (hbudget h (Nat.le_of_lt_succ h.isLt)) (by positivity)
        _ = (M : ℝ) ^ (h.val + 1) := mul_one _
        _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hpow
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- All finite-depth history events have their final original-reference
floors on one common measurable restriction. Later choosing a whole
ancestor preserves the descendant floors by nesting. -/
theorem exists_finite_history_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ → ℕ) (M m : ℕ) (hM : 1 ≤ M)
    (G : Set Ω) (hG : MeasurableSet G)
    (E : HistoryNode n M m → Set Ω) (hE : ∀ a, MeasurableSet (E a))
    (w : (h : ℕ) → Fin (n h) → ℝ) (hw : ∀ h i, 0 ≤ w h i)
    (hbudget : ∀ h ≤ m, ∑ i, w h i ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ G' : Set Ω, MeasurableSet G' ∧ G' ⊆ G ∧
      (∀ a p, p ∈ G' → p ∈ E a → τ * w a.1 a.2.1 ≤ (μ.restrict G').real (E a)) ∧
      μ.real G ≤ μ.real G' + τ * ((m + 1 : ℝ) * (M : ℝ) ^ (m + 1)) := by
  classical
  obtain ⟨S, G', _, hG', hsub, hmem, hfloor, hloss⟩ :=
    exists_simultaneous_reference_floors μ G hG E Finset.univ (fun a _ => hE a)
      (fun a => τ * w a.1 a.2.1) (fun a _ => mul_nonneg hτ (hw _ _))
  refine ⟨G', hG', hsub, ?_, hloss.trans ?_⟩
  · intro a p hp hpa
    exact hfloor a (hmem p hp a (Finset.mem_univ a) hpa)
  · apply add_le_add le_rfl
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (finite_history_reference_sum_le n M m hM w hbudget) hτ

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
