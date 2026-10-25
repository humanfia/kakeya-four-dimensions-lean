/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/FrameCore.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameGood
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.PrunedParent

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}

/-- The root records only the original parent and its successful entry. -/
def frameHistoryRoot (f : Frame D k s₀ U') :
    (h : ℕ) → Fin (f.nl h) → EntryHistory f.M h → Fin (f.nl 0) × Fin f.M
  | 0, i, u => (i, u)
  | h + 1, i, u => frameHistoryRoot f h (f.anc h i) u.1

/-- The finite ancestors supply both the trajectory and time inclusions. -/
theorem frameHistoryRoot_subsets (f : Frame D k s₀ U')
    (hnest : ∀ h < f.m, ∀ i : Fin (f.nl (h + 1)),
      f.block (h + 1) i ⊆ f.block h (f.anc h i)) :
    ∀ h ≤ f.m, ∀ i u,
      f.hist h i u ⊆ f.hist 0 (frameHistoryRoot f h i u).1 (frameHistoryRoot f h i u).2 ∧
      f.block h i ⊆ f.block 0 (frameHistoryRoot f h i u).1 := by
  intro h
  induction h with
  | zero => exact fun _ i u => ⟨subset_refl _, subset_refl _⟩
  | succ h ih =>
    intro hh i u
    obtain ⟨hs, hI⟩ := ih (by omega) (f.anc h i) u.1
    have hhist : f.hist (h + 1) i u ⊆ f.hist h (f.anc h i) u.1 :=
      historyAssignment_subset_parent f.nl (fun h => D.A k (f.depth h)) f.entry f.anc h i u.1 u.2
    exact ⟨hhist.trans hs, (hnest h (by omega) i).trans hI⟩

/-- The reference budget in the transferred finite-history representation. -/
theorem frame_history_reference_budget (f : Frame D k s₀ U') (hM : 1 ≤ f.M)
    (reference : (h : ℕ) → Fin (f.nl h) → ℝ≥0∞)
    (hbudget : ∀ h ≤ f.m, ∑ i, reference h i ≤ 1) :
    (∑ a : HistoryNode f.nl f.M f.m, reference a.1 a.2.1) ≤
      ((f.m + 1 : ℕ) : ℝ≥0∞) * (f.M : ℝ≥0∞) ^ (f.m + 1) := by
  change (∑ a : (Σ h : Fin (f.m + 1), Fin (f.nl h) × EntryHistory f.M h),
    reference a.1 a.2.1) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _h : Fin (f.m + 1), (f.M : ℝ≥0∞) ^ (f.m + 1) := by
      apply Finset.sum_le_sum
      intro h _
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, card_entryHistory, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      calc
        _ ≤ ((f.M ^ (h.val + 1) : ℕ) : ℝ≥0∞) := by
          simpa only [mul_one] using mul_le_mul' le_rfl (hbudget h (by omega))
        _ ≤ (f.M : ℝ≥0∞) ^ (f.m + 1) := by
          exact_mod_cast Nat.pow_le_pow_right hM (Nat.add_le_add_right (by omega : h.val ≤ f.m) 1)
    _ = _ := by simp [nsmul_eq_mul]

/-- The finite per-index source construction, before any normalization.
Every retained history keeps its ORIGINAL reference after the parent is selected. -/
theorem frame_exists_parent_core (f : Frame D k s₀ U')
    (hM : 1 ≤ f.M) (G : Set (α × ℝ)) (hG : MeasurableSet G)
    (hevent : ∀ h ≤ f.m, ∀ i u, MeasurableSet (f.event h i u))
    (hnest : ∀ h < f.m, ∀ i : Fin (f.nl (h + 1)),
      f.block (h + 1) i ⊆ f.block h (f.anc h i))
    (hunique : ∀ p ∈ G, ∀ (i i' : Fin (f.nl 0)) (u u' : Fin f.M),
      p ∈ f.event 0 i u → p ∈ f.event 0 i' u' → i = i' ∧ u = u')
    (hcover : ∀ p ∈ G, ∀ h ≤ f.m, ∃ i u, p ∈ f.event h i u)
    (hbudget : ∀ h ≤ f.m,
      (∑ i, ENNReal.ofReal (f.ql h) * D.ν k (D.A k (f.depth h) i)) ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hcost : ENNReal.ofReal θ *
      (((f.m + 1 : ℕ) : ℝ≥0∞) * (f.M : ℝ≥0∞) ^ (f.m + 1)) < D.ρ k G) :
    ∃ (i₀ : Fin (f.nl 0)) (u₀ : Fin f.M) (C : Set (α × ℝ)),
      MeasurableSet C ∧ C.Nonempty ∧ C ⊆ G ∧ C ⊆ f.event 0 i₀ u₀ ∧
      ENNReal.ofReal (θ * f.ql 0) * D.ν k (D.A k (f.depth 0) i₀) ≤ D.ρ k C ∧
      (∀ p ∈ C, ∀ h ≤ f.m, ∃ i u, p ∈ f.event h i u) ∧
      ∀ h ≤ f.m, ∀ i u, (f.event h i u ∩ C).Nonempty →
        f.block h i ⊆ f.block 0 i₀ ∧ f.hist h i u ⊆ f.hist 0 i₀ u₀ ∧
        ENNReal.ofReal (θ * f.ql h) * D.ν k (D.A k (f.depth h) i) ≤
          D.ρ k (f.event h i u ∩ C) := by
  classical
  let State := HistoryNode f.nl f.M f.m
  let event : State → Set (α × ℝ) := fun a => f.event a.1 a.2.1 a.2.2
  let root : (Fin (f.nl 0) × Fin f.M) → Set (α × ℝ) := fun r => f.event 0 r.1 r.2
  let rootIndex : (Fin (f.nl 0) × Fin f.M) → State := fun r => ⟨⟨0, by omega⟩, r⟩
  let ancestor : State → (Fin (f.nl 0) × Fin f.M) := fun a => frameHistoryRoot f a.1 a.2.1 a.2.2
  let reference : (h : ℕ) → Fin (f.nl h) → ℝ≥0∞ := fun h i =>
    ENNReal.ofReal (f.ql h) * D.ν k (D.A k (f.depth h) i)
  let weight : State → ℝ≥0∞ := fun a => ENNReal.ofReal θ * reference a.1 a.2.1
  have hsum : ∑ a, weight a < D.ρ k G := by
    apply lt_of_le_of_lt _ hcost
    rw [show (∑ a : State, weight a) = ENNReal.ofReal θ * ∑ a : State, reference a.1 a.2.1 by
      simp only [weight, Finset.mul_sum]]
    exact mul_le_mul' le_rfl (frame_history_reference_budget f hM reference hbudget)
  have hsub : ∀ a : State, event a ⊆ root (ancestor a) := by
    intro a
    obtain ⟨hs, hI⟩ := frameHistoryRoot_subsets f hnest a.1 (by omega) a.2.1 a.2.2
    exact Set.prod_mono hs hI
  have hrootUnique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r' := by
    intro p hp r r' hr hr'
    obtain ⟨hi, hu⟩ := hunique p hp r.1 r'.1 r.2 r'.2 hr hr'
    exact Prod.ext hi hu
  obtain ⟨r, C, hCm, hCne, hCG, hCr, hmass, hdesc⟩ :=
    exists_pruned_parent_history_core (D.ρ k) G hG event
      (fun a => hevent a.1 (by omega) a.2.1 a.2.2) root rootIndex (fun _ => rfl)
      ancestor hsub hrootUnique (fun p hp => by
        obtain ⟨i, u, hi⟩ := hcover p hp 0 (Nat.zero_le _)
        exact ⟨(i, u), hi⟩) weight hsum
  refine ⟨r.1, r.2, C, hCm, hCne, hCG, hCr, ?_,
    (fun p hp => hcover p (hCG hp)), ?_⟩
  · simpa only [weight, reference, ENNReal.ofReal_mul hθ, mul_assoc] using hmass
  · intro h hh i u hne
    let a : State := ⟨⟨h, by omega⟩, i, u⟩
    obtain ⟨p, hpe, hpC⟩ := hne
    have hrootEq : ancestor a = r :=
      hrootUnique p (hCG hpC) _ _ (hsub a hpe) (hCr hpC)
    obtain ⟨hs, hI⟩ := frameHistoryRoot_subsets f hnest h hh i u
    have hancestor : frameHistoryRoot f h i u = r := hrootEq
    rw [hancestor] at hs hI
    refine ⟨hI, hs, ?_⟩
    simpa only [a, event, weight, reference, ENNReal.ofReal_mul hθ, mul_assoc] using (hdesc a ⟨p, hpe, hpC⟩).2

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
