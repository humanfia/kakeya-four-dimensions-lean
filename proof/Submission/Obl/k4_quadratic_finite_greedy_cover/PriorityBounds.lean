-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PriorityBounds.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySelection

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- The full priority family has a polynomial count, using the same normalized
original-packet budget that makes greedy selection terminate. -/
theorem priority_family_card_bound
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (S : Finset (CandidateDatum C))
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b)) (hAfin : ∀ b, ν (γ b) (A b) ≠ ∞)
    (hS : ∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
      Disjoint a.trajectories a'.trajectories) :
    (S.card : ℝ) ≤ (C : ℝ) * Nk ^ ((d₁ / 8 + ρ * gain) * L + ε) := by
  classical
  let θ := Nk ^ (-((d₁ / 8 + ρ * gain) * L) - ε)
  let weight : CandidateDatum C → ℝ := fun a =>
    (ν (γ a.parent)).real a.trajectories / (ν (γ a.parent)).real (A a.parent)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hpieces : ∀ a ∈ S, MeasurableSet a.trajectories ∧ a.trajectories ⊆ A a.parent := by
    intro a ha
    rcases (hS a ha).1 with ⟨_, _, _, _, _, hm, hsub, _⟩
    exact ⟨hm, hsub⟩
  have hbudget : (∑ a ∈ S, weight a) ≤ (C : ℝ) := by
    simpa only [weight, Fintype.card_fin] using
      normalized_assignment_budget (fun b => ν (γ b)) A CandidateDatum.parent
        CandidateDatum.trajectories hApos hAfin S hpieces hdisj
  have hfloor : ∀ a ∈ S, θ ≤ weight a := by
    intro a ha
    have hf := candidate_trajectory_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε (1 / 8)
      T lev γ j A H a hN hL hd₁ (hS a ha).1.2.1 (hS a ha).2
    apply normalized_measure_floor (ν (γ a.parent)) (A a.parent) a.trajectories
      (hApos a.parent) (hAfin a.parent) (hpieces a ha).2 hθ.le
    simpa only [mul_one_div] using hf
  have hsum : (S.card : ℝ) * θ ≤ ∑ a ∈ S, weight a := by
    calc
      _ = ∑ _a ∈ S, θ := by simp
      _ ≤ _ := Finset.sum_le_sum hfloor
  have hinv : θ⁻¹ = Nk ^ ((d₁ / 8 + ρ * gain) * L + ε) := by
    rw [← Real.rpow_neg (le_trans zero_le_one hN)]
    congr 1
    ring
  have hh : (S.card : ℝ) ≤ (C : ℝ) / θ := (le_div_iff₀ hθ).mpr (hsum.trans hbudget)
  simpa only [div_eq_mul_inv, hinv] using hh

/-- Within an old packet, each fixed upper gain endpoint has its own sharp
count bound under the original trajectory prior. -/
theorem priority_parent_card_gain_le
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε hmax : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (S : Finset (CandidateDatum C))
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hS : ∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
      Disjoint a.trajectories a'.trajectories)
    (b : Fin C) (hApos : 0 < (ν (γ b)).real (A b)) (hAfin : ν (γ b) (A b) ≠ ∞) :
    ((S.filter (fun a => a.parent = b ∧ a.gain ≤ hmax)).card : ℝ) ≤
      Nk ^ ((d₁ * hmax + ρ * gain) * L + ε) := by
  classical
  let t := S.filter (fun a => a.parent = b ∧ a.gain ≤ hmax)
  let θ := Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hpieces : ∀ a ∈ t, MeasurableSet a.trajectories ∧ a.trajectories ⊆ A b := by
    intro a ha
    have has := (Finset.mem_filter.mp ha).1
    have hab := (Finset.mem_filter.mp ha).2.1
    rcases (hS a has).1 with ⟨_, _, _, _, _, hm, hsub, _⟩
    exact ⟨hm, by simpa only [hab] using hsub⟩
  have hd : (t : Set (CandidateDatum C)).PairwiseDisjoint CandidateDatum.trajectories := by
    intro a ha a' ha' hne
    exact hdisj a (Finset.mem_filter.mp ha).1 a' (Finset.mem_filter.mp ha').1 hne
      ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp ha').2.1.symm)
  have hf : ∀ a ∈ t, ENNReal.ofReal θ * ν (γ b) (A b) ≤ ν (γ b) a.trajectories := by
    intro a ha
    have has := (Finset.mem_filter.mp ha).1
    have hab := (Finset.mem_filter.mp ha).2.1
    have hgain := (Finset.mem_filter.mp ha).2.2
    have hh := candidate_trajectory_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε hmax
      T lev γ j A H a hN hL hd₁ hgain (hS a has).2
    simpa only [hab] using hh
  have hcard := card_le_inv_relative_floor (ν (γ b)) (A b)
    CandidateDatum.trajectories t hθ hApos hAfin hpieces hd hf
  have hinv : θ⁻¹ = Nk ^ ((d₁ * hmax + ρ * gain) * L + ε) := by
    rw [← Real.rpow_neg (le_trans zero_le_one hN)]
    congr 1
    ring
  exact hcard.trans_eq hinv

end Submission.Obl.k4_quadratic_finite_greedy_cover
