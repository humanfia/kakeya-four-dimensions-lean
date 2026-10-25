-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/FixedLevel.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.CountedRecovery
import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySelection

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- Full trajectory priority assignments inherit the old disjointness at a
fixed path level and world/time index. -/
theorem priority_fixed_level_disjoint
    (W C : ℕ) (S : Finset (CandidateDatum C)) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (i : ℕ)
    (hlev : ∀ a ∈ S, lev a.parent = i)
    (hsub : ∀ a ∈ S, a.trajectories ⊆ A a.parent)
    (hpriority : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
      Disjoint a.trajectories a'.trajectories)
    (hold : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b')) :
    ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → γ a.parent = γ a'.parent → j a.parent = j a'.parent →
      Disjoint a.trajectories a'.trajectories := by
  intro a ha a' ha' hne hworld htime
  by_cases hparent : a.parent = a'.parent
  · exact hpriority a ha a' ha' hne hparent
  · exact (hold _ _ hparent ((hlev a ha).trans (hlev a' ha').symm) hworld htime).mono
      (hsub a ha) (hsub a' ha')

/-- Every trajectory left by a priority rule has the original lower derivative
witness somewhere in its old block. -/
theorem priority_large_derivative
    (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (a : CandidateDatum C)
    (hsub : a.trajectories ⊆ candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a) :
    ∀ l ∈ a.trajectories, ∃ t ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
      (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent)),
      B (γ a.parent) / Nk ^ (ρ * gain * L + ε) ≤
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) a.test)| := by
  intro l hl
  exact (hsub hl).2.2.2.2

/-- Half-open counted packets at a common depth are disjoint within each
world, even when their polynomials and derivative cutoffs differ. -/
theorem countedPacket_disjoint {ι : Type*}
    (A : ι → Set Trajectory) (R : ι → MvPolynomial (Fin 4) ℝ)
    (b : ι → ℝ) (j : ι → ℕ) (T : ℕ) (H : ι → Set Incidence)
    (a a' : ι) (hdisj : j a = j a' → Disjoint (A a) (A a')) :
    Disjoint (countedPacket (H a) (A a) (R a) (b a) T (j a))
      (countedPacket (H a') (A a') (R a') (b a') T (j a')) := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  rcases lt_trichotomy (j a) (j a') with hj | hj | hj
  · have hjR : (j a : ℝ) + 1 ≤ (j a' : ℝ) := by exact_mod_cast hj
    have hh := div_le_div_of_nonneg_right hjR (by positivity : 0 ≤ (2 : ℝ) ^ T)
    exact (not_lt_of_ge (le_trans hh hp'.2.2.1.1)) hp.2.2.1.2
  · exact Set.disjoint_left.mp (hdisj hj) hp.2.1 hp'.2.1
  · have hjR : (j a' : ℝ) + 1 ≤ (j a : ℝ) := by exact_mod_cast hj
    have hh := div_le_div_of_nonneg_right hjR (by positivity : 0 ≤ (2 : ℝ) ^ T)
    exact (not_lt_of_ge (le_trans hh hp.2.2.1.1)) hp'.2.2.1.2

/-- Finite-set version of the common-level original-law recovery estimate. -/
theorem finite_family_counted_recovery {ι : Type*}
    (S : Finset ι) (W : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (γ : ι → Fin W) (j : ι → ℕ) (T : ℕ) (A : ι → Set Trajectory)
    (R : ι → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (K : ℝ)
    (H₀ H : Fin W → Set Incidence)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hAm : ∀ a ∈ S, MeasurableSet (A a))
    (hR : ∀ a ∈ S, (R a).totalDegree ≤ 2) (hB : ∀ w, 0 < B w) (hK : 2 ≤ K)
    (hj : ∀ a ∈ S, j a < 2 ^ T) (hsubH : ∀ w, H₀ w ⊆ H w)
    (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a'))
    (hlarge : ∀ a ∈ S, ∀ l ∈ A a, ∃ t ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
      (((j a : ℝ) + 1) / (2 : ℝ) ^ T),
      B (γ a) / K ≤ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R a))|) :
    (∑ a ∈ S, ω (γ a) * ((ν (γ a)).prod volume).real
      (H₀ (γ a) ∩ (A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
        (((j a : ℝ) + 1) / (2 : ℝ) ^ T)))) ≤
    (∑ a ∈ S, ω (γ a) * ((ν (γ a)).prod volume).real
      (countedPacket (H (γ a)) (A a) (R a) (B (γ a) / K ^ 4) T (j a))) + 8 / K ^ 3 := by
  classical
  have hh := family_counted_recovery W ν ω (fun a : S => γ a) (fun a : S => j a) T
    (fun a : S => A a) (fun a : S => R a) B K H₀ H hν hω hωsum
    (fun a => hAm a a.property) (fun a => hR a a.property) hB hK
    (fun a => hj a a.property) hsubH hHfin
    (fun a a' hne hw hj => hdisj a a.property a' a'.property
      (fun heq => hne (Subtype.ext heq)) hw hj)
    (fun a => hlarge a a.property)
  rw [Finset.sum_coe_sort S (fun a => ω (γ a) * ((ν (γ a)).prod volume).real
      (H₀ (γ a) ∩ (A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
        (((j a : ℝ) + 1) / (2 : ℝ) ^ T)))),
    Finset.sum_coe_sort S (fun a => ω (γ a) * ((ν (γ a)).prod volume).real
      (countedPacket (H (γ a)) (A a) (R a) (B (γ a) / K ^ 4) T (j a)))] at hh
  exact hh

end Submission.Obl.k4_quadratic_finite_greedy_cover
