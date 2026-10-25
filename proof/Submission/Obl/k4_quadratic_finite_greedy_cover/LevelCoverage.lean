-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/LevelCoverage.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.MenuSelection
import Submission.Obl.k4_quadratic_finite_greedy_cover.FixedLevel

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- The full priority family has a nonempty fixed-level, fixed-gain subfamily
whose original-law counted mass loses only the fixed menu factor and 8/K^3. -/
theorem candidate_level_gain_counted_mass
    (Nk L : ℝ) (W C Mc m : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (B : Fin W → ℝ) (ρ gain ε c : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H₀ H : Fin W → Set Incidence) (S : Finset (CandidateDatum C))
    (hm : 0 < m) (hgain : 0 ≤ gain) (hstep : 0 < ρ * gain) (hc : 0 < c)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hB : ∀ w, 0 < B w)
    (hK : 2 ≤ Nk ^ (ρ * gain * L + ε))
    (hlevel : ∀ b, lev b < m) (hj : ∀ b, j b < 2 ^ T (lev b))
    (hHsub : ∀ w, H₀ w ⊆ H w) (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hS : ∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a)
    (henv : ∀ a ∈ S, a.trajectories ⊆ candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a)
    (hpriority : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
      Disjoint a.trajectories a'.trajectories)
    (hold : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hcover : c ≤ ∑ w, ω w * ((ν w).prod volume).real
      (H₀ w ∩ selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j) w)) :
    ∃ i < m, ∃ z < ⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1,
      ∃ U : Finset (CandidateDatum C),
      U = S.filter (fun a => lev a.parent = i ∧ gainMenuIndex gain (ρ * gain) a.gain = z) ∧
      U.Nonempty ∧
      (∀ a ∈ U, lev a.parent = i ∧
        gain ≤ gain + (z : ℝ) * (ρ * gain) ∧
        gain + (z : ℝ) * (ρ * gain) ≤ a.gain ∧
        a.gain < gain + (z : ℝ) * (ρ * gain) + ρ * gain) ∧
      c / ((m * (⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1) : ℕ) : ℝ) -
        8 / (Nk ^ (ρ * gain * L + ε)) ^ 3 ≤
        ∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
          (countedPacket (H (γ a.parent)) a.trajectories a.test
            (B (γ a.parent) / (Nk ^ (ρ * gain * L + ε)) ^ 4) (T i) (j a.parent)) := by
  classical
  obtain ⟨i, hi, z, hz, hmass⟩ := candidate_level_gain_mass W C m ν ω H₀ S T lev γ j
    gain (ρ * gain) c hm hω hstep hgain (fun a ha => hlevel a.parent)
    (fun a ha => ⟨(hS a ha).1, (hS a ha).2.1⟩) hcover
  let U := S.filter (fun a => lev a.parent = i ∧ gainMenuIndex gain (ρ * gain) a.gain = z)
  have hUS : U ⊆ S := Finset.filter_subset _ _
  have hUi (a : CandidateDatum C) (ha : a ∈ U) : lev a.parent = i :=
    (Finset.mem_filter.mp ha).2.1
  have hsumpos : 0 < ∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
      (H₀ (γ a.parent) ∩ candidateCylinder T lev j a) := by
    have hden : 0 < ((m * (⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hm (by omega : 0 < ⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1)
    exact (div_pos hc hden).trans_le hmass
  have hUne : U.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hsumpos
    exact (lt_irrefl 0) hsumpos
  have hdisj := priority_fixed_level_disjoint W C U lev γ j A i hUi
    (fun a ha => (hS a (hUS ha)).2.2.2.2.2.2.1)
    (fun a ha a' ha' => hpriority a (hUS ha) a' (hUS ha')) hold
  have hrecovery := finite_family_counted_recovery U W ν ω (fun a => γ a.parent)
    (fun a => j a.parent) (T i) CandidateDatum.trajectories CandidateDatum.test B
    (Nk ^ (ρ * gain * L + ε)) H₀ H hν hω hωsum
    (fun a ha => (hS a (hUS ha)).2.2.2.2.2.1)
    (fun a ha => (hS a (hUS ha)).2.2.2.1) hB hK
    (fun a ha => by simpa only [hUi a ha] using hj a.parent) hHsub hHfin hdisj
    (fun a ha => by
      simpa only [hUi a ha] using priority_large_derivative Nk L W C B ρ gain ε r T lev γ j A a
        (henv a (hUS ha)))
  refine ⟨i, hi, z, hz, U, rfl, hUne, ?_, ?_⟩
  · intro a ha
    have hbin := (Finset.mem_filter.mp ha).2.2
    have hb := menuGain_bounds gain (ρ * gain) a.gain hstep (hS a (hUS ha)).1
    refine ⟨hUi a ha, ?_⟩
    simpa only [menuGain, hbin] using hb
  · have heq : (∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
        (H₀ (γ a.parent) ∩ candidateCylinder T lev j a)) =
        ∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
          (H₀ (γ a.parent) ∩ (a.trajectories ×ˢ
            Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i))) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [candidateCylinder, hUi a ha]
    rw [heq] at hmass
    linarith

end Submission.Obl.k4_quadratic_finite_greedy_cover
