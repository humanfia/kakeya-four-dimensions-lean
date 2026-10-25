-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PathPriority.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySelection

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- Full priority candidate coverage at the exact supplied saturated path.
All original-law mass witnesses and finite priority representations are retained. -/
theorem path_priority_cover
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Trajectory)
    (F : Fin C → Set Incidence)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (Exit : Prop)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hω : ∀ w, 0 ≤ ω w) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hE : ∀ w, E w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1) (hm : 0 < m)
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst)
    (hdiscovery : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ terminalUnion m lev γ F w) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) →
      Exit ∨ candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    Exit ∨ ∃ H₀ : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H₀ w) ∧ H₀ w ⊆ terminalUnion m lev γ F w ∧
        (ν w).prod volume (H₀ w) ≠ ∞) ∧
      κ⁻¹ ≤ ∑ w, ω w * ((ν w).prod volume).real (H₀ w) ∧
      ∃ S : Finset (CandidateDatum C),
      (∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
        CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
        Disjoint a.trajectories a'.trajectories) ∧
      (∀ a ∈ S, ∃ P : Finset (CandidateDatum C), P ⊆ S ∧
        a.trajectories = candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a \
          selectedUnion P CandidateDatum.parent
            (candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A) a.parent) ∧
      κ⁻¹ / 2 ≤ ∑ w, ω w * ((ν w).prod volume).real
        (H₀ w ∩ selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j) w) := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  obtain ⟨hUpos, hUfin⟩ := path_packetRegion_budget Nk L W ω ν E B f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst hN hν hp
  obtain ⟨H₀, hH₀, hmass₀⟩ := path_terminal_residual Nk L W ω ν E B f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst hm hp
  have hnodes := hp.2.2.2.2.2.2.2
  have hAm (b : Fin C) : MeasurableSet (A b) := by
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, hA, _⟩
    exact hA
  have hAfin (b : Fin C) : ν (γ b) (A b) ≠ ∞ := by finiteness
  have hApos (b : Fin C) : 0 < (ν (γ b)).real (A b) := by
    have hb := hUpos b
    rw [measureReal_def, packetRegion_measure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 : ℝ) ^ T (lev b))] at hb
    exact pos_of_mul_pos_left hb (by positivity)
  have hHfin (w : Fin W) : (ν w).prod volume (H₀ w) ≠ ∞ := by
    have hsub : H₀ w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨b, _, hb, hpb⟩ := (hH₀ w).2 hp
      rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
      apply hE w
      simpa only [hb] using (hF p hpb).1
    exact measure_ne_top_of_subset hsub (by simp)
  have hmassreal : κ⁻¹ ≤ ∑ w, ω w * ((ν w).prod volume).real (H₀ w) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg
      (fun w _ => mul_nonneg (hω w) measureReal_nonneg))).mp
    rw [ofReal_weighted_mass (fun w => (ν w).prod volume) ω H₀ hω hHfin]
    exact hmass₀
  have hdisc : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ H₀ w) →
      (∑ w, ω w * ((ν w).prod volume).real (H₀ w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (H w) →
      Exit ∨ candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
    intro H hH hmass
    apply hdiscovery H (fun w => ⟨(hH w).1, (hH w).2.trans (hH₀ w).2⟩)
    rw [← ofReal_weighted_mass (fun w => (ν w).prod volume) ω H hω
      (fun w => measure_ne_top_of_subset (hH w).2 (hHfin w))]
    exact ENNReal.ofReal_le_ofReal ((by linarith : κ⁻¹ / 2 ≤
      (∑ w, ω w * ((ν w).prod volume).real (H₀ w)) / 2).trans hmass)
  rcases priority_candidate_selection Nk L W C Mc ω ν B d₁ ρ gain ε r T lev γ j A H₀ Exit
    hN hL hd₁ hAm hApos hAfin (fun w => (hH₀ w).1) hHfin hdisc with
    hex | ⟨S, hS, hd, hu, hrep, hcov⟩
  · exact Or.inl hex
  · exact Or.inr ⟨H₀, (fun w => ⟨(hH₀ w).1, (hH₀ w).2, hHfin w⟩), hmassreal,
      S, hS, hd, hrep, le_trans (by linarith : κ⁻¹ / 2 ≤
        (∑ w, ω w * ((ν w).prod volume).real (H₀ w)) / 2) hcov⟩

end Submission.Obl.k4_quadratic_finite_greedy_cover
