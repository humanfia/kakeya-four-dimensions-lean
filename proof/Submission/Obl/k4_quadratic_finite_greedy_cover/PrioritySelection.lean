-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PrioritySelection.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.PriorityCandidates

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- Finite greedy selection by full eligible trajectory assignments. The
original matched masks remain as witnesses; the stop rule uses the enlarged
trajectory cylinders. Priority representations retain polynomial Boolean cost. -/
theorem priority_candidate_selection
    (Nk L : ℝ) (W C Mc : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H₀ : Fin W → Set Incidence) (Exit : Prop)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hAm : ∀ b, MeasurableSet (A b))
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b)) (hAfin : ∀ b, ν (γ b) (A b) ≠ ∞)
    (hHm : ∀ w, MeasurableSet (H₀ w)) (hHfin : ∀ w, (ν w).prod volume (H₀ w) ≠ ∞)
    (hdiscovery : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ H₀ w) →
      (∑ w, ω w * ((ν w).prod volume).real (H₀ w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (H w) →
      Exit ∨ candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    Exit ∨ ∃ S : Finset (CandidateDatum C),
      (∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
        CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
        Disjoint a.trajectories a'.trajectories) ∧
      (∀ b, selectedUnion S CandidateDatum.parent CandidateDatum.trajectories b =
        selectedUnion S CandidateDatum.parent
          (candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A) b) ∧
      (∀ a ∈ S, ∃ P : Finset (CandidateDatum C), P ⊆ S ∧
        a.trajectories = candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a \
          selectedUnion P CandidateDatum.parent
            (candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A) a.parent) ∧
      (∑ w, ω w * ((ν w).prod volume).real (H₀ w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real
          (H₀ w ∩ selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j) w) := by
  classical
  let E := candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A
  let μ : Fin W → Measure Incidence := fun w => (ν w).prod volume
  let Good : CandidateDatum C → Prop := fun a =>
    CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a
  let P : Finset (CandidateDatum C) → Prop := fun S =>
    (∀ a ∈ S, Good a) ∧
    (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent → Disjoint a.trajectories a'.trajectories) ∧
    (∀ b, selectedUnion S CandidateDatum.parent CandidateDatum.trajectories b =
      selectedUnion S CandidateDatum.parent E b) ∧
    ∀ a ∈ S, ∃ P' : Finset (CandidateDatum C), P' ⊆ S ∧
      a.trajectories = E a \ selectedUnion P' CandidateDatum.parent E a.parent
  let Stop : Finset (CandidateDatum C) → Prop := fun S =>
    (∑ w, ω w * (μ w).real (H₀ w)) / 2 ≤
      ∑ w, ω w * (μ w).real
        (H₀ w ∩ selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j) w)
  let weight : CandidateDatum C → ℝ := fun a =>
    (ν (γ a.parent)).real a.trajectories / (ν (γ a.parent)).real (A a.parent)
  let θ : ℝ := Nk ^ (-((d₁ / 8 + ρ * gain) * L) - ε)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hline_meas (S : Finset (CandidateDatum C)) (hs : P S) :
      ∀ a ∈ S, MeasurableSet a.trajectories := by
    intro a ha
    rcases (hs.1 a ha).1 with ⟨_, _, _, _, _, hmeas, _⟩
    exact hmeas
  have hbudget (S : Finset (CandidateDatum C)) (hs : P S) :
      (∑ a ∈ S, weight a) ≤ (C : ℝ) := by
    have hpiece : ∀ a ∈ S, MeasurableSet a.trajectories ∧ a.trajectories ⊆ A a.parent := by
      intro a ha
      rcases (hs.1 a ha).1 with ⟨_, _, _, _, _, hm, hsub, _⟩
      exact ⟨hm, hsub⟩
    simpa only [weight, Fintype.card_fin] using
      normalized_assignment_budget (fun b => ν (γ b)) A CandidateDatum.parent
        CandidateDatum.trajectories hApos hAfin S hpiece hs.2.1
  have hstep (S : Finset (CandidateDatum C)) (hs : P S) (hstop : ¬ Stop S) :
      Exit ∨ ∃ a, a ∉ S ∧ P (insert a S) ∧ θ ≤ weight a := by
    let Cov := selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j)
    let H : Fin W → Set Incidence := fun w => H₀ w \ Cov w
    have hCovm (w : Fin W) : MeasurableSet (Cov w) := by
      apply selectedUnion_measurable
      intro a ha
      exact (hline_meas S hs a ha).prod measurableSet_Icc
    have hHmeas (w : Fin W) : MeasurableSet (H w) := (hHm w).diff (hCovm w)
    have hbalance :
        (∑ w, ω w * (μ w).real (H w)) +
          (∑ w, ω w * (μ w).real (H₀ w ∩ Cov w)) =
            ∑ w, ω w * (μ w).real (H₀ w) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_add]
      congr 1
      exact measureReal_sdiff_add_inter (μ := μ w) (s := H₀ w) (hCovm w) (hHfin w)
    have hHmass : (∑ w, ω w * (μ w).real (H₀ w)) / 2 ≤
        ∑ w, ω w * (μ w).real (H w) := by
      dsimp [Stop] at hstop
      linarith [lt_of_not_ge hstop]
    rcases hdiscovery H (fun w => ⟨hHmeas w, sdiff_subset⟩) hHmass with hex | hc
    · exact Or.inl hex
    obtain ⟨a, hg, hc⟩ := candidate_has_counted_data Nk L W C Mc ν B d₁ ρ gain ε
      r T lev γ j A H hHmeas hc
    let a' := priorityClip Nk L W C B ρ gain ε r T lev γ j A S a
    have hcert : Good a' := priorityClip_certificate Nk L W C Mc ν B d₁ ρ gain ε
      r T lev γ j A H₀ S a (hline_meas S hs) (hAm a.parent) hg hc
    have hnewset : a'.trajectories = E a' \
        selectedUnion S CandidateDatum.parent CandidateDatum.trajectories a'.parent := rfl
    have hinc : θ ≤ weight a' := by
      have hf := candidate_trajectory_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε (1 / 8)
        T lev γ j A H₀ a' hN hL hd₁ hcert.1.2.1 hcert.2
      rcases hcert.1 with ⟨_, _, _, _, _, _, hsub, _⟩
      apply normalized_measure_floor (ν (γ a'.parent)) (A a'.parent) a'.trajectories
        (hApos a'.parent) (hAfin a'.parent) hsub hθ.le
      simpa only [mul_one_div] using hf
    have hfresh : a' ∉ S := by
      intro ha'
      have hempty : a'.trajectories = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        have hnot := (show l ∈ E a' \ selectedUnion S CandidateDatum.parent
          CandidateDatum.trajectories a'.parent from hnewset ▸ hl).2
        exact hnot (mem_iUnion₂.mpr ⟨a', ha', rfl, hl⟩)
      have hz : weight a' = 0 := by simp [weight, hempty]
      rw [hz] at hinc
      exact (not_le_of_gt hθ) hinc
    have hdisnew := priority_disjoint_insert S CandidateDatum.parent
      CandidateDatum.trajectories E a' hs.2.1 hnewset
    have hunionnew := priority_union_insert S CandidateDatum.parent
      CandidateDatum.trajectories E a' hs.2.2.1 hnewset
    refine Or.inr ⟨a', hfresh, ⟨?_, hdisnew, hunionnew, ?_⟩, hinc⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with hba | hbs
      · simpa only [hba] using hcert
      · exact hs.1 b hbs
    · intro b hb
      rcases Finset.mem_insert.mp hb with hba | hbs
      · subst b
        refine ⟨S, Finset.subset_insert _ _, ?_⟩
        rw [← hs.2.2.1 a'.parent]
        exact hnewset
      · obtain ⟨P', hP', hrep⟩ := hs.2.2.2 b hbs
        exact ⟨P', hP'.trans (Finset.subset_insert _ _), hrep⟩
  rcases finite_selection_or_exit weight P Stop Exit hθ
      (by simp [P, selectedUnion]) hbudget hstep with hex | ⟨S, hs, hstop⟩
  · exact Or.inl hex
  · exact Or.inr ⟨S, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hstop⟩

end Submission.Obl.k4_quadratic_finite_greedy_cover
