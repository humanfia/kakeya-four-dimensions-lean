-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PriorityCandidates.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySets
import Submission.Obl.k4_quadratic_finite_greedy_cover.DerivativeLoss

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

def candidateCylinder {C : ℕ} (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (j : Fin C → ℕ) (a : CandidateDatum C) : Set Incidence :=
  a.trajectories ×ˢ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
    (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent))

/-- Assign the entire eligible envelope after deleting earlier trajectory
assignments at this old packet. The original matched incidence mask is retained. -/
noncomputable def priorityClip
    (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (S : Finset (CandidateDatum C)) (a : CandidateDatum C) : CandidateDatum C :=
  { a with trajectories := candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a \
      selectedUnion S CandidateDatum.parent CandidateDatum.trajectories a.parent }

/-- Discovery on the residual of all earlier full trajectory cylinders retains
its complete original mass witness after clipping to a disjoint assignment. -/
theorem priorityClip_certificate
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H₀ : Fin W → Set Incidence) (S : Finset (CandidateDatum C)) (a : CandidateDatum C)
    (hSm : ∀ b ∈ S, MeasurableSet b.trajectories) (hAm : MeasurableSet (A a.parent))
    (hg : CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a)
    (hc : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A
      (fun w => H₀ w \ selectedUnion S (fun b => γ b.parent) (candidateCylinder T lev j) w) a) :
    let a' := priorityClip Nk L W C B ρ gain ε r T lev γ j A S a
    CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a' ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a' := by
  let E := candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a
  let U := selectedUnion S CandidateDatum.parent CandidateDatum.trajectories a.parent
  let a' := priorityClip Nk L W C B ρ gain ε r T lev γ j A S a
  change CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a' ∧
    CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a'
  have hEm : MeasurableSet E := candidateEnvelope_measurable Nk L W C B ρ gain ε
    r T lev γ j A a hg.2.2.2.1 hAm
  have hUm : MeasurableSet U := selectedUnion_measurable S
    CandidateDatum.parent CandidateDatum.trajectories hSm a.parent
  have henv : ∀ p ∈ a.counted, p.1 ∈ E :=
    counted_subset_candidateEnvelope Nk L W C Mc ν B d₁ ρ gain ε r T lev γ j A _ a hg hc
  have hnewLine : ∀ p ∈ a.counted, p.1 ∈ E \ U := by
    intro p hp
    refine ⟨henv p hp, ?_⟩
    intro hprior
    obtain ⟨b, hb, hba, hline⟩ := mem_iUnion₂.mp hprior
    have hpt := hc.2.2.1 p hp
    have htime : p ∈ candidateCylinder T lev j b := by
      refine ⟨hline, ?_⟩
      simpa only [hba] using hpt.2.1
    have hcovered : p ∈ selectedUnion S (fun b => γ b.parent)
        (candidateCylinder T lev j) (γ a.parent) :=
      mem_iUnion₂.mpr ⟨b, hb, congrArg γ hba, htime⟩
    exact (hc.2.1 hp).2 hcovered
  have hGnew : CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a' := by
    obtain ⟨hgain, hcap, hroom, hdeg, hcoeff, _, _, _⟩ := hg
    refine ⟨hgain, hcap, hroom, hdeg, hcoeff, hEm.diff hUm, ?_, ?_⟩
    · exact fun l hl => hl.1.1
    · intro l hl t ht
      have he := hl.1.2
      exact ⟨he.1 t ht, he.2.1 t ht, he.2.2.1 t ht⟩
  refine ⟨hGnew, hc.1, ?_, ?_, hc.2.2.2⟩
  · exact fun p hp => (hc.2.1 hp).1
  · intro p hp
    have hpt := hc.2.2.1 p hp
    exact ⟨hnewLine p hp, hpt.2⟩

end Submission.Obl.k4_quadratic_finite_greedy_cover
