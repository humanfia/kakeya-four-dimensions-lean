-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.NormalizedCandidate, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/NormalizedCandidate.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/NormalizedCandidate.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/NormalizedCandidate.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/NormalizedCandidate.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.PacketCandidate

/-! A precise interface between geometric branch extraction and restoration. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial MeasureTheory

/-- A normalized branch certificate. It contains no new test polynomial: the
local restoration hypothesis supplies that polynomial only after this
certificate is produced. All incidence masses use the original prior. -/
def normalizedCandidate (Cloc : ℕ) (Nk L : ℝ) (W : ℕ)
    (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event) : Prop :=
  ∃ (b : Fin C) (actualGain : ℝ) (Mz MH : ℕ) (D : LocalBranchData Cloc)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (η : ℝ) (A' : Set Line) (S : Line → Set ℝ) (counted : Set Event),
    gain ≤ actualGain ∧ actualGain ≤ 1 / 8 ∧
    r (lev b) + 2 * actualGain * L ≤ L ∧
    0 < B (γ b) ∧ 0 < η ∧ η ≤ 1 ∧
    Mz * Cloc + 2 * MH + 11 ≤ Mc ∧
    D.Z ≤ Nk ^ Mz ∧ (∀ i, |c i| ≤ Nk ^ MH) ∧
    (∀ i k, |M i k| ≤ Nk ^ MH) ∧ |B (γ b)| ≤ Nk ^ MH ∧
    D.b = dyadicThickness Nk (r (lev b) + actualGain * L) ∧
    restorationRemezFactor η * D.A ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) ∧
    MeasurableSet A' ∧ A' ⊆ A b ∧
    (∀ l ∈ A', S l ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l)) ∧
    (∀ l ∈ A', ∀ t ∈ S l,
      pointOfCoordinates (coordinateMap c M (B (γ b))
        (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) +
          ((2 : ℝ) ^ T (lev b))⁻¹ * t))) ∈ D.region) ∧
    (counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      pointOfCoordinates (coordinateMap c M (B (γ b)) (graphPoint p.1 p.2)) ∈ D.region}) ∧
    ENNReal.ofReal (Nk ^ (-((d₁ * actualGain + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted

/-- The restoration output and all whole-block bookkeeping have been discharged. -/
theorem normalizedCandidate_implies_candidate
    (Cloc : ℕ) (hr : ∀ D : LocalBranchData Cloc, ∃ Q, D.restored Q)
    (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event) (hN : 2 ≤ Nk)
    (h : normalizedCandidate Cloc Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    residualCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨b, actualGain, Mz, MH, D, c, M, η, A', S, counted,
    hgain, hgain8, hdepth, hB, hη, hη1, hformat, hZ, hc, hM, hBsize,
    hthickness, hbudget, hA'meas, hA'sub, hSwit, hwitness, hcounted, hmass⟩ := h
  exact residualCandidate_of_normalized_branch Nk L W ν B Mc d₁ ρ gain ε r T
    C lev γ j A H b actualGain hgain hgain8 hdepth Cloc Mz MH D (hr D)
    c M η A' S counted hN hB hη hη1 hformat hZ hc hM hBsize hthickness hbudget
    hA'meas hA'sub hSwit hwitness hcounted hmass

/-- The local assertion chooses one exponent which then works for every
normalized packet certificate, regardless of the source's Boolean format. -/
theorem local_restoration_supplies_candidate_conversion (h : LocalRestorationAssertion) :
    ∃ Cloc : ℕ, 1 ≤ Cloc ∧
      ∀ (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Line) (B : Fin W → ℝ)
        (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
        (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
        (A : Fin C → Set Line) (H : Fin W → Set Event), 2 ≤ Nk →
        normalizedCandidate Cloc Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H →
        residualCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨Cloc, hCloc, hr⟩ := apply_local_restoration h
  exact ⟨Cloc, hCloc, normalizedCandidate_implies_candidate Cloc hr⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
