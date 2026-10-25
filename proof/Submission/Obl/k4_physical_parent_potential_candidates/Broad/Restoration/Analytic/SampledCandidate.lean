-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/SampledCandidate.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/SampledCandidate.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/SampledCandidate.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SampledBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MeasureTheory

/-- The geometric output, before the finite dense-set jet theorem is applied.
No new test polynomial or global jet estimate is part of this certificate. -/
def sampledCandidate (Cloc J D : ℕ) (Nk L : ℝ) (W : ℕ)
    (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event) : Prop :=
  ∃ (b : Fin C) (actualGain : ℝ) (Mz MH : ℕ) (d : SampledBranchData Cloc J D)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (η : ℝ) (A' : Set Line) (S : Line → Set ℝ) (counted : Set Event),
    gain ≤ actualGain ∧ actualGain ≤ 1 / 8 ∧
    r (lev b) + 2 * actualGain * L ≤ L ∧
    0 < B (γ b) ∧ 0 < η ∧ η ≤ 1 ∧
    Mz * Cloc + 2 * MH + 11 ≤ Mc ∧
    d.Z ≤ Nk ^ Mz ∧ (∀ i, |c i| ≤ Nk ^ MH) ∧
    (∀ i k, |M i k| ≤ Nk ^ MH) ∧ |B (γ b)| ≤ Nk ^ MH ∧
    d.b = dyadicThickness Nk (r (lev b) + actualGain * L) ∧
    restorationRemezFactor η * (d.A ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) ∧
    MeasurableSet A' ∧ A' ⊆ A b ∧
    (∀ l ∈ A', S l ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l)) ∧
    (∀ l ∈ A', ∀ t ∈ S l,
      pointOfCoordinates (coordinateMap c M (B (γ b))
        (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) +
          ((2 : ℝ) ^ T (lev b))⁻¹ * t))) ∈ d.region) ∧
    (counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      pointOfCoordinates (coordinateMap c M (B (γ b)) (graphPoint p.1 p.2)) ∈ d.region}) ∧
    ENNReal.ofReal (Nk ^ (-((d₁ * actualGain + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted

theorem sampledCandidate_implies_normalized
    {Cloc J D : ℕ} (hjet : DenseJetBound D J)
    (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event)
    (h : sampledCandidate Cloc J D Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    normalizedCandidate Cloc Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨b, ag, Mz, MH, d, c, M, η, A', S, counted,
    hgain, hgain8, hdepth, hB, hη, hη1, hformat, hZ, hc, hM, hBsize,
    hthickness, hbudget, hA'meas, hA'sub, hSwit, hwitness, hcounted, hmass⟩ := h
  refine ⟨b, ag, Mz, MH, d.toLocal hjet, c, M, η, A', S, counted,
    hgain, hgain8, hdepth, hB, hη, hη1, hformat, hZ, hc, hM, hBsize,
    hthickness, hbudget, hA'meas, hA'sub, hSwit, ?_, ?_, hmass⟩
  · intro l hl t ht
    exact d.region_subset hjet (hwitness l hl t ht)
  · intro p hp
    obtain ⟨hpH, hpA, hpt, hpregion⟩ := hcounted hp
    exact ⟨hpH, hpA, hpt, d.region_subset hjet hpregion⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
