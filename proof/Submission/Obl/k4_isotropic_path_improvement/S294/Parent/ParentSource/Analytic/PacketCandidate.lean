-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.PacketCandidate, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/PacketCandidate.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/PacketCandidate.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/PacketCandidate.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/PacketCandidate.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.PacketRestoration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.Candidate

/-! Construct the exact residual candidate from a prepared normalized branch. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial MeasureTheory

/-- All mass in this implication is measured against the original packet prior.
The normalized branch and witness data contain the geometric content; the
restored polynomial is constructed after these data have been fixed. -/
theorem residualCandidate_of_normalized_branch
    (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event)
    (b : Fin C) (actualGain : ℝ)
    (hgain : gain ≤ actualGain) (hgain8 : actualGain ≤ 1 / 8)
    (hdepth : r (lev b) + 2 * actualGain * L ≤ L)
    (Cloc Mz MH : ℕ) (D : LocalBranchData Cloc)
    (hrestore : ∃ Q, D.restored Q)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (η : ℝ) (A' : Set Line) (S : Line → Set ℝ) (counted : Set Event)
    (hN : 2 ≤ Nk) (hB : 0 < B (γ b)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hformat : Mz * Cloc + 2 * MH + 11 ≤ Mc)
    (hZ : D.Z ≤ Nk ^ Mz) (hc : ∀ i, |c i| ≤ Nk ^ MH)
    (hM : ∀ i k, |M i k| ≤ Nk ^ MH) (hBsize : |B (γ b)| ≤ Nk ^ MH)
    (hthickness : D.b = dyadicThickness Nk (r (lev b) + actualGain * L))
    (hbudget : restorationRemezFactor η * D.A ^ Cloc ≤ Nk ^ (ρ * gain * L + ε))
    (hA'meas : MeasurableSet A') (hA'sub : A' ⊆ A b)
    (hSwit : ∀ l ∈ A', S l ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l))
    (hwitness : ∀ l ∈ A', ∀ t ∈ S l,
      pointOfCoordinates (coordinateMap c M (B (γ b))
        (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) +
          ((2 : ℝ) ^ T (lev b))⁻¹ * t))) ∈ D.region)
    (hcounted : counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      pointOfCoordinates (coordinateMap c M (B (γ b)) (graphPoint p.1 p.2)) ∈ D.region})
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * actualGain + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted) :
    residualCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨Q, hQ⟩ := hrestore
  let R := transportPolynomial c M (B (γ b)) Q
  have hN1 : 1 ≤ Nk := by linarith
  have hZ0 : 0 ≤ D.Z := (le_trans (by norm_num) D.two_le_A).trans D.A_le_Z
  have hcoeff (e : Fin 4 →₀ ℕ) : |Q.coeff e| ≤ Nk ^ (Mz * Cloc) := by
    apply (hQ.2.1 e).trans
    calc
      D.Z ^ Cloc ≤ (Nk ^ Mz) ^ Cloc := pow_le_pow_left₀ hZ0 hZ Cloc
      _ = Nk ^ (Mz * Cloc) := (pow_mul _ _ _).symm
  have hRcoeff (e : Fin 4 →₀ ℕ) : |R.coeff e| ≤ Nk ^ Mc :=
    (transportPolynomial_coeff_power_bound c M (B (γ b)) Q hN (Mz * Cloc) MH
      hc hM hBsize hQ.1 hcoeff e).trans (pow_le_pow_right₀ hN1 hformat)
  have hAC : 0 < D.A ^ Cloc := pow_pos (lt_of_lt_of_le (by norm_num) D.two_le_A) _
  have hlocal : D.A ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) :=
    (le_mul_of_one_le_left hAC.le (restorationRemezFactor_bounds hη hη1).1).trans hbudget
  refine ⟨b, actualGain, hgain, hgain8, hdepth, R, A',
    (totalDegree_transportPolynomial_le _ _ _ _).trans hQ.1, hRcoeff,
    hA'meas, hA'sub, ?_, ?_⟩
  · intro l hl t ht
    obtain ⟨s, hs, rfl⟩ := (mem_dyadic_block_iff (j b) (T (lev b)) t).mp ht
    have hpacket := restore_packet_bounds D Q hQ c M hB hη hη1 hbudget
      (blockOrigin l ((j b : ℝ) / (2 : ℝ) ^ T (lev b)))
      (blockVelocity l (((2 : ℝ) ^ T (lev b))⁻¹)) (S l)
      (hSwit l hl).1 (hSwit l hl).2 (by
        intro u hu
        simpa only [← graphPoint_on_block] using hwitness l hl u hu)
    simpa only [← graphPoint_on_block, hthickness] using hpacket.1 s hs
  · apply hmass.trans
    apply measure_mono
    intro p hp
    obtain ⟨hpH, hpA, hpt, hpregion⟩ := hcounted hp
    refine ⟨hpH, hpA, hpt, ?_⟩
    exact (restored_bounds_in_original_coordinates D Q hQ c M hB hlocal
      (graphPoint p.1 p.2) hpregion).2.1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
