-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/Expanded.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/Expanded.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/Expanded.lean
-- (namespace renamed; the attributions that file carries are kept below).
-- Shared from this LOT tree, o143, session x0542, origin/x0542 at 09fa381; Submission/Obl/k4_isotropic_discovery_of_local_restoration/Expanded.lean.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.SampledCandidate

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MeasureTheory MvPolynomial

/-- Scalar-and-function presentation used in the closed frozen statement. -/
def RawBranchData (Cloc J D : ℕ) (A Z a b h s : ℝ) (S : Poly) (f : Base → ℝ) (p : Fin 7 → Base) (E : Set Base) : Prop :=
  (2 ≤ A) ∧
    (A ^ (J + 1) ≤ Z) ∧
    (0 < b) ∧
    (b ≤ a) ∧
    (a ≤ 1) ∧
    (0 < h) ∧
    (h * (A ^ (J + 1)) ^ Cloc ≤ b / a) ∧
    (0 ≤ s) ∧
    (b⁻¹ ≤ Z) ∧
    (S.totalDegree ≤ 2) ∧
    (∀ e, |S.coeff e| ≤ Z) ∧
    (∀ u : Base, ∀ w : ℝ,
    |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 S))| ≤ A / a) ∧
    (ContDiffOn ℝ 6 f (Metric.ball 0 3)) ∧
    (|f 0| ≤ Z) ∧
    (‖fderiv ℝ f 0‖ ≤ Z) ∧
    (‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z) ∧
    (∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
    ∃ u ∈ Metric.closedBall (0 : Base) 1, s ≤ |f u - c - L u|) ∧
    (∀ ε : ℝ, s < ε →
    ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) ∧
    (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
    (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
    A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
    (MeasurableSet E) ∧
    (E ⊆ Metric.closedBall (0 : Base) 1) ∧
    (ENNReal.ofReal A⁻¹ ≤ volume E) ∧
    (HasRealExtension D f) ∧
    (∀ i : Fin 7,
    HasRealExtension D (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i))) ∧
    (HasRealExtension D
    (fun v => eval ![v 0, v 1, v 2, f v] S / a)) ∧
    (∀ i : Fin 7, HasRealExtension D
    (fun v => iteratedFDeriv ℝ 3
      (fun z => eval ![z 0, z 1, z 2, f z] S / a) v (fun _ => p i))) ∧
    (∀ i : Fin 7, ∀ u ∈ E,
    |iteratedFDeriv ℝ 2 f u (fun _ => p i)| ≤ A * (b + s * h)) ∧
    (∀ u ∈ E, |eval ![u 0, u 1, u 2, f u] S / a| ≤ A) ∧
    (∀ i : Fin 7, ∀ u ∈ E,
    |iteratedFDeriv ℝ 3
      (fun z => eval ![z 0, z 1, z 2, f z] S / a) u (fun _ => p i)| ≤ A * b / a)

/-- The old derivative floor remains part of every witness. -/
def rawRegion (A b : ℝ) (S : Poly) (f : Base → ℝ) : Set (Base × ℝ) :=
  {z | z.1 ∈ Metric.closedBall 0 1 ∧ |z.2 - f z.1| ≤ A * b ∧
    A⁻¹ ≤ |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 S)| ∧
    |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 S)| ≤ A}

def RawSampledCandidate (Cloc J D : ℕ) (Nk L : ℝ) (W : ℕ)
    (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event) : Prop :=
  ∃ (b : Fin C) (actualGain : ℝ) (Mz MH : ℕ) (A0 Z a0 b0 h0 s0 : ℝ) (S0 : Poly) (f0 : Base → ℝ) (p0 : Fin 7 → Base) (E0 : Set Base)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (η : ℝ) (A' : Set Line) (S : Line → Set ℝ) (counted : Set Event),
    RawBranchData Cloc J D A0 Z a0 b0 h0 s0 S0 f0 p0 E0 ∧
    gain ≤ actualGain ∧ actualGain ≤ 1 / 8 ∧
    r (lev b) + 2 * actualGain * L ≤ L ∧
    0 < B (γ b) ∧ 0 < η ∧ η ≤ 1 ∧
    Mz * Cloc + 2 * MH + 11 ≤ Mc ∧
    Z ≤ Nk ^ Mz ∧ (∀ i, |c i| ≤ Nk ^ MH) ∧
    (∀ i k, |M i k| ≤ Nk ^ MH) ∧ |B (γ b)| ≤ Nk ^ MH ∧
    b0 = dyadicThickness Nk (r (lev b) + actualGain * L) ∧
    restorationRemezFactor η * (A0 ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) ∧
    MeasurableSet A' ∧ A' ⊆ A b ∧
    (∀ l ∈ A', S l ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l)) ∧
    (∀ l ∈ A', ∀ t ∈ S l,
      pointOfCoordinates (coordinateMap c M (B (γ b))
        (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) +
          ((2 : ℝ) ^ T (lev b))⁻¹ * t))) ∈ (rawRegion A0 b0 S0 f0)) ∧
    (counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      pointOfCoordinates (coordinateMap c M (B (γ b)) (graphPoint p.1 p.2)) ∈ (rawRegion A0 b0 S0 f0)}) ∧
    ENNReal.ofReal (Nk ^ (-((d₁ * actualGain + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted

theorem rawSampledCandidate_implies_sampled
    {Cloc J D : ℕ}
    (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event)
    (h : RawSampledCandidate Cloc J D Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    sampledCandidate Cloc J D Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨b, ag, Mz, MH, A0, Z, a0, b0, h0, s0, S0, f0, p0, E0,
    c, M, η, A', S, counted, hraw, hrest⟩ := h
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29⟩ := hraw
  let d : SampledBranchData Cloc J D :=
    ⟨A0, Z, a0, b0, h0, s0, S0, f0, p0, E0,
      hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29⟩
  exact ⟨b, ag, Mz, MH, d, c, M, η, A', S, counted, hrest⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
