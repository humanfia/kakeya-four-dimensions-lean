-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentPrediction
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreLipschitz

/-!
# Physical parent row fit on an actual fine implicit core

The fine root error and the original parent motion are the only two errors.
The geometry is adapted from o265 session x0946, `CoreLipschitz.lean`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation
open scoped ContDiff

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The physical prediction is close to one original parent value along every returning row. -/
theorem parent_core_row_fit (hNk : 0 < Nk) (old b : Fin p.C) (hB : 0 < B (p.γ b))
    (P : Poly) (hP : P.totalDegree ≤ 2)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ 1)
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ) (U : Set Event)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    {M : ℝ} (hM : 0 ≤ M)
    (hjets : ∀ q ∈ U, |eval (xp q.1 q.2) (pderiv 3 P)| ≤ K * B (p.γ b) ∧
      |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 P))| ≤ K * B (p.γ b) ^ 2)
    (hmotion : ∀ q ∈ U, ∀ q' ∈ U, q'.1 = q.1 →
      |eval (xp q'.1 q'.2) P - eval (xp q.1 q.2) P| ≤ M * |q'.2 - q.2|)
    (q : Event) (hq : q ∈ U) (τ : ℝ) (hτ : τ ∈ coreRowTimes p b K R U q) :
    ‖packetLocalCorePoint Nk B p b K R c q +
        τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤ 1 / 4 ∧
      |parentCorePrediction Nk B p b P K R c f (packetLocalCorePoint Nk B p b K R c q +
          τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
        eval (xp q.1 q.2) P| ≤
      K ^ 14 * ε * δ Nk (p.r (p.lev b)) +
        M / 2 * coreRowStep p b K R := by
  have hKpos : 0 < K := by linarith
  have hκ : p.κ ≠ 0 := by linarith [hp.1]
  let q' : Event := (q.1, q.2 + coreRowStep p b K R * τ)
  have hline : packetLocalCorePoint Nk B p b K R c q' =
      packetLocalCorePoint Nk B p b K R c q +
        τ • spacetimeDirection (packetCubeVelocity p b q.1) := by
    have hh := packetLocalCorePoint_line Nk B p b hKpos R hκ c q.1 q.2 τ
    simp only [Prod.mk.eta] at hh
    exact hh
  have hq'U : q' ∈ U := hτ
  obtain ⟨hq'b, hq'o, hq'bin, hq'core, hq'match⟩ := hU q' hq'U
  obtain ⟨hqb, hqo, -, hqcore, -⟩ := hU q hq
  have hfirst : ‖packetLocalCorePoint Nk B p b K R c q +
      τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤ 1 / 4 := by
    rw [← hline]; exact hq'core
  refine ⟨hfirst, ?_⟩
  -- `|τ| ≤ 1/2`
  have hτhalf : |τ| ≤ 1 / 2 := by
    have hcoord : |τ| ≤ ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ := by
      have hh := PiLp.norm_apply_le (τ • spacetimeDirection (packetCubeVelocity p b q.1)) 0
      simpa [spacetimeDirection] using hh
    have hdiff : ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤
        ‖packetLocalCorePoint Nk B p b K R c q +
          τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ +
        ‖packetLocalCorePoint Nk B p b K R c q‖ := by
      calc
        ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ =
            ‖(packetLocalCorePoint Nk B p b K R c q +
              τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
              packetLocalCorePoint Nk B p b K R c q‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  -- prediction at the shifted incidence
  have hpred := parentCorePrediction_error hp hNk b hB P hP hwidth hK hκK hε hεK
    center hq'b hq'bin R c f hq'match (hjets q' hq'U).1 (hjets q' hq'U).2
  rw [hline] at hpred
  have hmarkov := hmotion q hq q' hq'U rfl
  have hstep : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
  have hmove : |q'.2 - q.2| ≤ coreRowStep p b K R * (1 / 2) := by
    rw [show q'.2 - q.2 = coreRowStep p b K R * τ by simp only [q']; ring,
      abs_mul, abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left hτhalf hstep
  have hmarkov' : |eval (xp q'.1 q'.2) P - eval (xp q.1 q.2) P| ≤
      M / 2 * coreRowStep p b K R := by
    refine hmarkov.trans ?_
    calc
      _ ≤ M * (coreRowStep p b K R * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hmove hM
      _ = _ := by ring
  calc
    _ ≤ |parentCorePrediction Nk B p b P K R c f (packetLocalCorePoint Nk B p b K R c q +
            τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
          eval (xp q'.1 q'.2) P| +
        |eval (xp q'.1 q'.2) P -
          eval (xp q.1 q.2) P| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hpred hmarkov'

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
