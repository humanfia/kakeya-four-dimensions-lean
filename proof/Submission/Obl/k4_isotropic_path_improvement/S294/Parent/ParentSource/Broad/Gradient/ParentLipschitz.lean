-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentLipschitz, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentLipschitz.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentLipschitz.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentGradient

/-!
# Physical parent Lipschitz estimate in old base coordinates

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

/-- The returning-row clock cancels the fine-frame expansion. The remaining
base coefficient is proportional to the old block length. -/
theorem parent_core_lipschitz (hN : 1 ≤ Nk) (hNk : 0 < Nk) (old b : Fin p.C)
    (hB : 0 < B (p.γ b))
    (P : Poly) (hP : P.totalDegree ≤ 2)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ 1)
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (U : Set Event)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    {M : ℝ} (hM : 0 ≤ M)
    (hparentJets : ∀ q ∈ U, |eval (xp q.1 q.2) (pderiv 3 P)| ≤ K * B (p.γ b) ∧
      |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 P))| ≤ K * B (p.γ b) ^ 2)
    {G : ℝ} (hG0 : 0 ≤ G)
    (hgrad : ∀ x ∈ closedBall (0 : Base) 2,
      ‖fderiv ℝ (parentCorePrediction Nk B p b P K R c f) x‖ ≤
        G * (K ^ 14 * ε * δ Nk (p.r (p.lev b)) +
          M / 2 * coreRowStep p b K R)) :
    ∀ z ∈ U, ∀ z' ∈ U,
      |eval (xp z.1 z.2) P -
          eval (xp z'.1 z'.2) P| ≤
        (2 + G / 2) * (K ^ 14 * ε * δ Nk (p.r (p.lev b))) +
          M / 2 * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
          ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
            ‖packetBase p old z - packetBase p old z'‖ := by
  intro z hz z' hz'
  obtain ⟨hzb, hzo, hzbin, hzcore, hzmatch⟩ := hU z hz
  obtain ⟨hz'b, hz'o, hz'bin, hz'core, hz'match⟩ := hU z' hz'
  set g := parentCorePrediction Nk B p b P K R c f with hgdef
  set err := K ^ 14 * ε * δ Nk (p.r (p.lev b)) with herr
  have hκ0 : 0 ≤ p.κ := by linarith [hp.1]
  have herr0 : 0 ≤ err := by
    have h1 : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
    have h3 : (0 : ℝ) ≤ K ^ 14 := by positivity
    rw [herr]; positivity
  have hstep0 : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
  have hfit0 : 0 ≤ err + M / 2 * coreRowStep p b K R := by
    positivity
  -- predictions at the two incidences
  have hpz := parentCorePrediction_error hp hNk b hB P hP hwidth hK hκK hε hεK
    center hzb hzbin R c f hzmatch (hparentJets z hz).1 (hparentJets z hz).2
  have hpz' := parentCorePrediction_error hp hNk b hB P hP hwidth hK hκK hε hεK
    center hz'b hz'bin R c f hz'match (hparentJets z' hz').1 (hparentJets z' hz').2
  -- mean value inequality on the ball of radius 2
  obtain ⟨-, hgsmooth, -⟩ := parentCorePrediction_analytic Nk B p b P hP K R center c sign F f
    hbranch
  have hdiff : ∀ x ∈ closedBall (0 : Base) 2, DifferentiableAt ℝ g x := by
    intro x hx
    have hx4 : x ∈ ball (0 : Base) 4 := by
      rw [mem_closedBall, dist_zero_right] at hx
      rw [mem_ball, dist_zero_right]
      linarith
    exact (hgsmooth.contDiffAt (isOpen_ball.mem_nhds hx4)).differentiableAt (by norm_num)
  have hzmem : packetLocalCorePoint Nk B p b K R c z ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hz'mem : packetLocalCorePoint Nk B p b K R c z' ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgrad
    (convex_closedBall (0 : Base) 2) hz'mem hzmem
  rw [Real.norm_eq_abs] at hmv
  -- distance of the two local points
  set dZ := ‖packetLocalCorePoint Nk B p b K R c z - packetLocalCorePoint Nk B p b K R c z'‖
    with hdZ
  have hdZhalf : dZ ≤ 1 / 2 := by
    rw [hdZ]
    calc
      _ ≤ ‖packetLocalCorePoint Nk B p b K R c z‖ + ‖packetLocalCorePoint Nk B p b K R c z'‖ :=
        norm_sub_le _ _
      _ ≤ 1 / 2 := by linarith
  obtain ⟨hlo, -, hlb⟩ := coreIncidence_line_old (hU z hz) hp
  have hexp := hp.local_core_expansion hN old b (by linarith : (0 : ℝ) ≤ K) R c z z' hlb hlo
  rw [← hdZ] at hexp
  -- the cancellation of the clock and core scales
  have hcancel : M / 2 * coreRowStep p b K R *
      (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
        ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old)))) =
      M / 2 * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
        ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by
    unfold coreRowStep
    have hK0 : K ^ R ≠ 0 := pow_ne_zero _ (by linarith)
    have hT1 : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
    have hT2 : (2 : ℝ) ^ p.T (p.lev old) ≠ 0 := by positivity
    field_simp
  have hsplit : G * (err + M / 2 * coreRowStep p b K R) * dZ ≤
      G / 2 * err + M / 2 * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
          ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
        ‖packetBase p old z - packetBase p old z'‖ := by
    have hA : G * err * dZ ≤ G / 2 * err := by
      have := mul_le_mul_of_nonneg_left hdZhalf (mul_nonneg hG0 herr0)
      linarith
    have hB' : G * (M / 2 * coreRowStep p b K R) * dZ ≤
        M / 2 * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
          ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
          ‖packetBase p old z - packetBase p old z'‖ := by
      have hpos : 0 ≤ G * (M / 2 * coreRowStep p b K R) := by
        positivity
      calc
        _ ≤ G * (M / 2 * coreRowStep p b K R) *
            (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
              ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old))) *
              ‖packetBase p old z - packetBase p old z'‖) :=
          mul_le_mul_of_nonneg_left hexp hpos
        _ = G * (M / 2 * coreRowStep p b K R *
            (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
              ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old))))) *
              ‖packetBase p old z - packetBase p old z'‖ := by ring
        _ = _ := by rw [hcancel]; ring
    have hexpand : G * (err + M / 2 * coreRowStep p b K R) * dZ =
        G * err * dZ + G * (M / 2 * coreRowStep p b K R) * dZ := by
      ring
    rw [hexpand]
    exact add_le_add hA hB'
  calc
    _ ≤ |eval (xp z.1 z.2) P -
          g (packetLocalCorePoint Nk B p b K R c z)| +
        |g (packetLocalCorePoint Nk B p b K R c z) - g (packetLocalCorePoint Nk B p b K R c z')| +
        |g (packetLocalCorePoint Nk B p b K R c z') -
          eval (xp z'.1 z'.2) P| := by
      have h1 := abs_sub_le (eval (xp z.1 z.2) P)
        (g (packetLocalCorePoint Nk B p b K R c z))
        (eval (xp z'.1 z'.2) P)
      have h2 := abs_sub_le (g (packetLocalCorePoint Nk B p b K R c z))
        (g (packetLocalCorePoint Nk B p b K R c z'))
        (eval (xp z'.1 z'.2) P)
      linarith
    _ ≤ err + G * (err + M / 2 * coreRowStep p b K R) * dZ +
        err := by
      refine add_le_add (add_le_add ?_ hmv) hpz'
      rw [abs_sub_comm]
      exact hpz
    _ ≤ _ := by linarith [hsplit]

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
