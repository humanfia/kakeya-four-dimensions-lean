-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceCoreValueVariation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceCoreValueVariation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceCoreValueVariation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceCoreValueVariation.lean.
-- Only the source value-norming declarations used here are retained; earlier provenance is preserved.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceCoreSignals
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeLines
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeBranch
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.OriginalValueVariation
import Submission.Lib.K4OriginalGeometricReference.RawJointSupport

/-!
The actual OLD signal on a coherent intermediate native sheet has a
whole-core variation bound from an earlier original entry. No local
velocity breadth or old polynomial coefficient envelope is required.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation

noncomputable section

/-- The old signal is normalized by its OWN original width, on the SAME
coherent fine sheet. The fine coordinate change has not changed that unit. -/
def oldSignalCorePrediction {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (a b : Fin p.C) (K : ℝ) (R : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ) (x : Base) : ℝ :=
  eval (Fin.snoc (fun j => c j + (K ^ R)⁻¹ * x j) (f x))
    (packetNativeCubePolynomial Nk B p b (p.R a)) /
      (δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b)))

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The actual corrected-root error in OLD signal units retains the
fine/old width ratio. This is independent of all absolute coefficients. -/
theorem path_old_signal_core_prediction_error
    (hNk : 0 < Nk) (a b : Fin p.C) (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hqb : q ∈ p.F b) (hqa : q ∈ p.F a)
    (hbin : |packetSignal Nk p b q - center| ≤ ε)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ)
    (hmatch : rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
      f (packetLocalCorePoint Nk B p b K R c q)) :
    |oldSignalCorePrediction Nk B p a b K R c f (packetLocalCorePoint Nk B p b K R c q) -
      eval (xp q.1 q.2) (p.R a) / δ Nk (p.r (p.lev a))| ≤
        K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev a))) := by
  let z := packetLocalCorePoint Nk B p b K R c q
  let oldWidth := δ Nk (p.r (p.lev a))
  let fineWidth := δ Nk (p.r (p.lev b))
  let ratio := oldWidth / fineWidth
  have hold : 0 < oldWidth := by dsimp [oldWidth, δ]; positivity
  have hfine : 0 < fineWidth := by dsimp [fineWidth, δ]; positivity
  have hratio : 0 < ratio := div_pos hold hfine
  have hpred := path_old_signal_core_prediction hp hNk a b hB hγ hwidth hK hκK hε hεK
    center hqb hqa hbin R c f hmatch
  change |eval (Fin.snoc (fun j => z j) (f z))
      (localNativePolynomial (fun j => c j) (K ^ R)⁻¹
        (packetNativeCubePolynomial Nk B p b (p.R a))) -
      fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)| ≤ K ^ 14 * ε at hpred
  have hsnoc : Fin.snoc (fun j => z j) (f z) = ![z 0, z 1, z 2, f z] := by
    ext j
    fin_cases j <;> rfl
  rw [hsnoc, localNativePolynomial_eval] at hpred
  let value := eval (Fin.snoc (fun j => c j + (K ^ R)⁻¹ * z j) (f z))
    (packetNativeCubePolynomial Nk B p b (p.R a))
  change |value / ratio - eval (xp q.1 q.2) (p.R a) / oldWidth| ≤ _
  have heq : value / ratio - eval (xp q.1 q.2) (p.R a) / oldWidth =
      (value - fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)) / ratio := by
    dsimp only [ratio]
    field_simp [hold.ne', hfine.ne'] <;> ring
  rw [heq, abs_div, abs_of_pos hratio]
  calc
    _ ≤ (K ^ 14 * ε) / ratio := div_le_div_of_nonneg_right hpred hratio.le
    _ = _ := by
      change (K ^ 14 * ε) / (oldWidth / fineWidth) = (K ^ 14 * ε) * (fineWidth / oldWidth)
      field_simp [hold.ne', hfine.ne'] <;> ring

/-- Actual original path tests and coherent corrected-root matching
bound this OLD-unit prediction on every original entry point. -/
theorem path_old_signal_core_value_bound
    (hNk : 0 < Nk) (a b : Fin p.C) (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hqb : q ∈ p.F b) (hqa : q ∈ p.F a)
    (hbin : |packetSignal Nk p b q - center| ≤ ε)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ)
    (hmatch : rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
      f (packetLocalCorePoint Nk B p b K R c q)) :
    |oldSignalCorePrediction Nk B p a b K R c f (packetLocalCorePoint Nk B p b K R c q)| ≤
      p.κ + K ^ 14 * ε := by
  let z := packetLocalCorePoint Nk B p b K R c q
  let oldWidth := δ Nk (p.r (p.lev a))
  let fineWidth := δ Nk (p.r (p.lev b))
  let ratio := oldWidth / fineWidth
  have hold : 0 < oldWidth := by dsimp [oldWidth, δ]; positivity
  have hfine : 0 < fineWidth := by dsimp [fineWidth, δ]; positivity
  have hratio : 0 < ratio := div_pos hold hfine
  have hratio1 : 1 ≤ ratio := (one_le_div hfine).mpr hwidth
  have hpred := path_old_signal_core_prediction hp hNk a b hB hγ hwidth hK hκK hε hεK
    center hqb hqa hbin R c f hmatch
  change |eval (Fin.snoc (fun j => z j) (f z))
      (localNativePolynomial (fun j => c j) (K ^ R)⁻¹
        (packetNativeCubePolynomial Nk B p b (p.R a))) -
      fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)| ≤ K ^ 14 * ε at hpred
  have hsnoc : Fin.snoc (fun j => z j) (f z) = ![z 0, z 1, z 2, f z] := by
    ext j
    fin_cases j <;> rfl
  rw [hsnoc, localNativePolynomial_eval] at hpred
  have hs := path_packet_support hp a hqa
  rcases (hp.2.2.2.2.2.2.2 a).2.2 with
    ⟨_, _, _, _, _, _, _, _, _, hwhole, _, _⟩
  have hwholePoint := (hwhole q.1 hs.2.1).2.2 q.2 hs.2.2.1
  have hactual : |eval (xp q.1 q.2) (p.R a)| ≤ p.κ * oldWidth := by
    simpa only [oldWidth, Native.x, xp, Native.δ, δ] using hwholePoint.2.1
  have hscaled : |fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)| ≤ p.κ * ratio := by
    rw [abs_mul, abs_inv, abs_of_pos hfine]
    calc
      _ ≤ fineWidth⁻¹ * (p.κ * oldWidth) :=
        mul_le_mul_of_nonneg_left hactual (by positivity)
      _ = _ := by dsimp only [ratio]; ring
  have hsum : |eval (Fin.snoc (fun j => c j + (K ^ R)⁻¹ * z j) (f z))
      (packetNativeCubePolynomial Nk B p b (p.R a))| ≤ K ^ 14 * ε + p.κ * ratio := by
    calc
      _ = |(eval (Fin.snoc (fun j => c j + (K ^ R)⁻¹ * z j) (f z))
          (packetNativeCubePolynomial Nk B p b (p.R a)) -
          fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)) +
          fineWidth⁻¹ * eval (xp q.1 q.2) (p.R a)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hpred hscaled)
  change |eval (Fin.snoc (fun j => c j + (K ^ R)⁻¹ * z j) (f z))
      (packetNativeCubePolynomial Nk B p b (p.R a)) / ratio| ≤ _
  rw [abs_div, abs_of_pos hratio]
  apply (div_le_iff₀ hratio).mpr
  calc
    _ ≤ K ^ 14 * ε + p.κ * ratio := hsum
    _ ≤ (K ^ 14 * ε) * ratio + p.κ * ratio :=
      add_le_add (le_mul_of_one_le_right (by positivity) hratio1) le_rfl
    _ = _ := by ring

/-- The relation degree of the normalized actual OLD signal is the fixed
branch degree, before J, source masses, or any coefficient formats. -/
theorem oldSignalCorePrediction_hasRealExtension
    (hNk : 0 < Nk) (a b : Fin p.C) {K : ℝ} (R : ℕ) (center : ℝ)
    (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f) :
    HasRealExtension 5186 (oldSignalCorePrediction Nk B p a b K R c f) := by
  have hdeg : (p.R a).totalDegree ≤ 2 := by
    rcases (hp.2.2.2.2.2.2.2 a).2.2 with ⟨_, _, _, _, hdeg, _⟩
    exact hdeg
  have hlam : δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b)) ≠ 0 := by
    apply div_ne_zero <;> unfold δ <;> positivity
  exact (hbranch.2.2.2.2.2.2.2 (packetNativeCubePolynomial Nk B p b (p.R a))
    (δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b)))
    ((packetNativeCubePolynomial_degree Nk B p b (p.R a)).trans hdeg) hlam).1

/-- Original earlier-entry floors and caps turn ACTUAL old path value
bounds into whole-core prediction variation. This step needs no local
palette breadth and no P coefficient or derivative envelope. -/
theorem path_old_signal_core_variation
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hNk : 0 < Nk) (a b : Fin p.C) (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (μ : Measure Event) {A β : ℝ} (hA : 2 ≤ A) (hβ : 0 < β)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set Base, MeasurableSet U →
      μ (packetLocalCorePoint Nk B p b K R c ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsource : ∀ᵐ q ∂μ, q ∈ p.F b ∧ q ∈ p.F a ∧
      |packetSignal Nk p b q - center| ≤ ε ∧
      packetLocalCorePoint Nk B p b K R c q ∈ closedBall (0 : Base) 1 ∧
      rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
        f (packetLocalCorePoint Nk B p b K R c q)) :
    ∀ x ∈ closedBall (0 : Base) 2, ∀ y ∈ closedBall (0 : Base) 2,
      |oldSignalCorePrediction Nk B p a b K R c f y -
        oldSignalCorePrediction Nk B p a b K R c f x| ≤
          (A ^ J * (p.κ + K ^ 14 * ε)) * ‖y - x‖ := by
  have hg := (oldSignalCorePrediction_hasRealExtension hp hNk a b R center c sign F f hbranch).mono_degree hD
  have hs : ∀ᵐ q ∂μ, packetLocalCorePoint Nk B p b K R c q ∈ closedBall (0 : Base) 1 ∧
      |oldSignalCorePrediction Nk B p a b K R c f (packetLocalCorePoint Nk B p b K R c q)| ≤
        p.κ + K ^ 14 * ε := by
    filter_upwards [hsource] with q hq
    exact ⟨hq.2.2.2.1, path_old_signal_core_value_bound hp hNk a b hB hγ hwidth
      hK hκK hε hεK center hq.1 hq.2.1 hq.2.2.1 R c f hq.2.2.2.2⟩
  intro x hx y hy
  exact original_value_prediction_variation hjets μ (packetLocalCorePoint Nk B p b K R c)
    _ hg hA hβ (by have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1; positivity) hmass hcap hs hx hy

/-- A later DEEP-history portion needs no new mass floor: its small
intermediate-core diameter and the EARLIER whole-core value norming give
actual OLD-height oscillation. An occupied anchor can then supply the
finite physical-state menu without evaluating a branch outside its core. -/
theorem path_old_signal_deep_entry_oscillation
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hNk : 0 < Nk) (a b : Fin p.C) (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (μ : Measure Event) {A β : ℝ} (hA : 2 ≤ A) (hβ : 0 < β)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set Base, MeasurableSet U →
      μ (packetLocalCorePoint Nk B p b K R c ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsource : ∀ᵐ q ∂μ, q ∈ p.F b ∧ q ∈ p.F a ∧
      |packetSignal Nk p b q - center| ≤ ε ∧
      packetLocalCorePoint Nk B p b K R c q ∈ closedBall (0 : Base) 1 ∧
      rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
        f (packetLocalCorePoint Nk B p b K R c q))
    (U : Set Event) {baseDiameter : ℝ}
    (hpoints : ∀ q ∈ U, q ∈ p.F b ∧ q ∈ p.F a ∧
      |packetSignal Nk p b q - center| ≤ ε ∧
      packetLocalCorePoint Nk B p b K R c q ∈ closedBall (0 : Base) 1 ∧
      rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
        f (packetLocalCorePoint Nk B p b K R c q))
    (hdiameter : ∀ q ∈ U, ∀ q' ∈ U,
      ‖packetLocalCorePoint Nk B p b K R c q - packetLocalCorePoint Nk B p b K R c q'‖ ≤
        baseDiameter) :
    ∀ q ∈ U, ∀ q' ∈ U,
      |eval (xp q.1 q.2) (p.R a) / δ Nk (p.r (p.lev a)) -
        eval (xp q'.1 q'.2) (p.R a) / δ Nk (p.r (p.lev a))| ≤
        2 * (K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev a)))) +
          (A ^ J * (p.κ + K ^ 14 * ε)) * baseDiameter := by
  have hv := path_old_signal_core_variation hp hD hjets hNk a b hB hγ hwidth
    hK hκK hε hεK center R c sign F f hbranch μ hA hβ hmass hcap hsource
  apply Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells.original_entry_residual_signal_diameter U
    (fun q => eval (xp q.1 q.2) (p.R a) / δ Nk (p.r (p.lev a)))
    (fun q => oldSignalCorePrediction Nk B p a b K R c f (packetLocalCorePoint Nk B p b K R c q))
  · intro q hq
    obtain ⟨hqb, hqa, hbin, _, hmatch⟩ := hpoints q hq
    simpa only [abs_sub_comm] using path_old_signal_core_prediction_error hp hNk a b hB hγ
      hwidth hK hκK hε hεK center hqb hqa hbin R c f hmatch
  · intro q hq q' hq'
    have hh := hv _
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) (hpoints q' hq').2.2.2.1) _
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) (hpoints q hq).2.2.2.1)
    exact hh.trans (mul_le_mul_of_nonneg_left (hdiameter q hq q' hq')
      (by have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1; positivity))

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
