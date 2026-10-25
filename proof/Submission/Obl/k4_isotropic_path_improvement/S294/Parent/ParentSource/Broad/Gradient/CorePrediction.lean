-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CorePrediction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CorePrediction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CorePrediction.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalRowRenewal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.LineMarkov
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceCoreValueVariation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.QuadraticRealJets

/-!
# The old-signal prediction on a fine core: analytic package

On a coherent fine core, the old signal is predicted by `g = oldSignalCorePrediction`,
the old polynomial evaluated on the fine branch. This file collects what the
renewal argument needs about `g`, all from the core's branch data:

* a rational presentation of degree at most `24` on the complex ball of radius `4`,
  with the branch's nonvanishing denominator;
* smoothness on the real ball of radius `4`;
* algebraic extensions of degree `578` for its three gradient components.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation
open scoped ContDiff

noncomputable section

/-- The old polynomial in the local coordinates of a fine core. -/
def oldSignalLocalPolynomial {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ) (p : Native.PathData W)
    (a b : Fin p.C) (K : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) : Poly :=
  localNativePolynomial (fun j => c j) (K ^ R)⁻¹ (packetNativeCubePolynomial Nk B p b (p.R a))

theorem oldSignalCorePrediction_eq_local {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (a b : Fin p.C) (K : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3))
    (f : Base → ℝ) (x : Base) :
    oldSignalCorePrediction Nk B p a b K R c f x =
      eval (Fin.snoc (fun i => x i) (f x)) (oldSignalLocalPolynomial Nk B p a b K R c) /
        (δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b))) := by
  have hsnoc : Fin.snoc (fun i => x i) (f x) = ![x 0, x 1, x 2, f x] := by
    ext j
    fin_cases j <;> rfl
  rw [hsnoc, oldSignalLocalPolynomial, localNativePolynomial_eval]
  rfl

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- **Analytic package of the old-signal prediction.** -/
theorem oldSignalCorePrediction_analytic (hNk : 0 < Nk) (a b : Fin p.C) {K : ℝ} (R : ℕ)
    (center : ℝ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f) :
    (∃ (Δ U V Wd : MvPolynomial (Fin 3) ℂ) (sq Q : EuclideanSpace ℂ (Fin 3) → ℂ),
      Δ.totalDegree ≤ 24 ∧ U.totalDegree ≤ 24 ∧ V.totalDegree ≤ 24 ∧ Wd.totalDegree ≤ 24 ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) Wd * Q z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) ∧
      ContDiffOn ℂ ∞ Q (ball 0 4) ∧
      (∀ x : Base, ‖x‖ < 4 →
        Q (DenseJet.realSlice x) = (oldSignalCorePrediction Nk B p a b K R c f x : ℂ)) ∧
      (∀ x : Base, ‖x‖ < 4 → eval (fun i => (DenseJet.realSlice x) i) Wd ≠ 0)) ∧
    ContDiffOn ℝ 2 (oldSignalCorePrediction Nk B p a b K R c f) (ball 0 4) ∧
    ∀ D : ℕ, 578 ≤ D → ∀ j : Fin 3,
      exf D (gradientComponent (oldSignalCorePrediction Nk B p a b K R c f) j) := by
  have hext := oldSignalCorePrediction_hasRealExtension hp hNk a b R center c sign F f hbranch
  obtain ⟨hF, -, hfF, -, hpres, -⟩ := hbranch
  obtain ⟨Δ, U, V, Wd, sq, hΔne, hWne, hΔ, hU, hV, hW, hsq, hrel⟩ := hpres
  have hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (sq z) ^ 2 = eval (fun j => z j) Δ := fun z hz => (hrel z hz).1
  have hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun j => z j) Wd * F z = eval (fun j => z j) U + eval (fun j => z j) V * sq z :=
    fun z hz => (hrel z hz).2.1
  have hdegR : (p.R a).totalDegree ≤ 2 := by
    rcases (hp.2.2.2.2.2.2.2 a).2.2 with ⟨_, _, _, _, hdeg, _⟩
    exact hdeg
  have hS : (oldSignalLocalPolynomial Nk B p a b K R c).totalDegree ≤ 2 :=
    (localNativePolynomial_totalDegree _ _ _).trans
      ((packetNativeCubePolynomial_degree Nk B p b (p.R a)).trans hdegR)
  have hlam : δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b)) ≠ 0 := by
    apply div_ne_zero <;> unfold δ <;> positivity
  have hgeq : (fun y : Base => eval (Fin.snoc (fun i => y i) (f y))
      (oldSignalLocalPolynomial Nk B p a b K R c) /
        (δ Nk (p.r (p.lev a)) / δ Nk (p.r (p.lev b)))) =
      oldSignalCorePrediction Nk B p a b K R c f := by
    funext y
    exact (oldSignalCorePrediction_eq_local Nk B p a b K R c f y).symm
  obtain ⟨UQ, VQ, WQ, Q, hUQ, hVQ, hWQ, -, hQ, hQreal, hrepQ, hWQnz⟩ :=
    quadratic_residual_rational_presentation 6 (by norm_num) Δ U V Wd hΔ hU hV hW hWne
      sq F hF hroot hrep f hfF (oldSignalLocalPolynomial Nk B p a b K R c) hS _ hlam
  have hball (x : Base) (hx : ‖x‖ < 4) :
      DenseJet.realSlice x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
    rw [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply]
    exact hx
  refine ⟨⟨Δ, UQ, VQ, WQ, sq, Q, hΔ.trans (by norm_num), hUQ, hVQ, hWQ, hroot, hrepQ,
    hQ.of_le le_top, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rw [hQreal x (by rw [mem_ball, dist_zero_right]; exact hx),
      oldSignalCorePrediction_eq_local]
  · intro x hx
    exact hWQnz _ (hrel _ (hball x hx)).2.2
  · exact hext.contDiffOn.of_le (by simp)
  · intro D hD j
    have hjet := hasRealExtension_quadratic_residual_jet 6 (by norm_num) Δ U V Wd hΔ hU hV hW
      hΔne hWne sq F hsq hF hroot hrep f hfF (oldSignalLocalPolynomial Nk B p a b K R c) hS _
      hlam (spacetimeBasis j) 1
    rw [hgeq] at hjet
    have hcomp : (fun x => iteratedFDeriv ℝ 1 (oldSignalCorePrediction Nk B p a b K R c f) x
        (fun _ => spacetimeBasis j)) =
        gradientComponent (oldSignalCorePrediction Nk B p a b K R c f) j := by
      funext x
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [hcomp] at hjet
    exact hjet.mono_degree (by norm_num at hD ⊢; omega)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
