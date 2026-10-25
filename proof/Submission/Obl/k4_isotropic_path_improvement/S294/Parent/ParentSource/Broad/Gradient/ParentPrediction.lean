-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentPrediction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentPrediction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentPrediction.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CorePrediction

/-!
# An independent physical quadratic on a fine implicit core

Generalized from the analytic package of o265 session x0946 in
`Broad/Gradient/CorePrediction.lean`. The parent polynomial is arbitrary and is not
assumed to be any old path test. Its coefficients do not enter the relation degrees.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation
open scoped ContDiff

noncomputable section

/-- A quadratic evaluated on a fine sheet, in an independently specified signal unit. -/
def independentCorePrediction (Q : Poly) (unit : ℝ) (c : Base) (scale : ℝ)
    (f : Base → ℝ) (x : Base) : ℝ :=
  eval (Fin.snoc (fun j => c j + scale * x j) (f x)) Q / unit

lemma independentCorePrediction_eq_local (Q : Poly) (unit : ℝ) (c : Base) (scale : ℝ)
    (f : Base → ℝ) (x : Base) :
    independentCorePrediction Q unit c scale f x =
      eval (Fin.snoc (fun i => x i) (f x)) (localNativePolynomial (fun j => c j) scale Q) /
        unit := by
  have hsnoc : Fin.snoc (fun i => x i) (f x) = ![x 0, x 1, x 2, f x] := by
    funext j
    fin_cases j <;> rfl
  rw [hsnoc, localNativePolynomial_eval]
  rfl

/-- The rational presentation and gradient relation degrees needed by original-row renewal. -/
def CorePredictionAnalytic (g : Base → ℝ) : Prop :=
  (∃ (Δ U V Wd : MvPolynomial (Fin 3) ℂ) (sq Q : EuclideanSpace ℂ (Fin 3) → ℂ),
    Δ.totalDegree ≤ 24 ∧ U.totalDegree ≤ 24 ∧ V.totalDegree ≤ 24 ∧ Wd.totalDegree ≤ 24 ∧
    (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) ∧
    (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) Wd * Q z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) ∧
    ContDiffOn ℂ ∞ Q (ball 0 4) ∧
    (∀ x : Base, ‖x‖ < 4 → Q (DenseJet.realSlice x) = (g x : ℂ)) ∧
    (∀ x : Base, ‖x‖ < 4 → eval (fun i => (DenseJet.realSlice x) i) Wd ≠ 0)) ∧
  ContDiffOn ℝ 2 g (ball 0 4) ∧
  ∀ D : ℕ, 578 ≤ D → ∀ j : Fin 3, exf D (gradientComponent g j)

/-- The original branch supplies extensions for every independent quadratic composition. -/
theorem independentCorePrediction_hasRealExtension
    (Q : Poly) (hQ : Q.totalDegree ≤ 2) (unit : ℝ) (hunit : unit ≠ 0)
    (T : Poly) (c : Base) (scale sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 T (fun j => c j) scale sign F f) :
    HasRealExtension 5186 (independentCorePrediction Q unit c scale f) :=
  (hbranch.2.2.2.2.2.2.2 Q unit hQ hunit).1

/-- A degree-24 presentation and degree-578 gradient extensions, independent of every
coefficient bound, physical width and path format. -/
theorem independentCorePrediction_analytic
    (Q : Poly) (hQ : Q.totalDegree ≤ 2) (unit : ℝ) (hunit : unit ≠ 0)
    (T : Poly) (c : Base) (scale sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 T (fun j => c j) scale sign F f) :
    CorePredictionAnalytic (independentCorePrediction Q unit c scale f) := by
  have hext := independentCorePrediction_hasRealExtension Q hQ unit hunit T c scale sign F f hbranch
  obtain ⟨hF, -, hfF, -, hpres, -⟩ := hbranch
  obtain ⟨Δ, U, V, Wd, sq, hΔne, hWne, hΔ, hU, hV, hW, hsq, hrel⟩ := hpres
  have hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (sq z) ^ 2 = eval (fun j => z j) Δ := fun z hz => (hrel z hz).1
  have hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun j => z j) Wd * F z = eval (fun j => z j) U + eval (fun j => z j) V * sq z :=
    fun z hz => (hrel z hz).2.1
  let S := localNativePolynomial (fun j => c j) scale Q
  have hS : S.totalDegree ≤ 2 := (localNativePolynomial_totalDegree _ _ _).trans hQ
  have hgeq : (fun y : Base => eval (Fin.snoc (fun i => y i) (f y)) S / unit) =
      independentCorePrediction Q unit c scale f := by
    funext y
    exact (independentCorePrediction_eq_local Q unit c scale f y).symm
  obtain ⟨UQ, VQ, WQ, Qc, hUQ, hVQ, hWQ, -, hQc, hQreal, hrepQ, hWQnz⟩ :=
    quadratic_residual_rational_presentation 6 (by norm_num) Δ U V Wd hΔ hU hV hW hWne
      sq F hF hroot hrep f hfF S hS unit hunit
  have hball (x : Base) (hx : ‖x‖ < 4) :
      DenseJet.realSlice x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
    rw [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply]
    exact hx
  refine ⟨⟨Δ, UQ, VQ, WQ, sq, Qc, hΔ.trans (by norm_num), hUQ, hVQ, hWQ, hroot, hrepQ,
    hQc.of_le le_top, ?_, ?_⟩, hext.contDiffOn.of_le (by simp), ?_⟩
  · intro x hx
    rw [hQreal x (by rw [mem_ball, dist_zero_right]; exact hx)]
    exact congrArg (fun v : ℝ => (v : ℂ))
      (independentCorePrediction_eq_local Q unit c scale f x).symm
  · intro x hx
    exact hWQnz _ (hrel _ (hball x hx)).2.2
  · intro D hD j
    have hjet := hasRealExtension_quadratic_residual_jet 6 (by norm_num) Δ U V Wd hΔ hU hV hW
      hΔne hWne sq F hsq hF hroot hrep f hfF S hS unit hunit (spacetimeBasis j) 1
    rw [hgeq] at hjet
    have hcomp : (fun x => iteratedFDeriv ℝ 1 (independentCorePrediction Q unit c scale f) x
        (fun _ => spacetimeBasis j)) = gradientComponent (independentCorePrediction Q unit c scale f) j := by
      funext x
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [hcomp] at hjet
    exact hjet.mono_degree (by norm_num at hD ⊢; omega)

/-- The physical parent prediction, rather than the old path test in its own width units. -/
def parentCorePrediction {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ) (p : Native.PathData W)
    (b : Fin p.C) (P : Poly) (K : ℝ) (R : ℕ) (c : Base) (f : Base → ℝ) : Base → ℝ :=
  independentCorePrediction (packetNativeCubePolynomial Nk B p b P)
    (δ Nk (p.r (p.lev b)))⁻¹ c (K ^ R)⁻¹ f

theorem parentCorePrediction_analytic {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (P : Poly) (hP : P.totalDegree ≤ 2)
    (K : ℝ) (R : ℕ) (center : ℝ) (c : Base) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f) :
    CorePredictionAnalytic (parentCorePrediction Nk B p b P K R c f) := by
  apply independentCorePrediction_analytic _ ((packetNativeCubePolynomial_degree Nk B p b P).trans hP)
    _ (by unfold δ; positivity) _ c _ sign F f hbranch

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Correcting the fine sheet changes the physical parent value by at most
`K^14 * epsilon * deltaFine`. The original hidden jets suffice; there is no
coefficient envelope or inverse physical width in this error. -/
theorem parentCorePrediction_error (hNk : 0 < Nk) (b : Fin p.C)
    (hB : 0 < B (p.γ b)) (P : Poly) (hP : P.totalDegree ≤ 2)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ 1)
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hq : q ∈ p.F b) (hbin : |packetSignal Nk p b q - center| ≤ ε)
    (R : ℕ) (c : Base) (f : Base → ℝ)
    (hmatch : rootLift (packetNativeValueTest Nk B p b center)
      (packetNativeCubePoint Nk B p b q) 3 = f (packetLocalCorePoint Nk B p b K R c q))
    (hfirst : |eval (xp q.1 q.2) (pderiv 3 P)| ≤ K * B (p.γ b))
    (hsecond : |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 P))| ≤ K * B (p.γ b) ^ 2) :
    |parentCorePrediction Nk B p b P K R c f (packetLocalCorePoint Nk B p b K R c q) -
      eval (xp q.1 q.2) P| ≤ K ^ 14 * ε * δ Nk (p.r (p.lev b)) := by
  have hδ : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
  obtain ⟨hfirst', hsecond'⟩ := packetNativeCubePolynomial_hidden_bounds hp b hB P q
    (by linarith : 0 ≤ K) (by norm_num : (0 : ℝ) < 1) hwidth hfirst
    (by simpa only [div_one] using hsecond)
  rw [k4_quadratic_atlas_normalization.second_pderiv_eq_curvature _
    ((packetNativeCubePolynomial_degree Nk B p b P).trans hP) 3, eval_C] at hsecond'
  have hpred := packet_signal_core_prediction hp hNk b hB hK hκK hε hεK center hq hbin
    R c f hmatch P hP hfirst' hsecond'
  let z := packetLocalCorePoint Nk B p b K R c q
  change |eval (Fin.snoc (fun j => z j) (f z))
      (localNativePolynomial (fun j => c j) (K ^ R)⁻¹
        (packetNativeCubePolynomial Nk B p b P)) -
      (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) P| ≤ K ^ 14 * ε at hpred
  change |independentCorePrediction _ _ _ _ _ z - _| ≤ _
  rw [independentCorePrediction_eq_local, div_inv_eq_mul]
  have heq : eval (Fin.snoc (fun j => z j) (f z))
        (localNativePolynomial (fun j => c j) (K ^ R)⁻¹
          (packetNativeCubePolynomial Nk B p b P)) * δ Nk (p.r (p.lev b)) -
      eval (xp q.1 q.2) P =
      (eval (Fin.snoc (fun j => z j) (f z))
        (localNativePolynomial (fun j => c j) (K ^ R)⁻¹
          (packetNativeCubePolynomial Nk B p b P)) -
        (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) P) *
        δ Nk (p.r (p.lev b)) := by field_simp [hδ.ne']
  rw [heq, abs_mul, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_right hpred hδ.le

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
