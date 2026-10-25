-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.RealStableBranch, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/RealStableBranch.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RealStableBranch.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RealStableBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RealStableBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.SmoothBranch
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.QuadraticBranchExtensions

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

theorem stable_quadratic_formula_ofReal (a b c : ℝ) (hd : 0 ≤ b ^ 2 - 4 * a * c) :
    -2 * (c : ℂ) / ((b : ℂ) + Complex.sqrt ((b : ℂ) ^ 2 - 4 * (a : ℂ) * (c : ℂ))) =
      ((-2 * c / (b + Real.sqrt (b ^ 2 - 4 * a * c)) : ℝ) : ℂ) := by
  have hcast : (b : ℂ) ^ 2 - 4 * (a : ℂ) * (c : ℂ) = ((b ^ 2 - 4 * a * c : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.sqrt_of_nonneg (by exact_mod_cast hd)]
  simp only [Complex.ofReal_re]
  push_cast
  rfl

/-- Fixed complex comparison margins construct a simple smooth quadratic
branch, its real restriction, and all four exact sampled extension fields.
The uniform degree is chosen from the two real base-polynomial degrees. -/
theorem exists_real_stable_branch_with_extensions (d : ℕ)
    (B C₀ : MvPolynomial (Fin 3) ℝ) (hB : B.totalDegree ≤ d)
    (hC : C₀.totalDegree ≤ d) (a : ℝ) {β : ℝ} (hβ : 0 < β)
    (hbclose : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      ‖eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) - (β : ℂ)‖ ≤ β / 4)
    (hdisc : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      ‖(eval (fun i => z i) (B.map (algebraMap ℝ ℂ))) ^ 2 -
        4 * (a : ℂ) * eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ)) -
          (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4) :
    ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ)) +
          eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) * F z + (a : ℂ) * (F z) ^ 2 = 0 ∧
        eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z ≠ 0) ∧
      ∀ (S : Poly) (lam : ℝ), S.totalDegree ≤ 2 → lam ≠ 0 →
        HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
        (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
        HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => eval ![x 0, x 1, x 2, f x] S / lam) ∧
        (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => iteratedFDeriv ℝ 3
            (fun y => eval ![y 0, y 1, y 2, f y] S / lam) x (fun _ => v))) := by
  let b : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => eval (fun i => z i) (B.map (algebraMap ℝ ℂ))
  let c : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ))
  let F : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => -2 * c z / (b z + Complex.sqrt ((b z) ^ 2 - 4 * (a : ℂ) * c z))
  let f : Base → ℝ := fun x =>
    -2 * eval (fun i => x i) C₀ /
      (eval (fun i => x i) B + Real.sqrt ((eval (fun i => x i) B) ^ 2 -
        4 * a * eval (fun i => x i) C₀))
  have hpoly (P : MvPolynomial (Fin 3) ℂ) :
      ContDiffOn ℂ ⊤ (fun z : EuclideanSpace ℂ (Fin 3) => eval (fun i => z i) P) (ball 0 4) := by
    apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
    intro i
    fun_prop
  have hF : ContDiffOn ℂ ⊤ F (ball 0 4) :=
    contDiffOn_stable_quadratic_formula (ball 0 4) (a : ℂ) b c
      (hpoly _) (hpoly _) hβ hbclose hdisc
  have hprop (z : EuclideanSpace ℂ (Fin 3)) (hz : z ∈ ball 0 4) :
      c z + b z * F z + (a : ℂ) * (F z) ^ 2 = 0 ∧ b z + 2 * (a : ℂ) * F z ≠ 0 := by
    have hm := stable_quadratic_complex_margins (a : ℂ) (b z) (c z) hβ
      (hbclose z hz) (hdisc z hz)
    have hden : b z + Complex.sqrt ((b z) ^ 2 - 4 * (a : ℂ) * c z) ≠ 0 :=
      norm_pos_iff.mp (hβ.trans_le hm.2.1)
    have hr := stable_quadratic_root_formula (a : ℂ) (b z) (c z)
      (Complex.sqrt ((b z) ^ 2 - 4 * (a : ℂ) * c z))
      (complex_sqrt_sq _) hden
    refine ⟨hr.1, ?_⟩
    change b z + 2 * (a : ℂ) * (-2 * c z / _) ≠ 0
    rw [hr.2]
    exact norm_pos_iff.mp ((by positivity : 0 < β / 2).trans_le hm.2.2.1)
  have hreal : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ) := by
    intro x hx
    have hcx : DenseJet.realSlice x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
      simpa only [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply] using hx
    have hbR : b (DenseJet.realSlice x) = (eval (fun i => x i) B : ℂ) :=
      Submission.Lib.K4QuadraticSheetsReal.eval_map_real B (fun i => x i)
    have hcR : c (DenseJet.realSlice x) = (eval (fun i => x i) C₀ : ℂ) :=
      Submission.Lib.K4QuadraticSheetsReal.eval_map_real C₀ (fun i => x i)
    have hpos := (stable_quadratic_complex_margins (a : ℂ)
      (b (DenseJet.realSlice x)) (c (DenseJet.realSlice x)) hβ
      (hbclose _ hcx) (hdisc _ hcx)).1
    have hdreal : 0 ≤ (eval (fun i => x i) B) ^ 2 - 4 * a * eval (fun i => x i) C₀ := by
      rw [hbR, hcR] at hpos
      simpa [Complex.mul_re, Complex.sub_re, pow_two] using hpos.le
    dsimp [F, f]
    rw [hbR, hcR]
    exact stable_quadratic_formula_ofReal a _ _ hdreal
  have hfsmooth : ContDiffOn ℝ 6 f (ball 0 3) := by
    intro x hx
    have hx4 : ‖x‖ < 4 := by
      have hx3 : ‖x‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hx
      linarith
    exact ((DenseJet.contDiffAt_real_slice (hF.of_le le_top)
      (fun y hy => hreal y (by simpa only [mem_ball, dist_zero_right] using hy)) hx4).of_le
      (by simp)).contDiffWithinAt
  refine ⟨F, f, hF, hfsmooth, hreal, hprop, ?_⟩
  intro S lam hS hlam
  exact simple_quadratic_branch_all_sampled_extensions d
    (B.map (algebraMap ℝ ℂ)) (C₀.map (algebraMap ℝ ℂ))
    ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ B).trans hB)
    ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ C₀).trans hC)
    (a : ℂ) F hF (fun z hz => (hprop z hz).1) (fun z hz => (hprop z hz).2)
    f hreal S hS lam hlam

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
