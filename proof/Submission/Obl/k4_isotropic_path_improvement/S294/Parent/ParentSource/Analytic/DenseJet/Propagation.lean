-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.DenseJet.Propagation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/DenseJet/Propagation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DenseJet/Propagation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DenseJet/Propagation.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Propagation.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.RealJets

/-!
# Propagating a bound for an algebraic sheet from a small real ball

A bound for a degree-`D` sheet on a real ball of radius `1/8` around a point of the
closed unit ball gives a bound, with a loss depending only on `D`, on the complex
balls of radius `1/2` around every real point of norm at most `2`.

The single step is the accepted uniform comparison
`Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_norm_constant_two`
(o149), applied after the affine change `z ↦ c + z / 4`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet

open Set Metric
open Submission.Obl.k4_algebraic_real_jet_comparison

/-- One step: a bound on the real ball of radius `1/8` around a real center of norm
less than `3` gives a bound on the complex ball of radius `1/2` around it. -/
theorem sheet_step (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (F : EuclideanSpace ℂ (Fin 3) → ℂ), HasSheetRelation 3 D F →
      DifferentiableOn ℂ F (ball 0 4) →
      ∀ (c : EuclideanSpace ℝ (Fin 3)), ‖c‖ < 3 → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x - c‖ ≤ 1 / 8 → ‖F (realSlice x)‖ ≤ B) →
      ∀ w : EuclideanSpace ℂ (Fin 3), ‖w - realSlice c‖ ≤ 1 / 2 → ‖F w‖ ≤ C * B := by
  obtain ⟨C, hC, hnorm⟩ := exists_sheet_norm_constant_two 3 D
  refine ⟨C, hC, ?_⟩
  intro F hrel hF c hc B hB hbase w hw
  let a : EuclideanSpace ℂ (Fin 3) := realSlice c
  have ha : ‖a‖ = ‖c‖ := norm_realSlice_apply c
  have hr : ((1 / 4 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hmap : MapsTo (fun z => a + ((1 / 4 : ℝ) : ℂ) • z) (ball 0 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    have hsm : ‖((1 / 4 : ℝ) : ℂ) • z‖ = ‖z‖ / 4 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      ring
    calc
      ‖a + ((1 / 4 : ℝ) : ℂ) • z‖ ≤ ‖a‖ + ‖((1 / 4 : ℝ) : ℂ) • z‖ := norm_add_le _ _
      _ < 4 := by rw [hsm, ha]; linarith
  have hrelG := hrel.comp_affine a hr hmap
  have hdG : DifferentiableOn ℂ (fun z => F (a + ((1 / 4 : ℝ) : ℂ) • z)) (ball 0 4) := by
    have hlin : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) => a + ((1 / 4 : ℝ) : ℂ) • z) := by
      fun_prop
    exact hF.comp hlin.differentiableOn hmap
  have hbaseG : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖(fun z => F (a + ((1 / 4 : ℝ) : ℂ) • z)) (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B := by
    intro x hx
    have heq : a + ((1 / 4 : ℝ) : ℂ) • (WithLp.toLp 2 (fun i => (x i : ℂ)) :
        EuclideanSpace ℂ (Fin 3)) = realSlice (c + (1 / 4 : ℝ) • x) := by
      ext i
      simp [a, realSlice_apply]
    simp only [heq]
    apply hbase
    have : c + (1 / 4 : ℝ) • x - c = (1 / 4 : ℝ) • x := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have hbound := hnorm _ hrelG hdG B hB hbaseG
  have hz : ‖(4 : ℂ) • (w - a)‖ ≤ 2 := by
    rw [norm_smul]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this]
    linarith
  have h := hbound _ hz
  have heq : a + ((1 / 4 : ℝ) : ℂ) • ((4 : ℂ) • (w - a)) = w := by
    rw [smul_smul]
    norm_num
  simpa only [heq] using h

/-- The chain: a bound on the real ball of radius `1/8` around a point of the closed
unit ball propagates to the complex balls of radius `1/2` around every real point of
norm at most `2`. -/
theorem sheet_chain (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (F : EuclideanSpace ℂ (Fin 3) → ℂ), HasSheetRelation 3 D F →
      DifferentiableOn ℂ F (ball 0 4) →
      ∀ (y : EuclideanSpace ℝ (Fin 3)), ‖y‖ ≤ 1 → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x - y‖ ≤ 1 / 8 → ‖F (realSlice x)‖ ≤ B) →
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 2 →
      ∀ w : EuclideanSpace ℂ (Fin 3), ‖w - realSlice x‖ ≤ 1 / 2 → ‖F w‖ ≤ C * B := by
  obtain ⟨C, hC, hstep⟩ := sheet_step D
  refine ⟨C ^ 9, by positivity, ?_⟩
  intro F hrel hF y hy B hB hbase x hx
  let c : ℕ → EuclideanSpace ℝ (Fin 3) := fun k => y + ((k : ℝ) / 8) • (x - y)
  have hc_norm : ∀ k : ℕ, k ≤ 8 → ‖c k‖ ≤ 2 := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / 8 := by positivity
    have hk1 : (k : ℝ) / 8 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      exact_mod_cast hk
    have heq : c k = (1 - (k : ℝ) / 8) • y + ((k : ℝ) / 8) • x := by
      simp only [c, smul_sub, sub_smul, one_smul]
      abel
    rw [heq]
    calc
      _ ≤ ‖(1 - (k : ℝ) / 8) • y‖ + ‖((k : ℝ) / 8) • x‖ := norm_add_le _ _
      _ = (1 - (k : ℝ) / 8) * ‖y‖ + ((k : ℝ) / 8) * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hk0]
      _ ≤ (1 - (k : ℝ) / 8) * 2 + ((k : ℝ) / 8) * 2 := by
        gcongr
        linarith
      _ = 2 := by ring
  have hc_step : ∀ k : ℕ, ‖c (k + 1) - c k‖ ≤ 3 / 8 := by
    intro k
    have heq : c (k + 1) - c k = (1 / 8 : ℝ) • (x - y) := by
      simp only [c]
      push_cast
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have : ‖x - y‖ ≤ 3 := (norm_sub_le x y).trans (by linarith)
    linarith
  have hc8 : c 8 = x := by
    simp only [c]
    norm_num
  have hcomplex : ∀ k : ℕ, k ≤ 8 → ∀ w : EuclideanSpace ℂ (Fin 3),
      ‖w - realSlice (c k)‖ ≤ 1 / 2 → ‖F w‖ ≤ C ^ (k + 1) * B := by
    intro k
    induction k with
    | zero =>
      intro _ w hw
      have h := hstep F hrel hF (c 0) (by linarith [hc_norm 0 (by norm_num)]) B hB
        (by
          intro z hz
          apply hbase z
          simpa [c] using hz) w hw
      simpa using h
    | succ k ih =>
      intro hk w hw
      have hprev := ih (by omega)
      have hreal : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z - c (k + 1)‖ ≤ 1 / 8 →
          ‖F (realSlice z)‖ ≤ C ^ (k + 1) * B := by
        intro z hz
        apply hprev
        rw [← map_sub, norm_realSlice_apply]
        calc
          ‖z - c k‖ = ‖(z - c (k + 1)) + (c (k + 1) - c k)‖ := by abel_nf
          _ ≤ ‖z - c (k + 1)‖ + ‖c (k + 1) - c k‖ := norm_add_le _ _
          _ ≤ 1 / 8 + 3 / 8 := add_le_add hz (hc_step k)
          _ = 1 / 2 := by norm_num
      have h := hstep F hrel hF (c (k + 1)) (by linarith [hc_norm (k + 1) hk])
        (C ^ (k + 1) * B) (by positivity) hreal w hw
      calc
        ‖F w‖ ≤ C * (C ^ (k + 1) * B) := h
        _ = C ^ (k + 1 + 1) * B := by ring
  intro w hw
  have h := hcomplex 8 le_rfl w (by rwa [hc8])
  simpa using h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet
