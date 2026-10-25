-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.RobustTests, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/RobustTests.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RobustTests.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RobustTests.lean.
-- Only the source value-norming declarations used here are retained; earlier provenance is preserved.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RobustTests.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Transfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Assertion
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.SampledBranch

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open Metric
open scoped ContDiff

theorem HasRealExtension.contDiffOn {D : ℕ} {f : Base → ℝ}
    (hf : HasRealExtension D f) : ContDiffOn ℝ ∞ f (ball 0 4) := by
  obtain ⟨F, P, hP, hdeg, hF, hrel, hmatch⟩ := hf
  intro x hx
  exact (DenseJet.contDiffAt_real_slice (hF.of_le le_top)
    (fun y hy => hmatch y (by simpa only [mem_ball, dist_zero_right] using hy))
    (by simpa only [mem_ball, dist_zero_right] using hx)).contDiffWithinAt

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Combine the point and direction transfers shared by x0491. The first
term pays for moving the base point and the second for moving the direction. -/
theorem diagonal_jet_point_direction_bound {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) {M B : ℝ}
    (hM : ∀ z ∈ U, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ M)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (hB : ‖iteratedFDeriv ℝ k f y‖ ≤ B) (p v : E) :
    |iteratedFDeriv ℝ k f x (fun _ => p) - iteratedFDeriv ℝ k f y (fun _ => v)| ≤
      M * ‖x - y‖ * ‖p‖ ^ k + B * k * max ‖p‖ ‖v‖ ^ (k - 1) * ‖p - v‖ := by
  have hmove := DenseJet.Transfer.norm_iteratedFDeriv_sub_le hU hconv hf k hM hy hx
  have hpoint : |iteratedFDeriv ℝ k f x (fun _ => p) -
      iteratedFDeriv ℝ k f y (fun _ => p)| ≤ M * ‖x - y‖ * ‖p‖ ^ k := by
    have hh := (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y).le_opNorm (fun _ => p)
    have heval : |iteratedFDeriv ℝ k f x (fun _ => p) -
        iteratedFDeriv ℝ k f y (fun _ => p)| ≤
        ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ * ‖p‖ ^ k := by
      simpa using hh
    exact heval.trans (mul_le_mul_of_nonneg_right hmove (by positivity))
  have hdir := DenseJet.Transfer.abs_diagonal_sub_le (iteratedFDeriv ℝ k f y) p v
  have hdir' : |iteratedFDeriv ℝ k f y (fun _ => p) -
      iteratedFDeriv ℝ k f y (fun _ => v)| ≤
      B * k * max ‖p‖ ‖v‖ ^ (k - 1) * ‖p - v‖ := by
    apply hdir.trans
    gcongr
  exact (abs_sub_le _ _ _).trans (add_le_add hpoint hdir')

/-- A small value on an actual trajectory transfers to a nearby fixed
direction at a nearby point, with one explicit mesh-error term. -/
theorem directional_sample_transfer {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) {B A h b : ℝ} (hA : 1 ≤ A) (hh : 0 ≤ h)
    (hnext : ∀ z ∈ U, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ B)
    {x y p v : E} (hx : x ∈ U) (hy : y ∈ U)
    (hcurrent : ‖iteratedFDeriv ℝ k f y‖ ≤ B)
    (hp : ‖p‖ ≤ A) (hv : ‖v‖ ≤ A) (hxy : ‖x - y‖ ≤ h) (hpv : ‖p - v‖ ≤ h)
    (hsample : |iteratedFDeriv ℝ k f y (fun _ => v)| ≤ b) :
    |iteratedFDeriv ℝ k f x (fun _ => p)| ≤ b + B * h * (A ^ k + k * A ^ (k - 1)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hcurrent
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have herror := diagonal_jet_point_direction_bound hU hconv hf k hnext hx hy hcurrent p v
  have herror' : |iteratedFDeriv ℝ k f x (fun _ => p) -
      iteratedFDeriv ℝ k f y (fun _ => v)| ≤
      B * h * A ^ k + B * k * A ^ (k - 1) * h := by
    apply herror.trans
    gcongr
    exact max_le hp hv
  have htriangle : |iteratedFDeriv ℝ k f x (fun _ => p)| ≤
      |iteratedFDeriv ℝ k f x (fun _ => p) - iteratedFDeriv ℝ k f y (fun _ => v)| +
        |iteratedFDeriv ℝ k f y (fun _ => v)| := by
    simpa only [sub_add_cancel] using abs_add_le
      (iteratedFDeriv ℝ k f x (fun _ => p) - iteratedFDeriv ℝ k f y (fun _ => v))
      (iteratedFDeriv ℝ k f y (fun _ => v))
  exact htriangle.trans ((add_le_add herror' hsample).trans_eq (by ring))

/-- Every order through six uses a common fixed power in the transfer
loss. This lets the geometric sampling step absorb all direction and
point errors in one parameter budget. -/
theorem bounded_order_directional_sample_transfer {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (hk : k ≤ 6) {B A h b : ℝ} (hA : 2 ≤ A) (hh : 0 ≤ h)
    (hnext : ∀ z ∈ U, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ B)
    {x y p v : E} (hx : x ∈ U) (hy : y ∈ U)
    (hcurrent : ‖iteratedFDeriv ℝ k f y‖ ≤ B)
    (hp : ‖p‖ ≤ A) (hv : ‖v‖ ≤ A) (hxy : ‖x - y‖ ≤ h) (hpv : ‖p - v‖ ≤ h)
    (hsample : |iteratedFDeriv ℝ k f y (fun _ => v)| ≤ b) :
    |iteratedFDeriv ℝ k f x (fun _ => p)| ≤ b + B * A ^ 9 * h := by
  have hAone : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hcurrent
  have hfactor : A ^ k + k * A ^ (k - 1) ≤ A ^ 9 := by
    have hprevious : A ^ (k - 1) ≤ A ^ k := pow_le_pow_right₀ hAone (Nat.sub_le _ _)
    have hkreal : (k : ℝ) ≤ 6 := by exact_mod_cast hk
    have hseven : (7 : ℝ) ≤ A ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA 3
      norm_num at hh
      linarith
    calc
      A ^ k + k * A ^ (k - 1) ≤ A ^ k + k * A ^ k := by gcongr
      _ = (1 + (k : ℝ)) * A ^ k := by ring
      _ ≤ 7 * A ^ k := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ A ^ 3 * A ^ k := mul_le_mul_of_nonneg_right hseven (by positivity)
      _ = A ^ (k + 3) := by rw [pow_add]; ring
      _ ≤ A ^ 9 := pow_le_pow_right₀ hAone (by omega)
  calc
    _ ≤ b + B * h * (A ^ k + k * A ^ (k - 1)) :=
      directional_sample_transfer hU hconv hf k hAone hh hnext hx hy hcurrent hp hv hxy hpv hsample
    _ ≤ b + B * h * A ^ 9 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfactor (mul_nonneg hB0 hh))
    _ = _ := by ring

end

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
