-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Graph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Graph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Graph.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Graph.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Group
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarShearCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLipschitz

set_option autoImplicit false

/-!
# The residual graph on a sliced starting group (version 2)

The `j = 2` counterpart of `exists_starting_residual_graph` of o078 (session x0662, branch
`x0662` at `f2bac599`, `ScalarBlockGraph.lean`).  On the trajectories labelled at the anchor time
`t₀` in one sliced group (same `H`-bin of `S(t₀)`, same `p`-bin of `y_{k'}(t₀)`), the residual
slope `R(t₀) = x'(t₀) - F(t₀) · y'` is, up to `6 K² (p + H)`, a `1`-Lipschitz function `G` of
the scaled fitted coordinate `3 K² y_k(t₀)` (paper: "freezing the other coordinates of `Y_l`
makes `q_l` an approximately Lipschitz function of the remaining coordinate").
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

theorem sum_rev (f : Fin 2 → ℝ) (k : Fin 2) : f k + f (Fin.rev k) = f 0 + f 1 := by
  fin_cases k
  · rfl
  · show f 1 + f 0 = f 0 + f 1
    ring

/-- The labels of one sliced starting group. -/
def slicedLabels (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ)) (t₀ H p : ℝ)
    (k : Fin 2) (b : ℤ × ℤ) : Set Λ :=
  {l | (l, t₀) ∈ E ∧ slicedCode c F t₀ H p k l = b}

theorem slicedLabels_measurable {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {E : Set (Λ × ℝ)}
    (hE : MeasurableSet E) (F : ℝ → Fin 2 → ℝ) (t₀ H p : ℝ) (k : Fin 2) (b : ℤ × ℤ) :
    MeasurableSet (slicedLabels c F E t₀ H p k b) :=
  (measurable_prodMk_right hE).inter
    (measurable_slicedCode hc F t₀ H p k (MeasurableSet.singleton b))

/-- The scaling of the fitted coordinate. -/
def graphScale (K : ℝ) : ℝ := 3 * K ^ 2

theorem exists_sliced_residual_graph {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K ζ d H p : ℝ} (h : UpperHyp ν c E F K ζ d) (hK : 1 ≤ K)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H) (hp : 0 < p) (hp1 : p ≤ 1) (t₀ : ℝ) (k : Fin 2)
    (b : ℤ × ℤ) :
    ∃ G : ℝ → ℝ, (∀ s t, |G s - G t| ≤ |s - t|) ∧
      (∀ l ∈ slicedLabels c F E t₀ H p k b,
        |zR F (c l) t₀ - G (graphScale K * zy (c l) t₀ k)| ≤ 6 * K ^ 2 * (p + H)) ∧
      ∀ l ∈ slicedLabels c F E t₀ H p k b, |G (graphScale K * zy (c l) t₀ k)| ≤ 17 * K ^ 2 := by
  set A := slicedLabels c F E t₀ H p k b with hAdef
  have hK0 : 0 ≤ K := by linarith
  have hL : 0 < graphScale K := by unfold graphScale; positivity
  have hF := h.row_bounded t₀
  have ha : |F t₀ k| ≤ K := (abs_le_norm (F t₀) k).trans hF
  have hb : |F t₀ (Fin.rev k)| ≤ K := (abs_le_norm (F t₀) (Fin.rev k)).trans hF
  -- same scalar bin
  have hS : ∀ l ∈ A, ∀ l' ∈ A,
      |(zx (c l) t₀ - F t₀ k * zy (c l) t₀ k - F t₀ (Fin.rev k) * zy (c l) t₀ (Fin.rev k)) -
        (zx (c l') t₀ - F t₀ k * zy (c l') t₀ k -
          F t₀ (Fin.rev k) * zy (c l') t₀ (Fin.rev k))| ≤ H := by
    intro l hl l' hl'
    have hcode : slicedCode c F t₀ H p k l = slicedCode c F t₀ H p k l' := hl.2.trans hl'.2.symm
    simp only [slicedCode, Prod.ext_iff] at hcode
    have hh := same_mesh_cell_close hH hcode.1
    have e : ∀ m : Λ, zx (c m) t₀ - F t₀ k * zy (c m) t₀ k -
        F t₀ (Fin.rev k) * zy (c m) t₀ (Fin.rev k) = zS F (c m) t₀ := by
      intro m; simp only [zS, dot_split (F t₀) (zy (c m) t₀) k]; ring
    rw [e l, e l']
    exact hh
  -- the residual comparison at the anchor time
  have hR : ∀ l ∈ A, ∀ l' ∈ A,
      |zR F (c l) t₀ - zR F (c l') t₀| ≤
        K * (|zx (c l) t₀ - zx (c l') t₀| + |zy (c l) t₀ k - zy (c l') t₀ k| +
          |zy (c l) t₀ (Fin.rev k) - zy (c l') t₀ (Fin.rev k)| + ζ) := by
    intro l hl l' hl'
    have hh := h.residual_comparison (l, t₀) hl.1 (l', t₀) hl'.1
    simp only [sub_self, abs_zero, zero_add] at hh
    refine hh.trans (le_of_eq ?_)
    have hsum := sum_rev (fun i => |zy (c l) t₀ i - zy (c l') t₀ i|) k
    beta_reduce at hsum
    rw [show |zx (c l) t₀ - zx (c l') t₀| + |zy (c l) t₀ k - zy (c l') t₀ k| +
        |zy (c l) t₀ (Fin.rev k) - zy (c l') t₀ (Fin.rev k)| + ζ =
        |zx (c l) t₀ - zx (c l') t₀| + (|zy (c l) t₀ k - zy (c l') t₀ k| +
        |zy (c l) t₀ (Fin.rev k) - zy (c l') t₀ (Fin.rev k)|) + ζ by ring, hsum]
    ring
  have hcmp := scalar_frozen_residual_comparison A (fun l => zx (c l) t₀)
    (fun l => zy (c l) t₀ k) (fun l => zy (c l) t₀ (Fin.rev k)) (fun l => zR F (c l) t₀)
    hK0 hH.le hζH ha hb hS hR
  -- the slice
  have hslice : ∀ l ∈ A, ∀ l' ∈ A,
      |zy (c l) t₀ (Fin.rev k) - zy (c l') t₀ (Fin.rev k)| ≤ p := by
    intro l hl l' hl'
    have hcode : slicedCode c F t₀ H p k l = slicedCode c F t₀ H p k l' := hl.2.trans hl'.2.symm
    simp only [slicedCode, Prod.ext_iff] at hcode
    exact same_mesh_cell_close hp hcode.2
  have hcmp' : ∀ l ∈ A, ∀ l' ∈ A,
      |zR F (c l) t₀ - zR F (c l') t₀| ≤
        graphScale K * |zy (c l) t₀ k - zy (c l') t₀ k| + 3 * K ^ 2 * (p + H) := by
    intro l hl l' hl'
    have hh := hcmp l hl l' hl'
    have hw := hslice l hl l' hl'
    have hcoef : 2 * K + K ^ 2 ≤ 3 * K ^ 2 := by nlinarith
    have h1 : (2 * K + K ^ 2) * (|zy (c l) t₀ k - zy (c l') t₀ k| +
        |zy (c l) t₀ (Fin.rev k) - zy (c l') t₀ (Fin.rev k)| + H) ≤
        3 * K ^ 2 * (|zy (c l) t₀ k - zy (c l') t₀ k| + p + H) := by
      apply mul_le_mul hcoef (by linarith) (by positivity) (by positivity)
    unfold graphScale
    nlinarith
  obtain ⟨G, hG, hnear⟩ := lipschitz_coordinate_factor_unit A (fun l => zy (c l) t₀ k)
    (fun l => zR F (c l) t₀) hL hcmp'
  refine ⟨G, hG, fun l hl => by have := hnear l hl; linarith, ?_⟩
  intro l hl
  have hq := (h.active_bounds hl.1).2.2.2.1
  have hn := hnear l hl
  have hpH : p + H ≤ 2 := by linarith
  have hh := abs_sub_le (G (graphScale K * zy (c l) t₀ k)) (zR F (c l) t₀) 0
  rw [sub_zero, sub_zero, abs_sub_comm (G (graphScale K * zy (c l) t₀ k)) (zR F (c l) t₀)] at hh
  have hKsq : K ≤ K ^ 2 := by nlinarith
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
