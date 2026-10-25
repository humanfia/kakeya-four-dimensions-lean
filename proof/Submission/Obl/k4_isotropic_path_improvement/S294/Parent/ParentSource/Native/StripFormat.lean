-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripFormat, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripFormat.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripFormat.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripFormat.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripFormat.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAssignments
import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatRule
import Submission.Lib.K4XInterface.Formats

/-! Priority strip assignments have a linear test count and fixed degree.
The affine velocity and midpoint formulas are supplied as polynomial evaluations. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MvPolynomial
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

theorem stripAssignment_format {d m D : ℕ} {H w r : ℝ}
    (A : Set (Fin d → ℝ)) (V M : (Fin d → ℝ) → StripSpace)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (i : Fin m) (z : ℤ)
    (p : Fin m → MvPolynomial (Fin d) ℝ) (q : MvPolynomial (Fin d) ℝ)
    (hp : ∀ j, (p j).totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (hevalp : ∀ x j, MvPolynomial.eval x (p j) = inner ℝ (V x) (n j) - β j)
    (hevalq : ∀ x, MvPolynomial.eval x q = inner ℝ (M x) (n i) / r)
    (hA : gfmt d H D A) :
    gfmt d (H + 2 * (m : ℝ) + 2) (max D 1)
      (stripAssignment A V M n β w r i z) := by
  classical
  have hsign (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ 1) :
      gfmt d 1 1 {x | 0 ≤ MvPolynomial.eval x P} :=
    gfmt_mono le_rfl hP (gfmt_nonneg P)
  have hshift (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ 1) (c : ℝ) :
      (C c + P).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) hP)
  let S : Fin m → Set (Fin d → ℝ) := fun j => {x | |MvPolynomial.eval x (p j)| ≤ w}
  have hS (j : Fin m) : gfmt d 2 1 (S j) := by
    have h1 := hsign (C w + -(p j)) (hshift _ (by simpa using hp j) w)
    have h2 := hsign (C w + p j) (hshift _ (hp j) w)
    have heq : S j = {x | 0 ≤ MvPolynomial.eval x (C w + -(p j))} ∩
        {x | 0 ≤ MvPolynomial.eval x (C w + p j)} := by
      ext x
      simp only [S, mem_ofPred_eq, mem_inter_iff, map_add, map_neg, eval_C, abs_le]
      constructor
      · rintro ⟨hlo, hhi⟩
        constructor <;> linarith
      · rintro ⟨hhi, hlo⟩
        constructor <;> linarith
    rw [heq]
    convert gfmt_inter h1 h2 using 1 <;> norm_num
  have hpriority : gfmt d (2 * (m : ℝ)) 1
      (V ⁻¹' Submission.Lib.K4FinitePlankAtlases.firstAssignment
        (fun j => affineStrip (n j) (β j) w) i) := by
    have h := Submission.Obl.k4_coarsened_outer_horizon_composition.fmt_rule_uniform
      S 2 hS (fun b => b i ∧ ∀ j, j < i → ¬ b j)
    change gfmt d ((Fintype.card (Fin m) : ℝ) * 2) 1
      {x | x ∈ S i ∧ ∀ j, j < i → x ∉ S j} at h
    have heq : (V ⁻¹' Submission.Lib.K4FinitePlankAtlases.firstAssignment
        (fun j => affineStrip (n j) (β j) w) i) =
        {x | x ∈ S i ∧ ∀ j, j < i → x ∉ S j} := by
      ext x
      simp only [mem_preimage, Submission.Lib.K4FinitePlankAtlases.firstAssignment,
        affineStrip, S, mem_ofPred_eq, hevalp]
    rw [heq]
    simpa only [Fintype.card_fin, mul_comm] using h
  have hbin : gfmt d 2 1 {x | ⌊inner ℝ (M x) (n i) / r⌋ = z} := by
    have h1 := hsign (C (-(z : ℝ)) + q) (hshift _ hq _)
    have h2 := hsign (C (-((z : ℝ) + 1)) + q) (hshift _ hq _)
    have heq : {x | ⌊inner ℝ (M x) (n i) / r⌋ = z} =
        {x | 0 ≤ MvPolynomial.eval x (C (-(z : ℝ)) + q)} ∩
        {x | 0 ≤ MvPolynomial.eval x (C (-((z : ℝ) + 1)) + q)}ᶜ := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, map_add, eval_C,
        hevalq, Int.floor_eq_iff, not_le]
      constructor
      · rintro ⟨hlo, hhi⟩
        constructor <;> linarith
      · rintro ⟨hlo, hhi⟩
        constructor <;> linarith
    rw [heq]
    convert gfmt_inter h1 (gfmt_compl h2) using 1 <;> norm_num
  simpa only [stripAssignment, max_self, max_assoc] using
    gfmt_inter (gfmt_inter hA hpriority) hbin

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
