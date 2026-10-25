-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedFormat, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedFormat.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedFormat.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedFormat.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedFormat.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedAssignments
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPolynomials

/-! Coarse parameter-bin merging changes only the Boolean decision on the
original strip tests. Its test count remains linear in the fine net size. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MvPolynomial
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open Submission.Obl.k4_coarsened_outer_horizon_composition
open scoped RealInnerProductSpace

private theorem strip_abs_poly_format {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ 1) (w : ℝ) :
    gfmt d 2 1 {x | |MvPolynomial.eval x P| ≤ w} := by
  have hdeg (c : ℝ) : (C c + P).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) hP)
  have hdeg' : (C w + -P).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) (by simpa using hP))
  have h1 := gfmt_mono le_rfl hdeg' (gfmt_nonneg (C w + -P))
  have h2 := gfmt_mono le_rfl (hdeg w) (gfmt_nonneg (C w + P))
  have heq : {x | |MvPolynomial.eval x P| ≤ w} =
      {x | 0 ≤ MvPolynomial.eval x (C w + -P)} ∩
      {x | 0 ≤ MvPolynomial.eval x (C w + P)} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, map_add, map_neg, eval_C, abs_le]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  rw [heq]
  convert gfmt_inter h1 h2 using 1 <;> norm_num

theorem mergedStripAssignment_format {d m D : ℕ} {H w r : ℝ}
    (A : Set (Fin d → ℝ)) (V M : (Fin d → ℝ) → StripSpace)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (q : StripCodeLabel r n β) (z : ℤ)
    (P : Fin m → MvPolynomial (Fin d) ℝ) (Q : MvPolynomial (Fin d) ℝ)
    (hP : ∀ j, (P j).totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1)
    (hevalP : ∀ x j, MvPolynomial.eval x (P j) = inner ℝ (V x) (n j) - β j)
    (hevalQ : ∀ x, MvPolynomial.eval x Q =
      inner ℝ (M x) (n (canonicalStripIndex r n β q)) / r)
    (hA : gfmt d H D A) :
    gfmt d (H + 2 * (m : ℝ) + 2) (max D 1)
      (mergedStripAssignment A V M r n β w q z) := by
  classical
  let S : Fin m → Set (Fin d → ℝ) := fun j => {x | |MvPolynomial.eval x (P j)| ≤ w}
  have hS (j : Fin m) : gfmt d 2 1 (S j) := strip_abs_poly_format _ (hP j) w
  have hpriority : gfmt d (2 * (m : ℝ)) 1 (V ⁻¹' mergedStripCell r n β w q) := by
    have h := fmt_rule_uniform S 2 hS
      (fun b => ∃ i, stripParameterCode r (n i) (β i) = q.val ∧
        b i ∧ ∀ j, j < i → ¬ b j)
    change gfmt d ((Fintype.card (Fin m) : ℝ) * 2) 1
      {x | ∃ i, stripParameterCode r (n i) (β i) = q.val ∧
        x ∈ S i ∧ ∀ j, j < i → x ∉ S j} at h
    have heq : V ⁻¹' mergedStripCell r n β w q =
        {x | ∃ i, stripParameterCode r (n i) (β i) = q.val ∧
          x ∈ S i ∧ ∀ j, j < i → x ∉ S j} := by
      ext x
      simp only [mem_preimage, mem_mergedStripCell, S,
        Submission.Lib.K4FinitePlankAtlases.firstAssignment, affineStrip, mem_ofPred_eq,
        hevalP]
    rw [heq]
    simpa only [Fintype.card_fin, mul_comm] using h
  have hbin : gfmt d 2 1
      {x | ⌊inner ℝ (M x) (n (canonicalStripIndex r n β q)) / r⌋ = z} := by
    have h := fmt_floor_eq Q hQ z
    change gfmt d 2 1 {x | ⌊MvPolynomial.eval x Q⌋ = z} at h
    simpa only [hevalQ] using h
  simpa only [mergedStripAssignment, max_self, max_assoc] using
    gfmt_inter (gfmt_inter hA hpriority) hbin

theorem packetMergedStripAssignment_format {m D : ℕ} {H w r : ℝ}
    (A : Set (Fin 6 → ℝ)) (copy : ℕ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (t₀ h : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    (q : StripCodeLabel r n β) (z : ℤ) (hA : gfmt 6 H D A) :
    gfmt 6 (H + 2 * (m : ℝ) + 2) (max D 1)
      (mergedStripAssignment A (fun a => packetVelocity h Q u (copy, a))
        (fun a => packetPosition Q c u (copy, a) (t₀ + h / 2)) r n β w q z) := by
  apply mergedStripAssignment_format A _ _ n β q z
    (fun j => packetNormalVelocityPoly h Q u (n j) (β j))
    (packetMidpointBinPoly Q c u (n (canonicalStripIndex r n β q)) t₀ h r)
    (fun j => packetNormalVelocityPoly_degree _ _ _ _ _)
    (packetMidpointBinPoly_degree _ _ _ _ _ _ _) _ _ hA
  · intro a j
    exact eval_packetNormalVelocityPoly _ _ _ _ _ _ _
  · intro a
    exact eval_packetMidpointBinPoly _ _ _ _ _ _ _ _ _

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
