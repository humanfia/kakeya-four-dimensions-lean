-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeBranchSigns, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeBranchSigns.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeBranchSigns.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeBranchSigns.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeBranchSigns.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeBranch

/-! # Actual corrected-root signs select admissible native core branches -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial Metric
open k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- Any actual exact root with the branch's strict derivative sign IS
the chosen local branch value. This is pointwise in the ORIGINAL
translated coordinates and includes zero hidden curvature. -/
theorem LocalNativeBranchData.exact_signed_root
    {D : ℕ} {P : Poly} {c : Fin 3 → ℝ} {scale σ : ℝ}
    {F : EuclideanSpace ℂ (Fin 3) → ℂ} {f : Base → ℝ}
    (hdata : LocalNativeBranchData D P c scale σ F f) (hP : P.totalDegree ≤ 2)
    (x : Base) (hx : x ∈ ball (0 : Base) 4) (w : ℝ)
    (hw : eval (Fin.snoc (fun j => c j + scale * x j) w) P = 0)
    (hsign : 0 < eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) * σ) :
    w = f x := by
  obtain ⟨hroot, hsignf⟩ := hdata.2.2.2.1 x hx
  have hf : curvature P 3 / 2 * (f x) ^ 2 +
      eval (fun j => c j + scale * x j) (restrictBase (pderiv 3 P)) * f x +
      eval (fun j => c j + scale * x j) (restrictBase P) = 0 := by
    rw [eval_snoc_quadratic P hP] at hroot
    change eval (fun j => c j + scale * x j) (restrictBase P) +
      eval (fun j => c j + scale * x j) (restrictBase (pderiv 3 P)) * f x +
      curvature P 3 * (f x) ^ 2 / 2 = 0 at hroot
    linear_combination hroot
  apply native_equation_signed_root_unique P hP _ w (f x) σ hw hf hsign
  simpa only [native_equation_derivative P hP] using hsignf

/-- In the linear case, a good center and one valid branch force the
hidden derivative to keep its center sign on the whole real core.
Thus ANY strict sign seen at an actual core point is admissible at the
center. The hidden value at that point is arbitrary. -/
theorem native_core_sign_admissible
    {D : ℕ} (P : Poly) (hP : P.totalDegree ≤ 2) (c : Fin 3 → ℝ) (scale : ℝ)
    (hdisc : 0 < eval c (baseDiscriminant P))
    (hfamily : ∀ σ : ℝ, σ ≠ 0 →
      (curvature P 3 = 0 → 0 < eval c (restrictBase (pderiv 3 P)) * σ) →
      LocalNativeBranch D P c scale σ)
    (x : Base) (hx : x ∈ ball (0 : Base) 4) (w σ : ℝ)
    (hsign : 0 < eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) * σ) :
    curvature P 3 = 0 → 0 < eval c (restrictBase (pderiv 3 P)) * σ := by
  intro hzero
  let b := eval c (restrictBase (pderiv 3 P))
  have hbsq : 0 < b ^ 2 := by
    simpa [b, native_equation_discriminant, hzero] using hdisc
  have hbne : b ≠ 0 := by
    intro hb
    rw [hb] at hbsq
    norm_num at hbsq
  obtain ⟨F, f, hdata⟩ := hfamily b hbne (fun _ => by simpa only [pow_two] using hbsq)
  have hroot := (hdata.2.2.2.1 x hx).2
  have hderiv (t : ℝ) :
      eval (Fin.snoc (fun j => c j + scale * x j) t) (pderiv 3 P) =
        eval (fun j => c j + scale * x j) (restrictBase (pderiv 3 P)) := by
    rw [native_equation_derivative P hP]
    simp [hzero]
  rw [hderiv] at hroot hsign
  change 0 < b * σ
  rcases mul_pos_iff.mp hroot with ⟨hz, hb⟩ | ⟨hz, hb⟩
  · rcases mul_pos_iff.mp hsign with ⟨_, hσ⟩ | ⟨hz', _⟩
    · exact mul_pos hb hσ
    · linarith
  · rcases mul_pos_iff.mp hsign with ⟨hz', _⟩ | ⟨_, hσ⟩
    · linarith
    · exact mul_pos_of_neg_of_neg hb hσ

/-- Every simple actual root point in a good core selects one of TWO
admissible signed branches. No nonvanishing-curvature assumption is used.
Applied to rootLift, this is the actual root/sign label of the entry. -/
theorem exists_admissible_native_core_sign
    {D : ℕ} (P : Poly) (hP : P.totalDegree ≤ 2) (c : Fin 3 → ℝ) (scale : ℝ)
    (hdisc : 0 < eval c (baseDiscriminant P))
    (hfamily : ∀ σ : ℝ, σ ≠ 0 →
      (curvature P 3 = 0 → 0 < eval c (restrictBase (pderiv 3 P)) * σ) →
      LocalNativeBranch D P c scale σ)
    (x : Base) (hx : x ∈ ball (0 : Base) 4) (w : ℝ)
    (hsimple : eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) * σ ∧
      LocalNativeBranch D P c scale σ := by
  rcases lt_or_gt_of_ne hsimple with hnegative | hpositive
  · have hs : 0 < eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) * (-1) := by
      linarith
    exact ⟨-1, Or.inr rfl, hs, hfamily (-1) (by norm_num)
      (native_core_sign_admissible P hP c scale hdisc hfamily x hx w (-1) hs)⟩
  · have hs : 0 < eval (Fin.snoc (fun j => c j + scale * x j) w) (pderiv 3 P) * 1 := by
      simpa only [mul_one] using hpositive
    exact ⟨1, Or.inl rfl, hs, hfamily 1 one_ne_zero
      (native_core_sign_admissible P hP c scale hdisc hfamily x hx w 1 hs)⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
