/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/AnchorEndpoints.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Kernel
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Set Metric

theorem eval_map_emb (P : MvPolynomial (Fin 3) ℝ) (α : EuclideanSpace ℝ (Fin 3)) :
    MvPolynomial.eval (fun i => emb α i) (P.map (algebraMap ℝ ℂ)) =
      (MvPolynomial.eval (fun i => α i) P : ℂ) := by
  change MvPolynomial.eval (fun i => (α i : ℂ)) (P.map (algebraMap ℝ ℂ)) = _
  rw [MvPolynomial.eval_map]
  exact Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal P (fun i => α i)


/-- A safe tube also bounds the real discriminant at its anchor endpoint. -/
theorem SafeFor.anchor_bounds {ρ : ℝ} (hρ : 0 < ρ)
    {P P' : MvPolynomial (Fin 3) ℝ}
    {z₀ α : EuclideanSpace ℝ (Fin 3)} {σ : ℂ}
    (hsafe : SafeFor ρ P P' z₀ α σ) :
    ρ ≤ |MvPolynomial.eval (fun i => α i) P| ∧
      ρ ≤ |MvPolynomial.eval (fun i => α i) P'| := by
  have hmem : emb α ∈ safePath z₀ α σ := Or.inr (right_mem_segment ℝ _ _)
  have htube := self_subset_thickening hρ _ hmem
  have hh := hsafe (emb α) htube
  simpa only [eval_map_emb, Complex.norm_real, Real.norm_eq_abs] using hh

end Submission.Obl.k4_matched_pair_representative_realization.Selection
