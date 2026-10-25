/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingCoordinates.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/MatchingCoordinates.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetJets
import Submission.Obl.k4_algebraic_real_jet_comparison.AffineRelations

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric MvPolynomial

/-- Local holomorphic quadratic sheets become degree-two sheets on the exact
fixed domain of the supplied Matching hypothesis by an invertible base scaling. -/
theorem local_sheet_isMatchSheet (P : MvPolynomial (Fin 4) ℂ)
    (hP : P ≠ 0) (hdegree : P.totalDegree ≤ 2)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (c : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball (emb c) (8 * r)))
    (hroot : ∀ z ∈ ball (emb c) (8 * r),
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z)) P = 0)
    (hreal : ∀ x ∈ ball c (8 * r), (F (emb x)).im = 0) :
    IsMatchSheet (fun z => F (emb c + ((2 * r : ℝ) : ℂ) • z)) := by
  let a : ℂ := (2 * r : ℝ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hanorm : ‖a‖ = 2 * r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * r)]
  have hmap : MapsTo (fun z : EuclideanSpace ℂ (Fin 3) => emb c + a • z)
      (ball 0 4) (ball (emb c) (8 * r)) := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hanorm]
    have hz' : ‖z‖ < 4 := mem_ball_zero_iff.mp hz
    nlinarith
  have hg : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) => emb c + a • z) := by
    fun_prop
  let Q := Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation
    (fun i => emb c i) a 1 P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation_injective
      (fun i => emb c i) ha one_ne_zero
    simpa only [map_zero] using h
  have hQdegree : Q.totalDegree ≤ 2 :=
    (Submission.Obl.k4_algebraic_real_jet_comparison.totalDegree_affineRelation_le _ _ _ P).trans hdegree
  refine ⟨⟨Q, hQ, hQdegree, ?_⟩, hF.comp hg.differentiableOn hmap, ?_⟩
  · intro z hz
    rw [Submission.Obl.k4_algebraic_real_jet_comparison.eval_affineRelation]
    simp only [one_mul]
    convert hroot (emb c + a • z) (hmap hz) using 1 <;> rfl
  · intro x hx
    have hemb : emb (c + (2 * r) • x) = emb c + a • emb x := by
      ext i
      change ((c i + (2 * r) * x i : ℝ) : ℂ) = (c i : ℂ) + a * (x i : ℂ)
      dsimp [a]
      push_cast
      rfl
    change (F (emb c + a • emb x)).im = 0
    rw [← hemb]
    apply hreal
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * r)]
    nlinarith

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
