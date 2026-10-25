-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/LocalSheets.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/LocalSheets.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Directional
import Submission.Obl.k4_algebraic_real_jet_comparison.AffineRelations

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set Metric MvPolynomial

/-- Normalize a local real algebraic sheet to the fixed comparison domain. The
polynomial degree is preserved and no coefficient conditioning is required. -/
noncomputable def localRealSheet {D : ℕ} (a : Real3) (r : ℝ) (hr : 0 < r)
    (f : Complex3 → ℂ) (P : MvPolynomial (Fin 4) ℂ)
    (hP : P ≠ 0) (hPD : P.totalDegree ≤ D)
    (hf : DifferentiableOn ℂ f (ball (emb a) r))
    (heq : ∀ z ∈ ball (emb a) r,
      eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) P = 0)
    (hreal : ∀ x : Real3, ‖x - a‖ < r → (f (emb x)).im = 0) : RealSheet D := by
  let s := r / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  let F : Complex3 → Complex3 := fun z => emb a + (s : ℂ) • z
  let Q := Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation
    (fun j : Fin 3 => (a j : ℂ)) (s : ℂ) 1 P
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hmap : MapsTo F (ball 0 4) (ball (emb a) r) := by
    intro z hz
    have hz' : ‖z‖ < 4 := mem_ball_zero_iff.mp hz
    rw [mem_ball, dist_eq_norm]
    have hnorm : ‖F z - emb a‖ = s * ‖z‖ := by
      simp only [F, add_sub_cancel_left, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm]
    dsimp [s]
    nlinarith
  refine
    { f := fun z => f (F z)
      P := Q
      nonzero := ?_
      degree := ?_
      holomorphic := hf.comp hF.differentiableOn hmap
      equation := ?_
      real_on_real := ?_ }
  · intro hzero
    apply hP
    apply Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation_injective
      (fun j : Fin 3 => (a j : ℂ)) hsC one_ne_zero
    simpa only [Q, map_zero] using hzero
  · exact (Submission.Obl.k4_algebraic_real_jet_comparison.totalDegree_affineRelation_le
      _ _ _ P).trans hPD
  · intro z hz
    dsimp only [Q]
    rw [Submission.Obl.k4_algebraic_real_jet_comparison.eval_affineRelation, one_mul]
    have hbase : (fun j : Fin 3 => (a j : ℂ) + (s : ℂ) * z j) =
        (fun j : Fin 3 => F z j) := by
      funext j
      change (emb a) j + (s : ℂ) * z j = F z j
      simp only [F, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hbase]
    exact heq (F z) (hmap hz)
  · intro x hx
    have hx' : ‖a + s • x - a‖ < r := by
      have hnorm : ‖a + s • x - a‖ = s * ‖x‖ := by
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      rw [hnorm]
      have hmul := mul_le_mul_of_nonneg_left hx hs.le
      dsimp [s] at hmul ⊢
      linarith
    have hemb : F (emb x) = emb (a + s • x) := by
      simpa only [F] using
        (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding_line a x s).symm
    rw [hemb]
    exact hreal (a + s • x) hx'

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
