-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.AffineTransport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/AffineTransport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/AffineTransport.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/AffineTransport.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/AffineTransport.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

/-!
# Transporting a restored test to the original coordinates

Only the first three coordinates undergo a base affine change.  The hidden
coordinate is multiplied by the original packet's derivative scale.  In
particular the two hidden derivatives acquire exactly one and two factors
of that scale.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

abbrev Poly := MvPolynomial (Fin 4) ℝ
abbrev Base := EuclideanSpace ℝ (Fin 3)

/-- An affine base change, followed by a scaling of the hidden coordinate. -/
def coordinateSubstitution (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (B : ℝ) : Fin 4 → Poly :=
  ![C (c 0) + ∑ j : Fin 3, C (M 0 j) * X j.castSucc,
    C (c 1) + ∑ j : Fin 3, C (M 1 j) * X j.castSucc,
    C (c 2) + ∑ j : Fin 3, C (M 2 j) * X j.castSucc,
    C B * X 3]

/-- The corresponding map on points, with no size restriction on the hidden coordinate. -/
def coordinateMap (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (B : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![c 0 + ∑ j : Fin 3, M 0 j * x j.castSucc,
    c 1 + ∑ j : Fin 3, M 1 j * x j.castSucc,
    c 2 + ∑ j : Fin 3, M 2 j * x j.castSucc,
    B * x 3]

/-- Pull the normalized polynomial back to the original coordinates. -/
def transportPolynomial (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (B : ℝ) (P : Poly) : Poly :=
  bind₁ (coordinateSubstitution c M B) P

lemma coordinateSubstitution_degree (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (i : Fin 4) :
    (coordinateSubstitution c M B i).totalDegree ≤ 1 := by
  have hmul (a : ℝ) (j : Fin 4) : (C a * X j : Poly).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  have hbase (a : ℝ) (v : Fin 3 → ℝ) :
      (C a + ∑ j : Fin 3, C (v j) * X j.castSucc : Poly).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    exact max_le (by simp) (totalDegree_finsetSum_le fun j _ => hmul _ _)
  fin_cases i <;> change _ ≤ 1
  all_goals first | exact hbase _ _ | exact hmul _ _

lemma totalDegree_transportPolynomial_le (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly) :
    (transportPolynomial c M B P).totalDegree ≤ P.totalDegree := by
  exact k4_quadratic_selector_sweep.totalDegree_bind_affine _
    (coordinateSubstitution_degree c M B) P

lemma eval_transportPolynomial (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly) (x : Fin 4 → ℝ) :
    eval x (transportPolynomial c M B P) = eval (coordinateMap c M B x) P := by
  change eval₂Hom (RingHom.id ℝ) x (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 4 → ℝ => eval₂Hom (RingHom.id ℝ) f P)
  funext i
  fin_cases i <;> simp [coordinateSubstitution, coordinateMap]

lemma hidden_derivative_substitution (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (i : Fin 4) :
    pderiv (3 : Fin 4) (coordinateSubstitution c M B i) =
      if i = 3 then C B else 0 := by
  fin_cases i <;> simp [coordinateSubstitution, Fin.sum_univ_succ]

/-- A chain rule using only the hidden-coordinate derivative of each substitution. -/
lemma pderiv_bind_hidden (v : Fin 4 → Poly) (B : ℝ)
    (hv : ∀ i, pderiv (3 : Fin 4) (v i) = if i = 3 then C B else 0)
    (P : Poly) :
    pderiv (3 : Fin 4) (bind₁ v P) = C B * bind₁ v (pderiv (3 : Fin 4) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, mul_add]
  | mul_X P i hP =>
    simp only [map_mul, bind₁_X_right, pderiv_mul, hP, hv, pderiv_X,
      map_add, map_mul, Pi.single_apply]
    by_cases hi : i = 3
    · subst i
      simp
      ring
    · simp [hi]
      ring

lemma pderiv_transportPolynomial (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly) :
    pderiv (3 : Fin 4) (transportPolynomial c M B P) =
      C B * transportPolynomial c M B (pderiv (3 : Fin 4) P) :=
  pderiv_bind_hidden _ B (hidden_derivative_substitution c M B) P

lemma pderiv_twice_transportPolynomial (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (transportPolynomial c M B P)) =
      C (B ^ 2) * transportPolynomial c M B
        (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [pderiv_transportPolynomial, pderiv_C_mul, pderiv_transportPolynomial]
  simp [pow_two, mul_assoc]

/-- All three pointwise quantities used by residual candidates transform exactly. -/
theorem eval_transport_hidden_derivatives (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly) (x : Fin 4 → ℝ) :
    eval x (pderiv (3 : Fin 4) (transportPolynomial c M B P)) =
        B * eval (coordinateMap c M B x) (pderiv (3 : Fin 4) P) ∧
      eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4)
        (transportPolynomial c M B P))) =
        B ^ 2 * eval (coordinateMap c M B x)
          (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  simp [pderiv_transportPolynomial, eval_transportPolynomial, pow_two, mul_assoc]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
