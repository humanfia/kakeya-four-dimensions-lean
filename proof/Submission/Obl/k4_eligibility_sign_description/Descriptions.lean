import Submission.Obl.k4_eligibility_sign_description.Families

namespace Submission.Obl.k4_eligibility_sign_description

noncomputable section

/-- A uniform description for a strict or weak absolute bound on a quadratic family. -/
lemma SignRep.quadratic_abs_family {σ X : Type*} (v : X → σ → ℝ) (strict : Bool)
    (F : ℝ → MvPolynomial σ ℝ) (hdeg : ∀ t, (F t).totalDegree ≤ 2)
    (hquad : ∀ x, Quadratic (fun t => MvPolynomial.eval (v x) (F t)))
    (H l r : ℝ) (hlr : l ≤ r) :
    SignRep v 12 4 (fun x => ∀ t ∈ Set.Icc l r,
      if strict then |MvPolynomial.eval (v x) (F t)| < H
      else |MvPolynomial.eval (v x) (F t)| ≤ H) := by
  have hminus := SignRep.quadratic_family v strict (fun t => MvPolynomial.C H - F t)
    (fun t => degree_sub_le (by simp only [MvPolynomial.totalDegree_C]; omega) (hdeg t))
    (fun x => by simpa using (hquad x).sub_const H) l r hlr
  have hplus := SignRep.quadratic_family v strict (fun t => MvPolynomial.C H + F t)
    (fun t => degree_add_le (by simp only [MvPolynomial.totalDegree_C]; omega) (hdeg t))
    (fun x => by simpa using (hquad x).add_const H) l r hlr
  refine (hminus.and hplus).congr ?_
  intro x
  cases strict
  · simp only [Positive, Bool.false_eq_true, ↓reduceIte, map_sub, map_add, MvPolynomial.eval_C]
    constructor
    · rintro ⟨hm, hp⟩ t ht
      exact abs_le.mpr ⟨by linarith [hp t ht], by linarith [hm t ht]⟩
    · intro h
      constructor <;> intro t ht <;> have hh := abs_le.mp (h t ht) <;> linarith
  · simp only [Positive, ↓reduceIte, map_sub, map_add, MvPolynomial.eval_C]
    constructor
    · rintro ⟨hm, hp⟩ t ht
      exact abs_lt.mpr ⟨by linarith [hp t ht], by linarith [hm t ht]⟩
    · intro h
      constructor <;> intro t ht <;> have hh := abs_lt.mp (h t ht) <;> linarith

lemma SignRep.trace_abs (P : MvPolynomial (Fin 4) ℝ) (hp : P.totalDegree ≤ 2)
    (H l r : ℝ) (hlr : l ≤ r) :
    SignRep coords 12 4 (fun z : E3 × E3 => ∀ t ∈ Set.Icc l r,
      |MvPolynomial.eval ![t, (z.2 + t • z.1) 0, (z.2 + t • z.1) 1,
        (z.2 + t • z.1) 2] P| ≤ H) := by
  simpa only [Bool.false_eq_true, ↓reduceIte, eval_tracePoly] using
    SignRep.quadratic_abs_family coords false (tracePoly P)
      (fun t => (degree_tracePoly P t).trans hp) (quadratic_tracePoly P hp) H l r hlr

lemma SignRep.derivative_large (P : MvPolynomial (Fin 4) ℝ) (hp : P.totalDegree ≤ 2)
    (b l r : ℝ) (hlr : l ≤ r) :
    SignRep coords 12 4 (fun z : E3 × E3 => ∃ t ∈ Set.Icc l r,
      b ≤ |MvPolynomial.eval ![t, (z.2 + t • z.1) 0, (z.2 + t • z.1) 1,
        (z.2 + t • z.1) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|) := by
  let Q := MvPolynomial.pderiv (3 : Fin 4) P
  have hQ : Q.totalDegree ≤ 2 := (degree_pderiv_le P _).trans hp
  have h := (SignRep.quadratic_abs_family coords true (tracePoly Q)
    (fun t => (degree_tracePoly Q t).trans hQ) (quadratic_tracePoly Q hQ) b l r hlr).not
  refine h.congr ?_
  intro z
  simp only [↓reduceIte, eval_tracePoly, not_forall, not_lt, exists_prop, Q]

lemma SignRep.transverse_norm (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2)
    (K l r : ℝ) (hK : 0 ≤ K) (hlr : l ≤ r) :
    SignRep coords 6 4 (fun z : E3 × E3 => ∀ t ∈ Set.Icc l r,
      ‖Matrix.toEuclideanLin M (WithLp.toLp 2
        (fun j : Fin 2 => (z.2 + t • z.1) j.castSucc - c j - t * u j))‖ ≤ K) := by
  refine (SignRep.quadratic_family coords false (transverseNormPoly M c u K)
    (degree_transverseNormPoly M c u K) (quadratic_transverseNormPoly M c u K) l r hlr).congr ?_
  intro z
  apply forall₂_congr
  intro t ht
  exact eval_transverseNormPoly M c u K t z hK

end
end Submission.Obl.k4_eligibility_sign_description
