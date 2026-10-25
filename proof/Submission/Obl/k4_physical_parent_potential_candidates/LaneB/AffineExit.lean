import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineDistance
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.VerticalReturn
import Submission.Obl.k4_seven_direction_local_degree_restoration.GraphTaylor

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set Metric MvPolynomial FubiniQuadric QuadraticTube

noncomputable section

namespace AffineExit

/-- An affine approximation on the unit ball has controlled coefficients
whenever the original function and its approximation error are bounded. -/
theorem approximation_coefficients {f : Base → ℝ} {H E c : ℝ} (L : Base →L[ℝ] ℝ)
    (hf : ∀ u ∈ closedBall (0:Base) 1, |f u| ≤ H)
    (hfit : ∀ u ∈ closedBall (0:Base) 1, |f u-c-L u| ≤ E) :
    |c| ≤ H+E ∧
    ∀ i:Fin 3, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ 2*H+2*E := by
  have h0 : (0:Base) ∈ closedBall (0:Base) 1 := by simp
  have hc0 : |f 0-c| ≤ E := by simpa using hfit 0 h0
  have hc : |c| ≤ H+E := by
    calc |c| = |f 0-(f 0-c)| := by congr 1; ring
      _ ≤ |f 0|+|f 0-c| := abs_sub _ _
      _ ≤ H+E := add_le_add (hf 0 h0) hc0
  refine ⟨hc,?_⟩
  intro i
  let e : Base := EuclideanSpace.basisFun (Fin 3) ℝ i
  have he : e ∈ closedBall (0:Base) 1 := by
    rw [mem_closedBall,dist_zero_right]
    exact le_of_eq ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i)
  calc
    |L e| = |(f e-c)-(f e-c-L e)| := by congr 1; ring
    _ ≤ |f e-c|+|f e-c-L e| := abs_sub _ _
    _ ≤ (|f e|+|c|)+E := add_le_add (abs_sub _ _) (hfit e he)
    _ ≤ (H+(H+E))+E := add_le_add (add_le_add (hf e he) hc) le_rfl
    _ = _ := by ring

/-- Choose a controlled affine approximation, including at zero affine
distance. A positive cutoff separates the immediate affine exit from the
normalized nonaffine branch; the latter scale has no inverse smaller than
the inverse cutoff. -/
theorem controlled_scale {f : Base → ℝ} (hf : ContinuousOn f (closedBall (0:Base) 1))
    {H b : ℝ} (hH : 0 ≤ H) (hb : 0 < b)
    (hbound : ∀ u ∈ closedBall (0:Base) 1, |f u| ≤ H) :
    ∃ (s c : ℝ) (L : Base →L[ℝ] ℝ), 0 ≤ s ∧ s ≤ H ∧
      (∀ (c' : ℝ) (L' : Base →L[ℝ] ℝ),
        ∃ u ∈ closedBall (0:Base) 1, s ≤ |f u-c'-L' u|) ∧
      (∀ ε:ℝ, s<ε → ∃ (c':ℝ) (L':Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0:Base) 1, |f u-c'-L' u| ≤ ε) ∧
      |c| ≤ 3*(H+b) ∧ (∀ i:Fin 3, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ 6*(H+b)) ∧
      ((s ≤ b ∧ ∀ u ∈ closedBall (0:Base) 1, |f u-c-L u| ≤ 2*b) ∨
       (b < s ∧ ∀ u ∈ closedBall (0:Base) 1, |f u-c-L u| ≤ 2*s)) := by
  obtain ⟨s,hs,hlow,happrox⟩ := exists_affine_distance_scale f hf
  have hsH : s ≤ H := by
    obtain ⟨u,hu,h⟩ := hlow 0 0
    simpa using h.trans (by simpa using hbound u hu)
  by_cases hsb : s ≤ b
  · obtain ⟨c,L,hfit⟩ := happrox (2*b) (by linarith)
    obtain ⟨hc,hL⟩ := approximation_coefficients L hbound hfit
    refine ⟨s,c,L,hs,hsH,hlow,happrox,?_,?_,Or.inl ⟨hsb,hfit⟩⟩
    · linarith
    · intro i
      linarith [hL i]
  · have hbs : b < s := lt_of_not_ge hsb
    obtain ⟨c,L,hfit⟩ := happrox (2*s) (by linarith)
    obtain ⟨hc,hL⟩ := approximation_coefficients L hbound hfit
    refine ⟨s,c,L,hs,hsH,hlow,happrox,?_,?_,Or.inr ⟨hbs,hfit⟩⟩
    · linarith
    · intro i
      linarith [hL i]

/-- A sufficiently affine branch already has a degree-one certificate,
with exact unit hidden derivative and zero hidden curvature. -/
theorem affine_certificate (f : Base → ℝ) (c : ℝ) (L : Base →L[ℝ] ℝ)
    {H E : ℝ} (hH : 1 ≤ H) (hc : |c| ≤ H)
    (hL : ∀ i:Fin 3, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H)
    (hfit : ∀ u ∈ closedBall (0:Base) 1, |f u-c-L u| ≤ E) :
    ∃ Q:Poly, Q.totalDegree ≤ 2 ∧ (∀ m, |Q.coeff m| ≤ 5*H) ∧
      ∀ u ∈ closedBall (0:Base) 1, ∀ w:ℝ,
        |ev Q u w| ≤ E+|w-f u| ∧ ev (pderiv (3:Fin 4) Q) u w = 1 ∧
        ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w = 0 := by
  let ell : Fin 3 → ℝ := fun i => L (EuclideanSpace.basisFun (Fin 3) ℝ i)
  refine ⟨height c ell,(degree_height c ell).trans (by norm_num),?_,?_⟩
  · intro m
    exact (Submission.Lib.K4ChartLifting.abs_coeff_le_coeffL1 _ _).trans
      (mass_height hH ell hc hL)
  · intro u hu w
    have he : ev (height c ell) u w = w-c-L u := by
      change eval (Fin.snoc (fun i => u i) w) (height c ell) = _
      rw [eval_height,Submission.Obl.k4_seven_direction_local_degree_restoration.linear_coordinates]
    refine ⟨?_,?_,?_⟩
    · rw [he]
      calc |w-c-L u| = |(f u-c-L u)+(w-f u)| := by congr 1; ring
        _ ≤ |f u-c-L u|+|w-f u| := abs_add_le _ _
        _ ≤ E+|w-f u| := add_le_add (hfit u hu) le_rfl
    · simp [pderiv_height,ev]
    · simp [pderiv_height,ev]

end AffineExit

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
