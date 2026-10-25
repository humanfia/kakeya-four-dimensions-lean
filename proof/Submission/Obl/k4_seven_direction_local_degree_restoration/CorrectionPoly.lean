import Submission.Obl.k4_seven_direction_local_degree_restoration.Affine
import Submission.Obl.k4_seven_direction_local_degree_restoration.GraphTaylor
import Submission.Obl.k4_seven_direction_local_degree_restoration.Hidden

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open MvPolynomial

noncomputable def baseLinear (L : Base →L[ℝ] ℝ) : Poly :=
  affinePoly 0 (Fin.snoc (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i)) 0)

noncomputable def hiddenAffine (f : Base → ℝ) (s : ℝ) : Poly :=
  affinePoly (-f 0 / s) (Fin.snoc
    (fun i : Fin 3 => -fderiv ℝ f 0 (EuclideanSpace.basisFun (Fin 3) ℝ i) / s) s⁻¹)

noncomputable def baseTaylor (R : Base → ℝ) : Poly := X 3 - quadraticTaylorGraph R

noncomputable def correctedPolynomial (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) : Poly :=
  S - C a * (baseTaylor R + hiddenAffine f s * baseLinear L + C lam * (hiddenAffine f s) ^ 2)

lemma baseLinear_pderiv (L : Base →L[ℝ] ℝ) : pderiv (3 : Fin 4) (baseLinear L) = 0 := by
  rw [baseLinear, affinePoly_pderiv]
  change C ((Fin.snoc (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i)) 0 : Fin 4 → ℝ) (Fin.last 3)) = 0
  rw [Fin.snoc_last, map_zero]


lemma hiddenAffine_pderiv (f : Base → ℝ) (s : ℝ) :
    pderiv (3 : Fin 4) (hiddenAffine f s) = C s⁻¹ := by
  rw [hiddenAffine, affinePoly_pderiv]
  change C ((Fin.snoc
    (fun i : Fin 3 => -fderiv ℝ f 0 (EuclideanSpace.basisFun (Fin 3) ℝ i) / s) s⁻¹ : Fin 4 → ℝ) (Fin.last 3)) = C s⁻¹
  rw [Fin.snoc_last]


lemma baseTaylor_pderiv (R : Base → ℝ) : pderiv (3 : Fin 4) (baseTaylor R) = 0 := by
  simp [baseTaylor, quadraticTaylorGraph, quadraticGraph_pderiv]

lemma baseLinear_eval (L : Base →L[ℝ] ℝ) (u : Base) (w : ℝ) :
    evalAt (baseLinear L) u w = L u := by
  have hcoord (i : Fin 3) : (![u 0, u 1, u 2, w] : Fin 4 → ℝ) i.castSucc = u i := by
    fin_cases i <;> rfl
  rw [evalAt, baseLinear, affinePoly_eval, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero, zero_add, hcoord]
  exact linear_coordinates L u

lemma hiddenAffine_eval (f : Base → ℝ) (s : ℝ) (u : Base) (w : ℝ) :
    evalAt (hiddenAffine f s) u w = (w - f 0 - fderiv ℝ f 0 u) / s := by
  have hcoord (i : Fin 3) : (![u 0, u 1, u 2, w] : Fin 4 → ℝ) i.castSucc = u i := by
    fin_cases i <;> rfl
  rw [evalAt, hiddenAffine, affinePoly_eval, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hcoord]
  have hsum : (∑ i : Fin 3,
      -fderiv ℝ f 0 (EuclideanSpace.basisFun (Fin 3) ℝ i) / s * u i) =
      -fderiv ℝ f 0 u / s := by
    rw [← linear_coordinates (fderiv ℝ f 0) u]
    simp [div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [hsum]
  have hlast : (![u 0, u 1, u 2, w] : Fin 4 → ℝ) (Fin.last 3) = w := rfl
  rw [hlast]
  simp only [div_eq_mul_inv]
  ring

lemma baseTaylor_eval (R : Base → ℝ) (u : Base) (w : ℝ) :
    evalAt (baseTaylor R) u w = R 0 + fderiv ℝ R 0 u +
      iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 := by
  rw [evalAt, baseTaylor, map_sub, eval_X, quadraticTaylorGraph_eval]
  simp

lemma correctedPolynomial_totalDegree (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) (hS : S.totalDegree ≤ 2) :
    (correctedPolynomial S f R a s L lam).totalDegree ≤ 2 := by
  have hH : (hiddenAffine f s).totalDegree ≤ 1 := affinePoly_totalDegree _ _
  have hL : (baseLinear L).totalDegree ≤ 1 := affinePoly_totalDegree _ _
  have hT : (baseTaylor R).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    exact quadraticGraph_totalDegree _ _ _
  have hHL : (hiddenAffine f s * baseLinear L).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by omega)
  have hHH : (C lam * hiddenAffine f s ^ 2).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_pow (hiddenAffine f s) 2
    simp only [totalDegree_C, zero_add]
    omega
  unfold correctedPolynomial
  refine (totalDegree_sub _ _).trans (max_le hS ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le hT hHL)) hHH)

lemma correctedPolynomial_pderiv (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) :
    pderiv (3 : Fin 4) (correctedPolynomial S f R a s L lam) = pderiv (3 : Fin 4) S -
      C (a / s) * (baseLinear L + C (2 * lam) * hiddenAffine f s) := by
  have hC2 : (C (2 : ℝ) : Poly) = 2 := C_eq_coe_nat 2
  simp [correctedPolynomial, baseTaylor_pderiv,
    hiddenAffine_pderiv, baseLinear_pderiv, pow_two, div_eq_mul_inv, map_mul, hC2]
  ring

lemma correctedPolynomial_pderiv_two (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (correctedPolynomial S f R a s L lam)) =
      pderiv (3 : Fin 4) (pderiv (3 : Fin 4) S) - C (2 * a * lam / s ^ 2) := by
  rw [correctedPolynomial_pderiv]
  simp only [map_sub, pderiv_C_mul, map_add, baseLinear_pderiv,
    hiddenAffine_pderiv, zero_add]
  rw [← map_mul, ← map_mul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

lemma correctedPolynomial_eval (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) (u : Base) (w : ℝ) :
    evalAt (correctedPolynomial S f R a s L lam) u w =
      evalAt S u w - a * (evalAt (baseTaylor R) u w +
        evalAt (hiddenAffine f s) u w * L u + lam * (evalAt (hiddenAffine f s) u w) ^ 2) := by
  unfold correctedPolynomial
  simp only [evalAt, map_sub, map_mul, map_add, map_pow, eval_C]
  change evalAt S u w - a * (evalAt (baseTaylor R) u w +
    evalAt (hiddenAffine f s) u w * evalAt (baseLinear L) u w +
      lam * evalAt (hiddenAffine f s) u w ^ 2) = _
  rw [baseLinear_eval]
  rfl

lemma correctedPolynomial_pderiv_eval (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) (u : Base) (w : ℝ) :
    evalAt (pderiv (3 : Fin 4) (correctedPolynomial S f R a s L lam)) u w =
      evalAt (pderiv (3 : Fin 4) S) u w - a / s *
        (L u + 2 * lam * evalAt (hiddenAffine f s) u w) := by
  rw [correctedPolynomial_pderiv]
  simp only [evalAt, map_sub, map_mul, map_add, eval_C]
  change evalAt (pderiv (3 : Fin 4) S) u w - a / s *
    (evalAt (baseLinear L) u w + 2 * lam * evalAt (hiddenAffine f s) u w) = _
  rw [baseLinear_eval]
  rfl

lemma correctedPolynomial_pderiv_two_eval (S : Poly) (f R : Base → ℝ) (a s : ℝ)
    (L : Base →L[ℝ] ℝ) (lam : ℝ) (u : Base) (w : ℝ) :
    evalAt (pderiv (3 : Fin 4) (pderiv (3 : Fin 4)
      (correctedPolynomial S f R a s L lam))) u w =
      evalAt (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) S)) u w - 2 * a * lam / s ^ 2 := by
  rw [correctedPolynomial_pderiv_two]
  simp only [evalAt, map_sub, eval_C]

lemma linear_basis_bound {L : Base →L[ℝ] ℝ} {M : ℝ} (hL : ‖L‖ ≤ M) (i : Fin 3) :
    |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ M := by
  have h := L.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)
  simpa [EuclideanSpace.basisFun_apply, Real.norm_eq_abs] using
    h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

lemma baseLinear_coeff_bound {L : Base →L[ℝ] ℝ} {M : ℝ} (hM : 0 ≤ M) (hL : ‖L‖ ≤ M)
    (e : Fin 4 →₀ ℕ) : |(baseLinear L).coeff e| ≤ 5 * M := by
  refine affinePoly_coeff_le hM (by simpa using hM) ?_ e
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change |(Fin.snoc (fun j : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0 : Fin 4 → ℝ) (Fin.last 3)| ≤ M
    rw [Fin.snoc_last]
    simpa using hM
  · simpa using linear_basis_bound hL j

lemma hiddenAffine_input_bounds {f : Base → ℝ} {s Z : ℝ} (hs : 0 < s) (hZ : 2 ≤ Z)
    (hsinv : s⁻¹ ≤ Z) (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z) :
    |-f 0 / s| ≤ Z ^ 2 ∧
      ∀ i : Fin 4, |(Fin.snoc
        (fun j : Fin 3 => -fderiv ℝ f 0 (EuclideanSpace.basisFun (Fin 3) ℝ j) / s) s⁻¹ : Fin 4 → ℝ) i| ≤ Z ^ 2 := by
  have hZ0 : 0 ≤ Z := by linarith
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have hbound {x : ℝ} (hx : |x| ≤ Z) : |-x / s| ≤ Z ^ 2 := by
    rw [div_eq_mul_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hs)]
    exact (mul_le_mul hx hsinv (inv_nonneg.mpr hs.le) hZ0).trans_eq (by ring)
  refine ⟨hbound h0, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, abs_of_pos (inv_pos.mpr hs)]
    exact hsinv.trans hZZ
  · simpa using hbound (linear_basis_bound h1 j)

lemma hiddenAffine_coeff_bound {f : Base → ℝ} {s Z : ℝ} (hs : 0 < s) (hZ : 2 ≤ Z)
    (hsinv : s⁻¹ ≤ Z) (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (e : Fin 4 →₀ ℕ) : |(hiddenAffine f s).coeff e| ≤ 5 * Z ^ 2 := by
  obtain ⟨hc, hl⟩ := hiddenAffine_input_bounds hs hZ hsinv h0 h1
  exact affinePoly_coeff_le (sq_nonneg Z) hc hl e

lemma hiddenAffine_mul_coeff_bound {f : Base → ℝ} {s Z B : ℝ} {P : Poly}
    (hs : 0 < s) (hZ : 2 ≤ Z) (hsinv : s⁻¹ ≤ Z)
    (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (hB : 0 ≤ B) (hP : ∀ e, |P.coeff e| ≤ B) (e : Fin 4 →₀ ℕ) :
    |(hiddenAffine f s * P).coeff e| ≤ 5 * Z ^ 2 * B := by
  obtain ⟨hc, hl⟩ := hiddenAffine_input_bounds hs hZ hsinv h0 h1
  exact affinePoly_mul_coeff_le (sq_nonneg Z) hB hc hl hP e

lemma correctedPolynomial_coeff_bound (K : ℕ) (hK : 1 ≤ K)
    {S : Poly} {f R : Base → ℝ} {a s Z : ℝ} {L : Base →L[ℝ] ℝ} {lam : ℝ}
    (hZ : 2 ≤ Z) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hs : 0 < s) (hsinv : s⁻¹ ≤ Z)
    (hS : ∀ e, |S.coeff e| ≤ Z)
    (hf0 : |f 0| ≤ Z) (hf1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (hR0 : |R 0| ≤ Z) (hR1 : ‖fderiv ℝ R 0‖ ≤ Z) (hR2 : ‖iteratedFDeriv ℝ 2 R 0‖ ≤ Z)
    (hL : ‖L‖ ≤ Z ^ K) (hlam : |lam| ≤ Z ^ K) (e : Fin 4 →₀ ℕ) :
    |(correctedPolynomial S f R a s L lam).coeff e| ≤ Z ^ (K + 10) := by
  have hZ0 : 0 ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hM0 : 0 ≤ Z ^ (K + 4) := pow_nonneg hZ0 _
  have hmono2 : Z ^ (K + 2) ≤ Z ^ (K + 4) := pow_le_pow_right₀ hZ1 (by omega)
  have hmono5 : Z ^ 5 ≤ Z ^ (K + 4) := pow_le_pow_right₀ hZ1 (by omega)
  have hmonoZ : Z ≤ Z ^ (K + 4) := by
    simpa using pow_le_pow_right₀ hZ1 (by omega : 1 ≤ K + 4)
  have hmono1 : 1 ≤ Z ^ (K + 4) := one_le_pow₀ hZ1
  have hT : |(baseTaylor R).coeff e| ≤ 1 + Z ^ 5 := by
    unfold baseTaylor
    rw [coeff_sub]
    exact (abs_sub _ _).trans (add_le_add (abs_coeff_X_le_one 3 e)
      (quadraticTaylorGraph_coeff_le hZ hR0 hR1 hR2 e))
  have hLcoeff := baseLinear_coeff_bound (pow_nonneg hZ0 K) hL
  have hHL : |(hiddenAffine f s * baseLinear L).coeff e| ≤ 25 * Z ^ (K + 2) := by
    refine (hiddenAffine_mul_coeff_bound hs hZ hsinv hf0 hf1 (by positivity) hLcoeff e).trans_eq ?_
    rw [pow_add]
    ring
  have hHH : ∀ e, |((hiddenAffine f s) ^ 2).coeff e| ≤ 25 * Z ^ 4 := by
    intro e
    rw [pow_two]
    refine (hiddenAffine_mul_coeff_bound hs hZ hsinv hf0 hf1 (by positivity)
      (hiddenAffine_coeff_bound hs hZ hsinv hf0 hf1) e).trans_eq ?_
    ring
  have hlamHH : |(C lam * (hiddenAffine f s) ^ 2).coeff e| ≤ 25 * Z ^ (K + 4) := by
    rw [coeff_C_mul, abs_mul]
    refine (mul_le_mul hlam (hHH e) (abs_nonneg _) (pow_nonneg hZ0 K)).trans_eq ?_
    rw [pow_add]
    ring
  have hcorr : |(baseTaylor R + hiddenAffine f s * baseLinear L + C lam * (hiddenAffine f s) ^ 2).coeff e| ≤
      52 * Z ^ (K + 4) := by
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    have h := abs_add_le ((baseTaylor R).coeff e + (hiddenAffine f s * baseLinear L).coeff e)
      ((C lam * hiddenAffine f s ^ 2).coeff e)
    have h' := abs_add_le ((baseTaylor R).coeff e) ((hiddenAffine f s * baseLinear L).coeff e)
    linarith
  have hQ : |(correctedPolynomial S f R a s L lam).coeff e| ≤ 53 * Z ^ (K + 4) := by
    unfold correctedPolynomial
    rw [coeff_sub, coeff_C_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ha]
    have hscale : a * |(baseTaylor R + hiddenAffine f s * baseLinear L + C lam * hiddenAffine f s ^ 2).coeff e| ≤
        52 * Z ^ (K + 4) := by
      exact (mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)).trans (by simpa using hcorr)
    linarith [hS e]
  have h53 : (53 : ℝ) ≤ Z ^ 6 := by
    calc (53 : ℝ) ≤ 2 ^ 6 := by norm_num
         _ ≤ Z ^ 6 := pow_le_pow_left₀ (by norm_num) hZ 6
  refine hQ.trans ((mul_le_mul_of_nonneg_right h53 hM0).trans_eq ?_)
  rw [← pow_add]
  congr 1
  omega

end Submission.Obl.k4_seven_direction_local_degree_restoration
