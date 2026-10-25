import Submission.Obl.k4_eligibility_sign_description.QuadraticSigns

namespace Submission.Obl.k4_eligibility_sign_description

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev Poly := MvPolynomial (Fin 3 ⊕ Fin 3) ℝ

def coords (z : E3 × E3) : Fin 3 ⊕ Fin 3 → ℝ :=
  Sum.elim (fun i => z.1 i) (fun i => z.2 i)

def sVar (i : Fin 3) : Poly := MvPolynomial.X (Sum.inl i)
def yVar (i : Fin 3) : Poly := MvPolynomial.X (Sum.inr i)

@[simp] lemma eval_sVar (z : E3 × E3) (i : Fin 3) :
    MvPolynomial.eval (coords z) (sVar i) = z.1 i := by simp [sVar, coords]
@[simp] lemma eval_yVar (z : E3 × E3) (i : Fin 3) :
    MvPolynomial.eval (coords z) (yVar i) = z.2 i := by simp [yVar, coords]

lemma eval_aeval_real {σ τ : Type*} (p : MvPolynomial τ ℝ)
    (f : τ → MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (MvPolynomial.aeval f p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) p := by
  simpa only [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq, Function.comp_def] using
    (MvPolynomial.eval_assoc f x p).symm

lemma Quadratic.mv_line {σ : Type*} (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ 2) (a b : σ → ℝ) :
    Quadratic (fun t => MvPolynomial.eval (fun i => a i + t * b i) p) := by
  let f : σ → Polynomial ℝ := fun i => Polynomial.C (b i) * Polynomial.X + Polynomial.C (a i)
  have hdeg : (MvPolynomial.aeval f p).natDegree ≤ 2 := by
    simpa using MvPolynomial.aeval_natDegree_le p hp f
      (fun i => Polynomial.natDegree_linear_le)
  have heval : ∀ t, (MvPolynomial.aeval f p).eval t =
      MvPolynomial.eval (fun i => a i + t * b i) p := by
    intro t
    clear hp hdeg
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i ih =>
      simp only [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, ih]
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
  obtain ⟨A, B, C, h⟩ := Quadratic.of_polynomial _ hdeg
  exact ⟨A, B, C, fun t => (heval t).symm.trans (h t)⟩

lemma degree_pderiv_le {σ : Type*} (p : MvPolynomial σ ℝ) (i : σ) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hm' := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hm'
  have hm'' := (mul_ne_zero_iff.mp hm').1
  have h := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hm'')
  have heq : (m + Finsupp.single i 1).sum (fun _ n => n) = m.sum (fun _ n => n) + 1 := by
    simp [Finsupp.sum_add_index']
  rw [heq] at h
  exact (Nat.le_succ _).trans h

def normPoly (r : ℝ) (side : Fin 3 → Fin 3 ⊕ Fin 3) : Poly :=
  MvPolynomial.C (r ^ 2) - ∑ i, MvPolynomial.X (side i) ^ 2

lemma degree_normPoly (r : ℝ) (side : Fin 3 → Fin 3 ⊕ Fin 3) :
    (normPoly r side).totalDegree ≤ 2 := by
  apply degree_sub_le
  · simp only [MvPolynomial.totalDegree_C]; omega
  · apply degree_sum_le
    intro i hi
    simp

lemma norm_le_iff {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (r : ℝ) (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ 0 ≤ r ^ 2 - ∑ i, (x i) ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hx := norm_nonneg x
  constructor <;> intro h <;> nlinarith

lemma SignRep.slope_norm (r : ℝ) (hr : 0 ≤ r) :
    SignRep coords 1 2 (fun z : E3 × E3 => ‖z.1‖ ≤ r) := by
  refine (SignRep.nonneg coords (normPoly r Sum.inl) 2 (degree_normPoly _ _)).congr ?_
  intro z
  simpa [normPoly, coords] using (norm_le_iff z.1 r hr).symm

lemma SignRep.intercept_norm (r : ℝ) (hr : 0 ≤ r) :
    SignRep coords 1 2 (fun z : E3 × E3 => ‖z.2‖ ≤ r) := by
  refine (SignRep.nonneg coords (normPoly r Sum.inr) 2 (degree_normPoly _ _)).congr ?_
  intro z
  simpa [normPoly, coords] using (norm_le_iff z.2 r hr).symm

/-- Restriction to a trajectory at a fixed time, as a polynomial in slope and intercept. -/
def tracePoly (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) : Poly :=
  MvPolynomial.aeval ![MvPolynomial.C t,
    yVar 0 + MvPolynomial.C t * sVar 0,
    yVar 1 + MvPolynomial.C t * sVar 1,
    yVar 2 + MvPolynomial.C t * sVar 2] P

lemma degree_tracePoly (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (tracePoly P t).totalDegree ≤ P.totalDegree := by
  apply degree_aeval_le
  intro i
  fin_cases i
  · change (MvPolynomial.C t : Poly).totalDegree ≤ 1
    simp only [MvPolynomial.totalDegree_C]; omega
  all_goals apply degree_add_le <;>
    first | simp [yVar] | exact (degree_C_mul_le _ _).trans (by simp [sVar])

@[simp] lemma eval_tracePoly (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) (z : E3 × E3) :
    MvPolynomial.eval (coords z) (tracePoly P t) =
      MvPolynomial.eval ![t, (z.2 + t • z.1) 0, (z.2 + t • z.1) 1,
        (z.2 + t • z.1) 2] P := by
  rw [tracePoly, eval_aeval_real]
  apply congrArg (fun f : Fin 4 → ℝ => MvPolynomial.eval f P)
  funext i
  fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]

lemma quadratic_tracePoly (P : MvPolynomial (Fin 4) ℝ) (hp : P.totalDegree ≤ 2)
    (z : E3 × E3) : Quadratic (fun t => MvPolynomial.eval (coords z) (tracePoly P t)) := by
  have h := Quadratic.mv_line P hp ![0, z.2 0, z.2 1, z.2 2] ![1, z.1 0, z.1 1, z.1 2]
  have heq : (fun t => MvPolynomial.eval (coords z) (tracePoly P t)) =
      (fun t => MvPolynomial.eval (fun i =>
        (![0, z.2 0, z.2 1, z.2 2] : Fin 4 → ℝ) i +
          t * (![1, z.1 0, z.1 1, z.1 2] : Fin 4 → ℝ) i) P) := by
    funext t
    rw [eval_tracePoly]
    apply congrArg (fun f : Fin 4 → ℝ => MvPolynomial.eval f P)
    funext i
    fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]
  rw [heq]
  exact h

def transversePoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (t : ℝ) (i : Fin 2) : Poly :=
  ∑ j, MvPolynomial.C (M i j) * (yVar j.castSucc + MvPolynomial.C t * sVar j.castSucc -
    MvPolynomial.C (c j) - MvPolynomial.C (t * u j))

def transverseNormPoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (K t : ℝ) : Poly :=
  MvPolynomial.C (K ^ 2) - ∑ i, transversePoly M c u t i ^ 2

lemma degree_transversePoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (t : ℝ) (i : Fin 2) :
    (transversePoly M c u t i).totalDegree ≤ 1 := by
  apply degree_sum_le
  intro j hj
  apply (degree_C_mul_le _ _).trans
  apply degree_sub_le
  · apply degree_sub_le
    · exact degree_add_le (by simp [yVar]) ((degree_C_mul_le _ _).trans (by simp [sVar]))
    · simp only [MvPolynomial.totalDegree_C]; omega
  · simp only [MvPolynomial.totalDegree_C]; omega

lemma degree_transverseNormPoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (K t : ℝ) :
    (transverseNormPoly M c u K t).totalDegree ≤ 2 := by
  apply degree_sub_le
  · simp only [MvPolynomial.totalDegree_C]; omega
  · apply degree_sum_le
    intro i hi
    exact (MvPolynomial.totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left 2 (degree_transversePoly M c u t i))

lemma eval_transversePoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (t : ℝ)
    (z : E3 × E3) (i : Fin 2) :
    MvPolynomial.eval (coords z) (transversePoly M c u t i) =
      (Matrix.toEuclideanLin M (WithLp.toLp 2
        (fun j : Fin 2 => (z.2 + t • z.1) j.castSucc - c j - t * u j))) i := by
  fin_cases i <;> simp [transversePoly, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, PiLp.add_apply, PiLp.smul_apply]

lemma eval_transverseNormPoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (K t : ℝ)
    (z : E3 × E3) (hK : 0 ≤ K) :
    0 ≤ MvPolynomial.eval (coords z) (transverseNormPoly M c u K t) ↔
      ‖Matrix.toEuclideanLin M (WithLp.toLp 2
        (fun j : Fin 2 => (z.2 + t • z.1) j.castSucc - c j - t * u j))‖ ≤ K := by
  simpa [transverseNormPoly, eval_transversePoly] using
    (norm_le_iff (Matrix.toEuclideanLin M (WithLp.toLp 2
      (fun j : Fin 2 => (z.2 + t • z.1) j.castSucc - c j - t * u j))) K hK).symm

lemma quadratic_transverseNormPoly (M : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (K : ℝ)
    (z : E3 × E3) :
    Quadratic (fun t => MvPolynomial.eval (coords z) (transverseNormPoly M c u K t)) := by
  let a : Fin 2 → ℝ := fun i => ∑ j, M i j * (z.2 j.castSucc - c j)
  let b : Fin 2 → ℝ := fun i => ∑ j, M i j * (z.1 j.castSucc - u j)
  have heval : ∀ t i, MvPolynomial.eval (coords z) (transversePoly M c u t i) = a i + t * b i := by
    intro t i
    simp [transversePoly, a, b, Fin.sum_univ_two]
    ring
  refine ⟨-(b 0 ^ 2 + b 1 ^ 2), -(2 * a 0 * b 0 + 2 * a 1 * b 1),
    K ^ 2 - (a 0 ^ 2 + a 1 ^ 2), ?_⟩
  intro t
  simp [transverseNormPoly, heval, Fin.sum_univ_two]
  ring

end
end Submission.Obl.k4_eligibility_sign_description
