/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/Forms.lean. -/
import Mathlib


/-!
# Multilinear forms on `ℝ³` as homogeneous polynomials

`formPoly M` is the homogeneous polynomial `y ↦ M (y, …, y)` of an `n`-linear form on
`EuclideanSpace ℝ (Fin 3)`. We bound its coefficients by the operator norm, and compute its
first and second coordinate derivatives when `M` is symmetric.
-/

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/- Adapted from root/x0001 K4CubicTests/PolynomialPerturbation.lean via o144/x0488, commit 5ed40f2. -/
/-- The formal coordinate derivatives give the derivative of evaluation along
any coordinate-wise differentiable real curve. -/
theorem hasDerivAt_eval_polynomial_curve (F : MvPolynomial (Fin 3) ℝ)
    (z : ℝ → Fin 3 → ℝ) (z' : Fin 3 → ℝ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (z' i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (z s) F)
      (∑ i : Fin 3, MvPolynomial.eval (z t) (pderiv i F) * z' i) t := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
      simpa only [map_add, add_mul, Finset.sum_add_distrib] using hp.fun_add hq
  | mul_X p j hp =>
      convert hp.fun_mul (hz j) using 1
      · funext s
        simp only [map_mul, eval_X, Pi.mul_apply]
      · simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Fin.sum_univ_three]
        fin_cases j <;> simp [Pi.single_apply] <;> ring



/-- The base space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Standard basis vectors of `E3`. -/
noncomputable def e3 (i : Fin 3) : E3 := EuclideanSpace.single i 1

lemma e3_apply (i j : Fin 3) : (e3 i) j = if j = i then 1 else 0 := by
  simp [e3]

lemma norm_e3 (i : Fin 3) : ‖e3 i‖ = 1 := by
  simp [e3]

lemma eq_sum_e3 (x : E3) : x = ∑ i, x i • e3 i := by
  ext j
  simp [e3, Pi.single_apply]

lemma abs_apply_le_norm (x : E3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- A symmetric multilinear map. -/
def IsSymmML {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → E3), M (m ∘ σ) = M m

/-- Multilinear expansion in the standard basis. -/
lemma multilinear_expand {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) (m : Fin n → E3) :
    M m = ∑ ι : Fin n → Fin 3, (∏ k, m k (ι k)) * M (fun k => e3 (ι k)) := by
  conv_lhs => rw [show m = fun k => ∑ i, m k i • e3 i from funext fun k => eq_sum_e3 (m k)]
  rw [M.map_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [M.map_smul_univ (fun k => m k (ι k)) (fun k => e3 (ι k)), smul_eq_mul]

/-- The operator norm is controlled by the values on standard basis vectors. -/
lemma norm_le_of_basis {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ι : Fin n → Fin 3, |M (fun k => e3 (ι k))| ≤ c) : ‖M‖ ≤ 3 ^ n * c := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [multilinear_expand M m, Real.norm_eq_abs]
  calc |∑ ι : Fin n → Fin 3, (∏ k, m k (ι k)) * M (fun k => e3 (ι k))|
      ≤ ∑ ι : Fin n → Fin 3, |(∏ k, m k (ι k)) * M (fun k => e3 (ι k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ι : Fin n → Fin 3, (∏ k, ‖m k‖) * c := by
        refine Finset.sum_le_sum fun ι _ => ?_
        rw [abs_mul, Finset.abs_prod]
        exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          fun k _ => abs_apply_le_norm _ _) (h ι) (abs_nonneg _) (by positivity)
    _ = 3 ^ n * c * ∏ k, ‖m k‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- A basis value is bounded by the operator norm. -/
lemma abs_basis_le_norm {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) (ι : Fin n → Fin 3) :
    |M (fun k => e3 (ι k))| ≤ ‖M‖ := by
  have h := M.le_opNorm (fun k => e3 (ι k))
  simpa [norm_e3, Real.norm_eq_abs] using h

/-- The homogeneous polynomial `y ↦ M (y, …, y)`. -/
noncomputable def formPoly {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ ι : Fin n → Fin 3, C (M (fun k => e3 (ι k))) * ∏ k, X (ι k)

lemma eval_formPoly {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) (y : Fin 3 → ℝ) :
    eval y (formPoly M) = M (fun _ => WithLp.toLp 2 y) := by
  rw [multilinear_expand M, formPoly, map_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp [map_prod, mul_comm]

lemma formPoly_isHomogeneous {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) : (formPoly M).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro ι _
  have h : (∏ k : Fin n, (X (ι k) : MvPolynomial (Fin 3) ℝ)).IsHomogeneous (∑ _k : Fin n, 1) :=
    IsHomogeneous.prod _ _ _ fun k _ => isHomogeneous_X ℝ (ι k)
  have h' := (isHomogeneous_C (Fin 3) (M (fun k => e3 (ι k)))).mul h
  simpa using h'

lemma prod_X_eq_monomial {n : ℕ} (ι : Fin n → Fin 3) :
    (∏ k, X (ι k) : MvPolynomial (Fin 3) ℝ) = monomial (∑ k, Finsupp.single (ι k) 1) 1 := by
  rw [monomial_sum_one]
  rfl

lemma coeff_formPoly_abs_le {n : ℕ} (M : E3 [×n]→L[ℝ] ℝ) (m : Fin 3 →₀ ℕ) :
    |(formPoly M).coeff m| ≤ 3 ^ n * ‖M‖ := by
  classical
  rw [formPoly, coeff_sum]
  calc |∑ ι : Fin n → Fin 3, (C (M (fun k => e3 (ι k))) * ∏ k, X (ι k)).coeff m|
      ≤ ∑ ι : Fin n → Fin 3, |(C (M (fun k => e3 (ι k))) * ∏ k, X (ι k)).coeff m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ι : Fin n → Fin 3, ‖M‖ := by
        refine Finset.sum_le_sum fun ι _ => ?_
        rw [coeff_C_mul, prod_X_eq_monomial, coeff_monomial, abs_mul]
        have h1 : |(if (∑ k, Finsupp.single (ι k) 1) = m then (1 : ℝ) else 0)| ≤ 1 := by
          split_ifs <;> simp
        calc |M (fun k => e3 (ι k))| * |(if (∑ k, Finsupp.single (ι k) 1) = m then (1 : ℝ) else 0)|
            ≤ ‖M‖ * 1 := mul_le_mul (abs_basis_le_norm M ι) h1 (abs_nonneg _) (norm_nonneg _)
          _ = ‖M‖ := mul_one _
    _ = 3 ^ n * ‖M‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- Moving the `k`-th argument to the front, for a symmetric form. -/
lemma IsSymmML.update_eq_cons {n : ℕ} {M : E3 [×(n + 1)]→L[ℝ] ℝ} (hM : IsSymmML M)
    (a v : E3) (k : Fin (n + 1)) :
    M (Function.update (fun _ => a) k v) = M (Fin.cons v (fun _ => a)) := by
  rw [← hM (Equiv.swap 0 k)]
  congr 1
  funext i
  simp only [Function.comp_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rw [Fin.cons_succ, Function.update_apply, Equiv.swap_apply_def]
    by_cases hik : i.succ = k
    · subst hik
      simp [Fin.succ_ne_zero, (Fin.succ_ne_zero i).symm]
    · simp [hik, Fin.succ_ne_zero]

/-- The first coordinate derivative of `formPoly M` for a symmetric form `M`. -/
lemma eval_pderiv_formPoly {n : ℕ} (M : E3 [×(n + 1)]→L[ℝ] ℝ) (hM : IsSymmML M)
    (j : Fin 3) (y : Fin 3 → ℝ) :
    eval y (pderiv j (formPoly M)) =
      ((n : ℝ) + 1) * M (Fin.cons (e3 j) (fun _ => WithLp.toLp 2 y)) := by
  classical
  set z : ℝ → Fin 3 → ℝ := fun t i => y i + t * ((Pi.single j (1 : ℝ) : Fin 3 → ℝ) i) with hz
  have hzd : ∀ i, HasDerivAt (fun s => z s i) ((Pi.single j (1 : ℝ) : Fin 3 → ℝ) i) 0 := by
    intro i
    have := ((hasDerivAt_id (0 : ℝ)).mul_const
      ((Pi.single j (1 : ℝ) : Fin 3 → ℝ) i)).const_add (y i)
    simpa [hz] using this
  have h1 := hasDerivAt_eval_polynomial_curve (formPoly M) z (Pi.single j 1) 0 hzd
  have hz0 : z 0 = y := by funext i; simp [hz]
  rw [hz0] at h1
  have hsum : (∑ i : Fin 3, eval y (pderiv i (formPoly M)) *
      (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i) =
      eval y (pderiv j (formPoly M)) := by
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  rw [hsum] at h1
  have hcurve : (fun s => eval (z s) (formPoly M)) =
      fun s => M (fun _ => WithLp.toLp 2 y + s • e3 j) := by
    funext s
    rw [eval_formPoly]
    congr 1
  have hc : HasDerivAt (fun s : ℝ => (fun _ : Fin (n + 1) => WithLp.toLp 2 y + s • e3 j))
      (fun _ => e3 j) 0 := by
    rw [hasDerivAt_pi]
    intro _
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e3 j)).const_add (WithLp.toLp 2 y)
  have h2' := (M.hasFDerivAt (fun _ => WithLp.toLp 2 y + (0 : ℝ) • e3 j)).comp_hasDerivAt
    (0 : ℝ) hc
  have h2 : HasDerivAt (fun s : ℝ => M (fun _ => WithLp.toLp 2 y + s • e3 j))
      ((M.linearDeriv fun _ => WithLp.toLp 2 y + (0 : ℝ) • e3 j) fun _ => e3 j) (0 : ℝ) := h2'
  rw [← hcurve] at h2
  have heq := h1.unique h2
  rw [heq]
  simp only [zero_smul, add_zero, ContinuousMultilinearMap.linearDeriv_apply]
  rw [Finset.sum_congr rfl fun k _ => hM.update_eq_cons (WithLp.toLp 2 y) (e3 j) k]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Currying a symmetric form at the front keeps it symmetric. -/
lemma IsSymmML.curryLeft {n : ℕ} {M : E3 [×(n + 1)]→L[ℝ] ℝ} (hM : IsSymmML M) (v : E3) :
    IsSymmML (M.curryLeft v) := by
  intro σ m
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
  have h : (Fin.cons v (m ∘ σ) : Fin (n + 1) → E3) =
      (Fin.cons v m : Fin (n + 1) → E3) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  rw [h, hM]

/-- The coordinate derivative of `formPoly M` as a polynomial, for symmetric `M`. -/
lemma pderiv_formPoly {n : ℕ} (M : E3 [×(n + 1)]→L[ℝ] ℝ) (hM : IsSymmML M) (k : Fin 3) :
    pderiv k (formPoly M) = C ((n : ℝ) + 1) * formPoly (M.curryLeft (e3 k)) := by
  apply MvPolynomial.funext
  intro y
  rw [eval_pderiv_formPoly M hM, map_mul, eval_C, eval_formPoly,
    ContinuousMultilinearMap.curryLeft_apply]

/-- The second coordinate derivatives of `formPoly M`, for symmetric `M`. -/
lemma eval_pderiv_pderiv_formPoly {n : ℕ} (M : E3 [×(n + 2)]→L[ℝ] ℝ) (hM : IsSymmML M)
    (j k : Fin 3) (y : Fin 3 → ℝ) :
    eval y (pderiv j (pderiv k (formPoly M))) =
      ((n : ℝ) + 2) * ((n : ℝ) + 1) *
        M (Fin.cons (e3 k) (Fin.cons (e3 j) (fun _ => WithLp.toLp 2 y))) := by
  rw [pderiv_formPoly M hM k, pderiv_C_mul, map_mul, eval_C,
    eval_pderiv_formPoly _ (hM.curryLeft (e3 k)) j y,
    ContinuousMultilinearMap.curryLeft_apply]
  push_cast
  ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition
