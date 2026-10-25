import Mathlib
import Submission.Lib.K4PolynomialPotential.Coordinate

/-!
Adapted from: here:o062
Original proof: Submission/Obl/k4_scalar_mesh_projection/Potential.lean.

Polynomial potentials for scalar row fields. Coordinate primitives give an
explicit potential whose gradient error is the primitive of the scalar curl.
-/

namespace Submission.Lib.K4PolynomialPotential

open MvPolynomial

noncomputable def polynomialPrimitive {σ : Type*} (i : σ) :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ := by
  classical
  let L := Finsupp.linearCombination ℝ (fun d : σ →₀ ℕ =>
    monomial (d + Finsupp.single i 1) (((d i : ℝ) + 1)⁻¹))
  refine { toFun := fun P => L P.coeff, map_add' := ?_, map_smul' := ?_ }
  · intro P Q
    exact L.map_add P.coeff Q.coeff
  · intro c P
    exact L.map_smul c P.coeff

theorem polynomialPrimitive_monomial {σ : Type*} (i : σ) (d : σ →₀ ℕ) (c : ℝ) :
    polynomialPrimitive i (monomial d c) =
      monomial (d + Finsupp.single i 1) (c / ((d i : ℝ) + 1)) := by
  classical
  change (Finsupp.linearCombination ℝ (fun d : σ →₀ ℕ =>
    monomial (d + Finsupp.single i 1) (((d i : ℝ) + 1)⁻¹))) (Finsupp.single d c) = _
  rw [Finsupp.linearCombination_single, smul_monomial]
  simp only [smul_eq_mul, div_eq_mul_inv]

theorem pderiv_polynomialPrimitive {σ : Type*} (i : σ) (P : MvPolynomial σ ℝ) :
    pderiv i (polynomialPrimitive i P) = P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial d c =>
    rw [polynomialPrimitive_monomial, pderiv_monomial]
    simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.cast_add, Nat.cast_one]
    congr 1
    exact div_mul_cancel₀ _ (by positivity : (d i : ℝ) + 1 ≠ 0)

theorem pderiv_polynomialPrimitive_of_ne {σ : Type*} {i j : σ}
    (P : MvPolynomial σ ℝ) (hji : j ≠ i) :
    pderiv j (polynomialPrimitive i P) = polynomialPrimitive i (pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial d c =>
    have hexp : (d + Finsupp.single i 1) - Finsupp.single j 1 =
        (d - Finsupp.single j 1) + Finsupp.single i 1 := by
      ext k
      change (d k + (Finsupp.single i 1) k) - (Finsupp.single j 1) k =
        (d k - (Finsupp.single j 1) k) + (Finsupp.single i 1) k
      by_cases hki : k = i
      · subst k
        simp [hji, hji.symm]
      · simp [hki, Ne.symm hki]
    simp only [polynomialPrimitive_monomial, pderiv_monomial]
    rw [hexp]
    congr 1
    simp [Finsupp.add_apply, Finsupp.single_apply, hji, hji.symm, div_eq_mul_inv]
    ring

theorem eval_polynomialPrimitive_zero {σ : Type*} [Fintype σ]
    (x : σ → ℝ) (i : σ) (P : MvPolynomial σ ℝ) (hxi : x i = 0) :
    MvPolynomial.eval x (polynomialPrimitive i P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | monomial d c =>
    rw [polynomialPrimitive_monomial, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun j => by simp)]
    have hzero : (∏ j : σ, x j ^ ((d + Finsupp.single i 1 : σ →₀ ℕ) j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hxi, Finsupp.add_apply]
    rw [hzero, mul_zero]

theorem polynomialPrimitive_totalDegree {σ : Type*} (i : σ)
    (P : MvPolynomial σ ℝ) :
    (polynomialPrimitive i P).totalDegree ≤ P.totalDegree + 1 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [polynomialPrimitive_monomial]
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have hsum : (d + Finsupp.single i 1).sum (fun _ e => e) =
      d.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  change (d + Finsupp.single i 1).sum (fun _ e => e) ≤ P.totalDegree + 1
  rw [hsum]
  exact Nat.add_le_add_right (MvPolynomial.le_totalDegree hd) 1

/-- The mean-value estimate along a polynomial coordinate line. -/
theorem polynomial_coordinate_eval_sub_bound {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) {E : ℝ}
    (hxi : x i ∈ Set.Icc (-1 : ℝ) 1)
    (hbound : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval (Function.update x i u) (pderiv i P)| ≤ E) :
    |MvPolynomial.eval x P - MvPolynomial.eval (Function.update x i 0) P| ≤
      E * |x i| := by
  let q := Submission.Lib.K4PolynomialPotential.coordinatePolynomialHom x i P
  have hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖q.derivative.eval u‖ ≤ E := by
    intro u hu
    dsimp only [q]
    rw [Submission.Lib.K4PolynomialPotential.derivative_coordinatePolynomialHom,
      Submission.Lib.K4PolynomialPotential.eval_coordinatePolynomialHom]
    simpa only [Real.norm_eq_abs] using hbound u hu
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (-1 : ℝ) 1) (x := 0) (y := x i)
    (f := fun u => q.eval u) (f' := fun u => q.derivative.eval u)
    (fun u hu => (q.hasDerivAt u).hasDerivWithinAt) hb
    (convex_Icc _ _) (by norm_num) hxi
  simpa only [q, Submission.Lib.K4PolynomialPotential.eval_coordinatePolynomialHom,
    Function.update_eq_self, Real.norm_eq_abs, sub_zero] using h

/-- Coordinate integration costs only the length of that coordinate. -/
theorem polynomialPrimitive_eval_bound {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) {E : ℝ}
    (hxi : x i ∈ Set.Icc (-1 : ℝ) 1)
    (hbound : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval (Function.update x i u) P| ≤ E) :
    |MvPolynomial.eval x (polynomialPrimitive i P)| ≤ E * |x i| := by
  have h := polynomial_coordinate_eval_sub_bound (polynomialPrimitive i P) x i hxi (by
    rw [pderiv_polynomialPrimitive]
    exact hbound)
  rw [eval_polynomialPrimitive_zero (Function.update x i 0) i P (by simp), sub_zero] at h
  exact h

theorem update_mem_unit_box {σ : Type*} [DecidableEq σ] {x : σ → ℝ}
    (hx : x ∈ Set.Icc (-1 : σ → ℝ) 1) (i : σ) (u : ℝ)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    Function.update x i u ∈ Set.Icc (-1 : σ → ℝ) 1 := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hu.1
    · simpa [Function.update_of_ne hji] using hx.1 j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hu.2
    · simpa [Function.update_of_ne hji] using hx.2 j

/-- Integrate the first row on the zero spatial axis and the second row in
the spatial coordinate. The subtraction implements the axis restriction. -/
noncomputable def polynomialPotential (A B : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  polynomialPrimitive 0 A -
    polynomialPrimitive 0 (polynomialPrimitive 1 (pderiv 1 A)) +
    polynomialPrimitive 1 B

theorem polynomialPotential_spatial (A B : MvPolynomial (Fin 2) ℝ) :
    pderiv 1 (polynomialPotential A B) = B := by
  rw [polynomialPotential, map_add, map_sub,
    pderiv_polynomialPrimitive_of_ne A (by decide : (1 : Fin 2) ≠ 0),
    pderiv_polynomialPrimitive_of_ne (polynomialPrimitive 1 (pderiv 1 A))
      (by decide : (1 : Fin 2) ≠ 0),
    pderiv_polynomialPrimitive, pderiv_polynomialPrimitive]
  simp

theorem polynomialPotential_time_error (A B : MvPolynomial (Fin 2) ℝ) :
    pderiv 0 (polynomialPotential A B) - A =
      polynomialPrimitive 1 (pderiv 0 B - pderiv 1 A) := by
  rw [polynomialPotential, map_add, map_sub, pderiv_polynomialPrimitive,
    pderiv_polynomialPrimitive,
    pderiv_polynomialPrimitive_of_ne B (by decide : (0 : Fin 2) ≠ 1), map_sub]
  ring

theorem polynomialPotential_totalDegree (A B : MvPolynomial (Fin 2) ℝ)
    {D : ℕ} (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D) :
    (polynomialPotential A B).totalDegree ≤ D + 2 := by
  have h0 := polynomialPrimitive_totalDegree (0 : Fin 2) A
  have h1 := polynomialPrimitive_totalDegree (1 : Fin 2) B
  have hd := Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le A (1 : Fin 2)
  have h10 := polynomialPrimitive_totalDegree (1 : Fin 2) (pderiv 1 A)
  have h01 := polynomialPrimitive_totalDegree (0 : Fin 2)
    (polynomialPrimitive 1 (pderiv 1 A))
  unfold polynomialPotential
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le <;> omega
  · omega

theorem polynomialPotential_eval_zero (A B : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial.eval (0 : Fin 2 → ℝ) (polynomialPotential A B) = 0 := by
  rw [polynomialPotential, map_add, map_sub,
    eval_polynomialPrimitive_zero (0 : Fin 2 → ℝ) 0 A (by rfl),
    eval_polynomialPrimitive_zero (0 : Fin 2 → ℝ) 0
      (polynomialPrimitive 1 (pderiv 1 A)) (by rfl),
    eval_polynomialPrimitive_zero (0 : Fin 2 → ℝ) 1 B (by rfl)]
  simp

theorem polynomialPotential_time_error_bound (A B : MvPolynomial (Fin 2) ℝ)
    {E : ℝ} (hcurl : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1,
      |MvPolynomial.eval z (pderiv 0 B - pderiv 1 A)| ≤ E)
    (x : Fin 2 → ℝ) (hx : x ∈ Set.Icc (-1 : Fin 2 → ℝ) 1) :
    |MvPolynomial.eval x (pderiv 0 (polynomialPotential A B)) - MvPolynomial.eval x A| ≤
      E * |x 1| := by
  rw [← map_sub, polynomialPotential_time_error]
  exact polynomialPrimitive_eval_bound _ x 1 ⟨hx.1 1, hx.2 1⟩
    (fun u hu => hcurl _ (update_mem_unit_box hx 1 u hu))

/-- The potential has a degree-independent size bound on the same real box. -/
theorem polynomialPotential_eval_bound (A B : MvPolynomial (Fin 2) ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1, |MvPolynomial.eval z A| ≤ K)
    (hB : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1, |MvPolynomial.eval z B| ≤ K)
    (x : Fin 2 → ℝ) (hx : x ∈ Set.Icc (-1 : Fin 2 → ℝ) 1) :
    |MvPolynomial.eval x (polynomialPotential A B)| ≤ 2 * K := by
  let vbase : Fin 2 → ℝ := Function.update x 1 0
  have hbasebox : vbase ∈ Set.Icc (-1 : Fin 2 → ℝ) 1 :=
    update_mem_unit_box hx 1 0 (by norm_num)
  have haxis : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval (Function.update vbase 0 u)
        (pderiv 0 (polynomialPotential A B))| ≤ K := by
    intro u hu
    let z : Fin 2 → ℝ := Function.update vbase 0 u
    have hz1 : z 1 = 0 := by simp [z, vbase]
    have herr := congrArg (fun P : MvPolynomial (Fin 2) ℝ => MvPolynomial.eval z P)
      (polynomialPotential_time_error A B)
    rw [map_sub, eval_polynomialPrimitive_zero z 1 _ hz1] at herr
    rw [sub_eq_zero.mp herr]
    exact hA z (update_mem_unit_box hbasebox 0 u hu)
  have hbase := polynomial_coordinate_eval_sub_bound (polynomialPotential A B)
    vbase 0 ⟨hbasebox.1 0, hbasebox.2 0⟩ haxis
  have hzero : Function.update vbase 0 0 = (0 : Fin 2 → ℝ) := by
    funext j
    fin_cases j <;> simp [vbase]
  rw [hzero, polynomialPotential_eval_zero, sub_zero] at hbase
  have hspatial := polynomial_coordinate_eval_sub_bound (polynomialPotential A B)
    x 1 ⟨hx.1 1, hx.2 1⟩ (by
      rw [polynomialPotential_spatial]
      exact fun u hu => hB _ (update_mem_unit_box hx 1 u hu))
  have hx1 : |x 1| ≤ 1 := abs_le.mpr ⟨hx.1 1, hx.2 1⟩
  have hb0 : |vbase 0| ≤ 1 := abs_le.mpr ⟨hbasebox.1 0, hbasebox.2 0⟩
  calc
    |MvPolynomial.eval x (polynomialPotential A B)| =
        |(MvPolynomial.eval x (polynomialPotential A B) -
          MvPolynomial.eval vbase (polynomialPotential A B)) +
          MvPolynomial.eval vbase (polynomialPotential A B)| := by congr 1 <;> ring
    _ ≤ |MvPolynomial.eval x (polynomialPotential A B) -
          MvPolynomial.eval vbase (polynomialPotential A B)| +
          |MvPolynomial.eval vbase (polynomialPotential A B)| := abs_add_le _ _
    _ ≤ K * |x 1| + K * |vbase 0| := add_le_add hspatial hbase
    _ ≤ 2 * K := by
      have h1 := mul_le_mul_of_nonneg_left hx1 hK
      have h0 := mul_le_mul_of_nonneg_left hb0 hK
      linarith

/-- Quantitative polynomial Poincare construction for the two scalar rows. -/
theorem exists_bounded_polynomial_potential (A B : MvPolynomial (Fin 2) ℝ)
    {D : ℕ} (hdegA : A.totalDegree ≤ D) (hdegB : B.totalDegree ≤ D)
    {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hA : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1, |MvPolynomial.eval z A| ≤ K)
    (hB : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1, |MvPolynomial.eval z B| ≤ K)
    (hcurl : ∀ z ∈ Set.Icc (-1 : Fin 2 → ℝ) 1,
      |MvPolynomial.eval z (pderiv 0 B - pderiv 1 A)| ≤ E) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ D + 2 ∧ pderiv 1 P = B ∧
      MvPolynomial.eval (0 : Fin 2 → ℝ) P = 0 ∧
      ∀ x ∈ Set.Icc (-1 : Fin 2 → ℝ) 1, |MvPolynomial.eval x P| ≤ 2 * K ∧
        |MvPolynomial.eval x (pderiv 0 P) - MvPolynomial.eval x A| ≤ E := by
  refine ⟨polynomialPotential A B, polynomialPotential_totalDegree A B hdegA hdegB,
    polynomialPotential_spatial A B, polynomialPotential_eval_zero A B, ?_⟩
  intro x hx
  refine ⟨polynomialPotential_eval_bound A B hK hA hB x hx,
    (polynomialPotential_time_error_bound A B hcurl x hx).trans ?_⟩
  calc
    E * |x 1| ≤ E * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hx.1 1, hx.2 1⟩) hE
    _ = E := mul_one _

theorem exists_polynomial_potential_of_zero_curl (A B : MvPolynomial (Fin 2) ℝ)
    (hcurl : pderiv 0 B = pderiv 1 A) :
    ∃ P : MvPolynomial (Fin 2) ℝ, pderiv 0 P = A ∧ pderiv 1 P = B := by
  refine ⟨polynomialPotential A B, ?_, polynomialPotential_spatial A B⟩
  have h := polynomialPotential_time_error A B
  rw [hcurl, sub_self, map_zero] at h
  exact sub_eq_zero.mp h

end Submission.Lib.K4PolynomialPotential
