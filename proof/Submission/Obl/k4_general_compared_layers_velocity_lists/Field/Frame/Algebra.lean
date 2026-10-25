-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Algebra; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Mathlib
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Background
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Polynomial facts for the list frame of a common field

* an affine substitution in a polynomial of total degree at most two is a quadratic,
  and a quadratic is recovered from its values at `0, 1/2, 1`;
* the exact transverse Taylor identity of a projected quadratic `G(t, Y)` in `Y`
  (the expansion behind `transA`, `transB`, `transD`);
* a local variation bound for projected quadratics (through the accepted o248
  three-variable bound);
* the floor of a perturbed quotient;
* the quadratic background `C₁(τ, ζ) U + C₃ U²` as a polynomial in the original base
  `(t, Z, Y)`, its evaluation, degree and coefficient budget.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MvPolynomial

noncomputable section

namespace Parent.FieldFrame

/-- An affine substitution in a polynomial of total degree at most two is a quadratic. -/
theorem affine_eval_quadratic {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 2)
    (A B : Fin n → ℝ) : ∃ c : Fin 3 → ℝ, ∀ u : ℝ,
      eval (fun i => A i + u * B i) P = c 0 + c 1 * u + c 2 * u ^ 2 := by
  classical
  set g : Fin n → Polynomial ℝ := fun i => Polynomial.C (A i) + Polynomial.C (B i) * Polynomial.X
    with hg_def
  set Q : Polynomial ℝ := aeval g P with hQ_def
  have hQ : ∀ u, Q.eval u = eval (fun i => A i + u * B i) P := by
    intro u
    have h := congrArg (fun φ : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℝ => φ P)
      (MvPolynomial.comp_aeval (R := ℝ) g (Polynomial.aeval u))
    simp only [AlgHom.comp_apply] at h
    rw [← Polynomial.coe_aeval_eq_eval, hQ_def, h]
    change eval _ P = _
    have hfun : (fun i => (Polynomial.aeval u) (g i)) = fun i => A i + u * B i := by
      funext i
      rw [hg_def]
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.algebraMap_eq,
        Polynomial.C_eq_algebraMap]
      simp
      ring
    rw [hfun]
  have hg : ∀ i, (g i).natDegree ≤ 1 := by
    intro i
    simp only [hg_def]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hdeg : Q.natDegree ≤ 2 := by
    rw [hQ_def]
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    rw [aeval_monomial, Polynomial.algebraMap_eq]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Finsupp.prod]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ d.support, (g i ^ d i).natDegree ≤ ∑ i ∈ d.support, d i := by
          apply Finset.sum_le_sum
          intro i _
          refine Polynomial.natDegree_pow_le.trans ?_
          simpa using Nat.mul_le_mul_left (d i) (hg i)
      _ = d.sum (fun _ e => e) := rfl
      _ ≤ P.totalDegree := le_totalDegree hd
      _ ≤ 2 := hP
  refine ⟨![Q.coeff 0, Q.coeff 1, Q.coeff 2], fun u => ?_⟩
  rw [← hQ, Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]

/-- A quadratic is recovered from its values at `0`, `1/2` and `1`. -/
theorem quadratic_interp {f : ℝ → ℝ} {c0 c1 c2 : ℝ}
    (hf : ∀ u, f u = c0 + c1 * u + c2 * u ^ 2) (u : ℝ) :
    f 0 + u * (4 * f (1 / 2) - f 1 - 3 * f 0) +
      u ^ 2 * (2 * f 1 - 4 * f (1 / 2) + 2 * f 0) = f u := by
  rw [hf 0, hf (1 / 2), hf 1, hf u]
  ring

theorem taylor_monomial (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 ≤ 2) (c t y h : ℝ) :
    eval ![t, y + h] (monomial d c) = eval ![t, y] (monomial d c) +
      h * eval ![t, y] (pderiv 1 (monomial d c)) +
      h ^ 2 / 2 * eval ![0, 0] (pderiv 1 (pderiv 1 (monomial d c))) := by
  simp only [pderiv_monomial, eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  simp
  generalize d 0 = a at hd ⊢
  generalize d 1 = b at hd ⊢
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | (simp; ring) | simp

/-- The exact Taylor identity in the second variable of a quadratic `G(t, Y)`. -/
theorem eval_taylor_Y (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) (t y h : ℝ) :
    eval ![t, y + h] G = eval ![t, y] G + h * eval ![t, y] (pderiv 1 G) +
      h ^ 2 / 2 * eval ![0, 0] (pderiv 1 (pderiv 1 G)) := by
  classical
  have key : ∀ d ∈ G.support, eval ![t, y + h] (monomial d (G.coeff d)) =
      eval ![t, y] (monomial d (G.coeff d)) +
      h * eval ![t, y] (pderiv 1 (monomial d (G.coeff d))) +
      h ^ 2 / 2 * eval ![0, 0] (pderiv 1 (pderiv 1 (monomial d (G.coeff d)))) := by
    intro d hd
    have hdeg : d 0 + d 1 ≤ 2 := by
      have := (le_totalDegree hd).trans hG
      rwa [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
    exact taylor_monomial d hdeg _ t y h
  have hG' := G.as_sum
  calc eval ![t, y + h] G = ∑ d ∈ G.support, eval ![t, y + h] (monomial d (G.coeff d)) := by
        conv_lhs => rw [hG']
        rw [map_sum]
    _ = ∑ d ∈ G.support, (eval ![t, y] (monomial d (G.coeff d)) +
      h * eval ![t, y] (pderiv 1 (monomial d (G.coeff d))) +
      h ^ 2 / 2 * eval ![0, 0] (pderiv 1 (pderiv 1 (monomial d (G.coeff d))))) :=
        Finset.sum_congr rfl key
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        conv_rhs => rw [hG']
        simp only [map_sum]

/-- Local variation of a quadratic in two variables with bounded coefficients
(through the accepted o248 bound in three variables). -/
theorem eval2_variation (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {M R δ : ℝ}
    (hM : ∀ e, |G.coeff e| ≤ M) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i - x i| ≤ δ) :
    |eval y G - eval x G| ≤ 216 * M * R ^ 2 * δ := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set P : MvPolynomial (Fin 3) ℝ := rename Fin.castSucc G with hP
  have hPdeg : P.totalDegree ≤ 2 := (totalDegree_rename_le _ _).trans hG
  have hPM : ∀ e, |P.coeff e| ≤ M := by
    intro e
    by_cases h : ∃ u : Fin 2 →₀ ℕ, u.mapDomain Fin.castSucc = e
    · obtain ⟨u, rfl⟩ := h
      rw [hP, coeff_rename_mapDomain _ (Fin.castSucc_injective 2)]
      exact hM u
    · rw [hP, coeff_rename_eq_zero _ _ _ (fun u hu => (h ⟨u, hu⟩).elim)]
      simpa using hM0
  have hx' : ∀ i, |(![x 0, x 1, 0] : Fin 3 → ℝ) i| ≤ R := by
    intro i
    fin_cases i
    · simpa using hx 0
    · simpa using hx 1
    · simpa using (zero_le_one.trans hR)
  have hy' : ∀ i, |(![y 0, y 1, 0] : Fin 3 → ℝ) i - (![x 0, x 1, 0] : Fin 3 → ℝ) i| ≤ δ := by
    intro i
    fin_cases i
    · simpa using hy 0
    · simpa using hy 1
    · simpa using hδ0
  have h := Submission.Obl.k4_wide_velocity_lists_scalar_preparation.quadratic_background_variation
    P hPdeg hPM hR hδ0 hδ1 _ _ hx' hy'
  have ex : ∀ z : Fin 2 → ℝ, eval (![z 0, z 1, 0] : Fin 3 → ℝ) P = eval z G := by
    intro z
    have hz : (![z 0, z 1, 0] : Fin 3 → ℝ) ∘ Fin.castSucc = z := by
      funext i
      fin_cases i <;> rfl
    rw [hP, eval_rename, hz]
  rwa [ex, ex] at h

/-- Floors of two quotients by `a` of values `c a`-close differ by at most `⌈c⌉ + 1`. -/
theorem floor_sub_mem {X Y a c : ℝ} (ha : 0 < a) (h : |X - Y| ≤ c * a) :
    ⌊X / a⌋ - ⌊Y / a⌋ ∈ Finset.Icc (-(⌈c⌉ + 1)) (⌈c⌉ + 1) := by
  have h' : |X / a - Y / a| ≤ c := by
    rw [← sub_div, abs_div, abs_of_pos ha, div_le_iff₀ ha]
    exact h
  have h1 := Int.floor_le (X / a)
  have h2 := Int.lt_floor_add_one (X / a)
  have h3 := Int.floor_le (Y / a)
  have h4 := Int.lt_floor_add_one (Y / a)
  have h5 := Int.le_ceil c
  rw [abs_le] at h'
  rw [Finset.mem_Icc]
  constructor
  · have : (-(⌈c⌉ + 1) : ℝ) < ((⌊X / a⌋ - ⌊Y / a⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this.le
  · have : ((⌊X / a⌋ - ⌊Y / a⌋ : ℤ) : ℝ) < ((⌈c⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this.le

/-! ### The quadratic background in the original base -/

/-- Normalized block time `(t - t₀) / q` as a polynomial in the base `(t, Z, Y)`. -/
def bgTau (t₀ q : ℝ) : MvPolynomial (Fin 3) ℝ := C q⁻¹ * (X 0 - C t₀)

/-- Normalized major coordinate `(Z - c₀ - c₁ t) / q`. -/
def bgZeta (q : ℝ) (c : Fin 5 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C q⁻¹ * (X 1 - C (c 0) - C (c 1) * X 0)

/-- Normalized transverse coordinate `(Y - c₂ - c₃ t - c₄ Z) / w`. -/
def bgU (w : ℝ) (c : Fin 5 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C w⁻¹ * (X 2 - C (c 2) - C (c 3) * X 0 - C (c 4) * X 1)

/-- The quadratic background `(F₀ + F₁ τ + F₂ ζ) U + F₃ U²` of a common field `F`. -/
def bgPoly (t₀ q w : ℝ) (c : Fin 5 → ℝ) (F : Fin 4 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  (C (F 0) + C (F 1) * bgTau t₀ q + C (F 2) * bgZeta q c) * bgU w c + C (F 3) * bgU w c ^ 2

theorem eval_bgPoly (t₀ q w : ℝ) (c : Fin 5 → ℝ) (F : Fin 4 → ℝ) (z : Fin 3 → ℝ) :
    eval z (bgPoly t₀ q w c F) =
      (F 0 + F 1 * ((z 0 - t₀) / q) + F 2 * ((z 1 - c 0 - c 1 * z 0) / q)) *
          ((z 2 - c 2 - c 3 * z 0 - c 4 * z 1) / w) +
        F 3 * ((z 2 - c 2 - c 3 * z 0 - c 4 * z 1) / w) ^ 2 := by
  simp only [bgPoly, bgTau, bgZeta, bgU, map_add, map_mul, map_sub, map_pow, eval_C, eval_X]
  ring

theorem totalDegree_affine_le (a b : ℝ) (i : Fin 3) :
    (C a * (X i - C b) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_C]; omega

theorem totalDegree_bgTau (t₀ q : ℝ) : (bgTau t₀ q).totalDegree ≤ 1 :=
  totalDegree_affine_le _ _ _

theorem totalDegree_C_mul_X_le (a : ℝ) (i : Fin 3) :
    (C a * X i : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

theorem totalDegree_bgZeta (q : ℝ) (c : Fin 5 → ℝ) : (bgZeta q c).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_C_mul_X_le _ _))
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_C]; omega

theorem totalDegree_bgU (w : ℝ) (c : Fin 5 → ℝ) : (bgU w c).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_C_mul_X_le _ _))
  refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_C_mul_X_le _ _))
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_C]; omega

theorem totalDegree_C_mul_le' (a : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (C a * P).totalDegree ≤ P.totalDegree := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]

theorem totalDegree_bgPoly (t₀ q w : ℝ) (c : Fin 5 → ℝ) (F : Fin 4 → ℝ) :
    (bgPoly t₀ q w c F).totalDegree ≤ 2 := by
  have h1 : (C (F 0) + C (F 1) * bgTau t₀ q + C (F 2) * bgZeta q c :
      MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_C]; omega
      · exact (totalDegree_C_mul_le' _ _).trans (totalDegree_bgTau _ _)
    · exact (totalDegree_C_mul_le' _ _).trans (totalDegree_bgZeta _ _)
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_bgU w c
    omega
  · refine (totalDegree_C_mul_le' _ _).trans ?_
    refine (totalDegree_pow _ _).trans ?_
    have := totalDegree_bgU w c
    nlinarith

open Submission.Lib.K4ChartLifting in
theorem coeffL1_bgTau_le (t₀ q : ℝ) : coeffL1 (bgTau t₀ q) ≤ |q⁻¹| * (1 + |t₀|) := by
  refine (coeffL1_C_mul_le _ _).trans ?_
  gcongr
  refine (coeffL1_sub_le _ _).trans ?_
  rw [coeffL1_X, coeffL1_C]

open Submission.Lib.K4ChartLifting in
theorem coeffL1_C_mul_X_le' (a : ℝ) (i : Fin 3) :
    coeffL1 (C a * X i : MvPolynomial (Fin 3) ℝ) ≤ |a| := by
  refine (coeffL1_C_mul_le _ _).trans ?_
  rw [coeffL1_X, mul_one]

open Submission.Lib.K4ChartLifting in
theorem coeffL1_bgZeta_le (q : ℝ) (c : Fin 5 → ℝ) :
    coeffL1 (bgZeta q c) ≤ |q⁻¹| * (1 + |c 0| + |c 1|) := by
  refine (coeffL1_C_mul_le _ _).trans ?_
  gcongr
  refine (coeffL1_sub_le _ _).trans ?_
  refine add_le_add ?_ (coeffL1_C_mul_X_le' _ _)
  refine (coeffL1_sub_le _ _).trans ?_
  rw [coeffL1_X, coeffL1_C]

open Submission.Lib.K4ChartLifting in
theorem coeffL1_bgU_le (w : ℝ) (c : Fin 5 → ℝ) :
    coeffL1 (bgU w c) ≤ |w⁻¹| * (1 + |c 2| + |c 3| + |c 4|) := by
  refine (coeffL1_C_mul_le _ _).trans ?_
  gcongr
  refine (coeffL1_sub_le _ _).trans ?_
  refine add_le_add ?_ (coeffL1_C_mul_X_le' _ _)
  refine (coeffL1_sub_le _ _).trans ?_
  refine add_le_add ?_ (coeffL1_C_mul_X_le' _ _)
  refine (coeffL1_sub_le _ _).trans ?_
  rw [coeffL1_X, coeffL1_C]

open Submission.Lib.K4ChartLifting in
/-- The coefficient budget of the background. -/
theorem coeffL1_bgPoly_le {t₀ q w K B : ℝ} {c : Fin 5 → ℝ} {F : Fin 4 → ℝ}
    (hq : 0 < q) (hw : 0 < w) (hqw : q⁻¹ ≤ w⁻¹) (hq1 : 1 ≤ q⁻¹) (ht₀ : |t₀| ≤ 1)
    (hK : 1 ≤ K) (hc : ∀ e, |c e| ≤ K) (hF : ∀ i, |F i| ≤ B) :
    coeffL1 (bgPoly t₀ q w c F) ≤ 40 * K ^ 2 * B * w⁻¹ ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hF 0)
  have hqi : 0 < q⁻¹ := inv_pos.mpr hq
  have hwi : 0 < w⁻¹ := inv_pos.mpr hw
  have hτ : coeffL1 (bgTau t₀ q) ≤ 2 * q⁻¹ := by
    refine (coeffL1_bgTau_le _ _).trans ?_
    rw [abs_of_pos hqi]
    nlinarith
  have hζ : coeffL1 (bgZeta q c) ≤ 3 * K * q⁻¹ := by
    refine (coeffL1_bgZeta_le _ _).trans ?_
    rw [abs_of_pos hqi]
    nlinarith [hc 0, hc 1]
  have hU : coeffL1 (bgU w c) ≤ 4 * K * w⁻¹ := by
    refine (coeffL1_bgU_le _ _).trans ?_
    rw [abs_of_pos hwi]
    nlinarith [hc 2, hc 3, hc 4]
  have hC1 : coeffL1 (C (F 0) + C (F 1) * bgTau t₀ q + C (F 2) * bgZeta q c :
      MvPolynomial (Fin 3) ℝ) ≤ 6 * K * B * w⁻¹ := by
    refine (coeffL1_add_le _ _).trans ?_
    have e1 := coeffL1_add_le (C (F 0) : MvPolynomial (Fin 3) ℝ) (C (F 1) * bgTau t₀ q)
    have e2 := coeffL1_C_mul_le (F 1) (bgTau t₀ q)
    have e3 := coeffL1_C_mul_le (F 2) (bgZeta q c)
    rw [coeffL1_C] at e1
    have hF0 := hF 0
    have hF1 := hF 1
    have hF2 := hF 2
    have k1 : |F 1| * coeffL1 (bgTau t₀ q) ≤ B * (2 * q⁻¹) :=
      mul_le_mul hF1 hτ (coeffL1_nonneg _) hB
    have k2 : |F 2| * coeffL1 (bgZeta q c) ≤ B * (3 * K * q⁻¹) :=
      mul_le_mul hF2 hζ (coeffL1_nonneg _) hB
    have k3 : B * q⁻¹ ≤ B * w⁻¹ := mul_le_mul_of_nonneg_left hqw hB
    have k4 : B ≤ B * q⁻¹ := le_mul_of_one_le_right hB hq1
    have k5 : B * q⁻¹ ≤ K * (B * q⁻¹) := le_mul_of_one_le_left (by positivity) hK
    nlinarith
  calc coeffL1 (bgPoly t₀ q w c F)
      ≤ coeffL1 ((C (F 0) + C (F 1) * bgTau t₀ q + C (F 2) * bgZeta q c) * bgU w c) +
          coeffL1 (C (F 3) * bgU w c ^ 2) := coeffL1_add_le _ _
    _ ≤ (6 * K * B * w⁻¹) * (4 * K * w⁻¹) + B * (4 * K * w⁻¹) ^ 2 := by
        gcongr
        · exact (coeffL1_mul_le _ _).trans
            (mul_le_mul hC1 hU (coeffL1_nonneg _) (by positivity))
        · refine (coeffL1_C_mul_le _ _).trans ?_
          refine mul_le_mul (hF 3) ?_ (coeffL1_nonneg _) hB
          exact (coeffL1_pow_le _ _).trans (pow_le_pow_left₀ (coeffL1_nonneg _) hU 2)
    _ = 40 * K ^ 2 * B * w⁻¹ ^ 2 := by ring

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
