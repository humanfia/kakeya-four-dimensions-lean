import Mathlib

/-!
# Coefficient and complex evaluation norm bounds

Adapted from: here:o114

Coefficient bounds from real-box bounds, uniformly over bounded-degree
polynomials. Evaluation on a fixed finite grid is an injective linear map on
the bounded-degree space. Its inverse bound controls every coefficient.
-/

namespace Submission.Lib.K4PolynomialRemezThree

open MvPolynomial Set
open scoped BigOperators

noncomputable def coefficientMass {σ : Type*} (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ d ∈ P.support, |P.coeff d|

theorem coefficientMass_nonneg {σ : Type*} (P : MvPolynomial σ ℝ) :
    0 ≤ coefficientMass P := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_coeff_le_coefficientMass {σ : Type*} (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    |P.coeff d| ≤ coefficientMass P := by
  classical
  by_cases hd : d ∈ P.support
  · exact Finset.single_le_sum (f := fun m => |P.coeff m|) (fun _ _ => abs_nonneg _) hd
  · have hd0 : P.coeff d = 0 := by simpa only [mem_support_iff, not_not] using hd
    rw [hd0, abs_zero]
    exact coefficientMass_nonneg P

/-- A degree bound and a real unit-box bound control all coefficients with one
constant depending only on dimension and degree. -/
theorem exists_coefficient_bound_on_unit_cube (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
      (∀ x ∈ Icc (0 : Fin n → ℝ) 1, |eval x P| ≤ E) →
      ∀ d, |P.coeff d| ≤ C * E := by
  classical
  let V := restrictTotalDegree (Fin n) ℝ D
  let r := Module.finrank ℝ V
  let b : Module.Basis (Fin r) ℝ V := Module.finBasis ℝ V
  let e : (Fin r → ℝ) ≃ₗ[ℝ] V := b.equivFun.symm
  let g : Fin (D + 1) → ℝ := fun k => (k : ℝ) / ((D : ℝ) + 1)
  have hden : 0 < (D : ℝ) + 1 := by positivity
  have hg : Function.Injective g := by
    intro k l hkl
    have hh : (k : ℝ) = l := (div_left_inj' hden.ne').mp hkl
    apply Fin.ext
    exact_mod_cast hh
  let Grid := Fin n → Fin (D + 1)
  let L : (Fin r → ℝ) →ₗ[ℝ] (Grid → ℝ) :=
    { toFun := fun v k => eval (fun i => g (k i)) (e v : MvPolynomial (Fin n) ℝ)
      map_add' := by intro v w; ext k; simp
      map_smul' := by intro c v; ext k; simp }
  have hzero : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    have hp : (e v : MvPolynomial (Fin n) ℝ) = 0 := by
      let S : Fin n → Finset ℝ := fun _ => Finset.univ.image g
      have hcard (i : Fin n) : (S i).card = D + 1 := by
        simp [S, Finset.card_image_of_injective _ hg]
      have hdeg : (e v : MvPolynomial (Fin n) ℝ).totalDegree ≤ D :=
        (mem_restrictTotalDegree _ _ _).mp (e v).property
      apply eq_zero_of_eval_zero_at_prod_finset _ S
      · intro i
        rw [hcard i]
        exact Nat.lt_succ_of_le
          ((degreeOf_le_totalDegree (e v : MvPolynomial (Fin n) ℝ) i).trans hdeg)
      · intro x hx
        choose k hk hkx using fun i => Finset.mem_image.mp (hx i)
        have hxeq : x = fun i => g (k i) := by
          funext i
          exact (hkx i).symm
        rw [hxeq]
        exact congrFun hv k
    apply e.injective
    apply Subtype.ext
    simpa only [map_zero, ZeroMemClass.coe_zero] using hp
  have hinj : Function.Injective L := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hzero
    simp only [map_sub, hvw, sub_self]
  obtain ⟨K, hK, hanti⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hinj)
  let B : ℝ := ∑ i : Fin r, coefficientMass (b i : MvPolynomial (Fin n) ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => coefficientMass_nonneg _
  have hcoeff (v : Fin r → ℝ) (d : Fin n →₀ ℕ) :
      |(e v : MvPolynomial (Fin n) ℝ).coeff d| ≤ ‖v‖ * B := by
    have hexp : (e v : MvPolynomial (Fin n) ℝ).coeff d =
        ∑ i : Fin r, v i * (b i : MvPolynomial (Fin n) ℝ).coeff d := by
      dsimp only [e]
      rw [b.equivFun_symm_apply]
      simp
    rw [hexp]
    calc
      _ ≤ ∑ i : Fin r, |v i * (b i : MvPolynomial (Fin n) ℝ).coeff d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin r, |v i| * |(b i : MvPolynomial (Fin n) ℝ).coeff d| := by
        simp only [abs_mul]
      _ ≤ ∑ i : Fin r, ‖v‖ * coefficientMass (b i : MvPolynomial (Fin n) ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
          (abs_coeff_le_coefficientMass _ d) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]
  refine ⟨(K : ℝ) * (B + 1), mul_pos hK (by linarith), ?_⟩
  intro P hP E hE hbound d
  let p : V := ⟨P, (mem_restrictTotalDegree _ _ _).mpr hP⟩
  let v : Fin r → ℝ := b.equivFun p
  have hev : e v = p := b.equivFun.symm_apply_apply p
  have hgrid (k : Grid) : (fun i => g (k i)) ∈ Icc (0 : Fin n → ℝ) 1 := by
    constructor
    · intro i
      dsimp [g]
      positivity
    · intro i
      dsimp [g]
      apply (div_le_iff₀ hden).mpr
      have hh : ((k i : ℕ) : ℝ) < (D : ℝ) + 1 := by exact_mod_cast (k i).isLt
      linarith
  have hLv : ‖L v‖ ≤ E := by
    apply (pi_norm_le_iff_of_nonneg hE).mpr
    intro k
    change |eval (fun i => g (k i)) (e v : MvPolynomial (Fin n) ℝ)| ≤ E
    rw [hev]
    exact hbound _ (hgrid k)
  have hv : ‖v‖ ≤ (K : ℝ) * E :=
    (ZeroHomClass.bound_of_antilipschitz L hanti v).trans
      (mul_le_mul_of_nonneg_left hLv K.coe_nonneg)
  have hh := hcoeff v d
  rw [hev] at hh
  calc
    |P.coeff d| ≤ ‖v‖ * B := hh
    _ ≤ ((K : ℝ) * E) * B := mul_le_mul_of_nonneg_right hv hB
    _ ≤ ((K : ℝ) * E) * (B + 1) := by gcongr; linarith
    _ = (K : ℝ) * (B + 1) * E := by ring

/-- There are at most `(D+1)^n` monomials in the support of a degree-`D`
polynomial; the larger rectangular exponent box suffices here. -/
theorem card_support_le_degree_box (n D : ℕ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) : P.support.card ≤ (D + 1) ^ n := by
  classical
  have hcoord (d : P.support) (i : Fin n) : d.val i < D + 1 :=
    Nat.lt_succ_of_le ((le_degreeOf_of_mem_support i d.property).trans
      ((degreeOf_le_totalDegree P i).trans hP))
  let tag : P.support → (Fin n → Fin (D + 1)) := fun d i => ⟨d.val i, hcoord d i⟩
  have hinj : Function.Injective tag := by
    intro d e hde
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun hde i)
  have hh := Fintype.card_le_of_injective tag hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hh

/-- A coefficient bound gives polynomial growth of the complex evaluation. -/
theorem norm_complex_eval_le_of_coeff_bound (n D : ℕ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R)
    (hcoeff : ∀ d, |P.coeff d| ≤ E) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ R) :
    ‖eval₂ (algebraMap ℝ ℂ) z P‖ ≤ ((D + 1 : ℕ) : ℝ) ^ n * R ^ D * E := by
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hmonomial (d : Fin n →₀ ℕ) (hd : d ∈ P.support) :
      ‖d.prod (fun i k => z i ^ k)‖ ≤ R ^ D := by
    rw [Finsupp.prod, norm_prod]
    calc
      _ ≤ ∏ i ∈ d.support, R ^ d i := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _
      _ = R ^ (d.sum fun _ k => k) := by
        rw [Finset.prod_pow_eq_pow_sum]
        rfl
      _ ≤ R ^ D := pow_le_pow_right₀ hR ((le_totalDegree hd).trans hP)
  have hterm (d : Fin n →₀ ℕ) (hd : d ∈ P.support) :
      ‖eval₂ (algebraMap ℝ ℂ) z (monomial d (P.coeff d))‖ ≤ E * R ^ D := by
    rw [eval₂_monomial, norm_mul]
    rw [show (algebraMap ℝ ℂ) (P.coeff d) = (P.coeff d : ℂ) from rfl,
      Complex.norm_real]
    exact mul_le_mul (hcoeff d) (hmonomial d hd) (norm_nonneg _) hE
  have hcard : (P.support.card : ℝ) ≤ ((D + 1 : ℕ) : ℝ) ^ n := by
    exact_mod_cast card_support_le_degree_box n D P hP
  conv_lhs => rw [P.as_sum]
  rw [eval₂_sum]
  calc
    _ ≤ ∑ d ∈ P.support, ‖eval₂ (algebraMap ℝ ℂ) z (monomial d (P.coeff d))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ P.support, E * R ^ D := Finset.sum_le_sum hterm
    _ = (P.support.card : ℝ) * (E * R ^ D) := by simp [nsmul_eq_mul]
    _ ≤ (((D + 1 : ℕ) : ℝ) ^ n) * (E * R ^ D) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hE (pow_nonneg hR0 _))
    _ = _ := by ring

/-- Norm comparison from a real unit cube to a complex box, with the correct
fixed polynomial cost in the radius. -/
theorem exists_complex_bound_from_real_cube (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
      (∀ x ∈ Icc (0 : Fin n → ℝ) 1, |eval x P| ≤ E) →
      ∀ R : ℝ, 1 ≤ R → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ R) →
        ‖eval₂ (algebraMap ℝ ℂ) z P‖ ≤ C * R ^ D * E := by
  obtain ⟨C, hC, hbound⟩ := exists_coefficient_bound_on_unit_cube n D
  refine ⟨((D + 1 : ℕ) : ℝ) ^ n * C, mul_pos (by positivity) hC, ?_⟩
  intro P hP E hE hreal R hR z hz
  have hh := norm_complex_eval_le_of_coeff_bound n D P hP (mul_nonneg hC.le hE) hR
    (hbound P hP E hE hreal) z hz
  calc
    _ ≤ ((D + 1 : ℕ) : ℝ) ^ n * R ^ D * (C * E) := hh
    _ = _ := by ring

end Submission.Lib.K4PolynomialRemezThree
