import Mathlib
import Submission.Obl.k4_quadratic_sheet_continuation.TuranEst
import Submission.Obl.k4_quadratic_sheet_continuation.RadReduce
import Submission.Obl.k4_quadratic_sheet_continuation.SheetQuadratic
import Submission.Obl.k4_quadratic_sheet_continuation.Smooth

/-!
# Scalar jet propagation for evaluations of simple linear or quadratic sheets

For sheets `f i` on the `A⁻¹`-neighbourhood of `[0,1] ⊆ ℂ`, simple roots of polynomials of total
degree at most two in `(t, w)`, and `G t = Q(t, f(t))` with `deg Q ≤ D`, the jets of `G` at `0`
up to a fixed order control `G 1` with loss `A ^ K` (`scalar_jet_propagation`).

Each sheet gives the nonvanishing square root `s i = ∂_w P_i(t, f_i) = 2 γ f_i + α(t)` of the
polynomial `Δ i = α ^ 2 - 4 γ β`; `f_i * E` is affine in `s i` with polynomial coefficients
(`E = ∏ Δ i`), so `G * E ^ D` is a polynomial in `t` and the `s i`, which reduces to the class of
`turan_jet_bound`.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Polynomial Finset

noncomputable section

/-- Evaluation at `Y i = s i t`, coefficients evaluated at `t`. -/
def evY {m : ℕ} (s : Fin m → ℂ → ℂ) (t : ℂ) : MvPolynomial (Fin m) ℂ[X] →+* ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (fun i => s i t)

/-- The homogenized substitution of `Xs j / E` into `Q`. -/
def homSubst {m k : ℕ} (Q : MvPolynomial (Fin k) ℂ) (D : ℕ) (E : ℂ[X])
    (Xs : Fin k → MvPolynomial (Fin m) ℂ[X]) : MvPolynomial (Fin m) ℂ[X] :=
  ∑ μ ∈ Q.support, MvPolynomial.C (C (Q.coeff μ) * E ^ (D - ∑ j, μ j)) * ∏ j, Xs j ^ μ j

theorem evY_homSubst {m k : ℕ} (Q : MvPolynomial (Fin k) ℂ) {D : ℕ} (hQ : Q.totalDegree ≤ D)
    (E : ℂ[X]) (Xs : Fin k → MvPolynomial (Fin m) ℂ[X]) (s : Fin m → ℂ → ℂ) (t : ℂ)
    (x : Fin k → ℂ) (hx : ∀ j, evY s t (Xs j) = x j * E.eval t) :
    evY s t (homSubst Q D E Xs) = MvPolynomial.eval x Q * E.eval t ^ D := by
  classical
  rw [homSubst, map_sum, MvPolynomial.eval_eq', sum_mul]
  apply sum_congr rfl
  intro μ hμ
  have hμD : ∑ j, μ j ≤ D := by
    have := MvPolynomial.le_totalDegree hμ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    omega
  rw [map_mul, map_prod]
  simp only [map_pow, hx]
  simp only [evY, MvPolynomial.eval₂Hom_C, Polynomial.coe_evalRingHom, eval_mul, eval_C, eval_pow]
  rw [prod_congr rfl (fun j _ => mul_pow (x j) (E.eval t) (μ j)), prod_mul_distrib,
    prod_pow_eq_pow_sum]
  calc Q.coeff μ * E.eval t ^ (D - ∑ j, μ j) * ((∏ j, x j ^ μ j) * E.eval t ^ ∑ j, μ j)
      = Q.coeff μ * (∏ j, x j ^ μ j) * (E.eval t ^ (D - ∑ j, μ j) * E.eval t ^ ∑ j, μ j) := by
        ring
    _ = Q.coeff μ * (∏ j, x j ^ μ j) * E.eval t ^ D := by
        rw [← pow_add, Nat.sub_add_cancel hμD]

theorem coeffDegLe_homSubst {m k : ℕ} (Q : MvPolynomial (Fin k) ℂ) {D : ℕ}
    (hQ : Q.totalDegree ≤ D) (E : ℂ[X]) {e : ℕ} (hE : E.natDegree ≤ e)
    (Xs : Fin k → MvPolynomial (Fin m) ℂ[X]) {c : ℕ} (hX : ∀ j, CoeffDegLe (Xs j) c) :
    CoeffDegLe (homSubst Q D E Xs) (D * e + D * c) := by
  classical
  apply CoeffDegLe.sum
  intro μ hμ
  have hμD : ∑ j, μ j ≤ D := by
    have := MvPolynomial.le_totalDegree hμ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    omega
  have h1 : CoeffDegLe (MvPolynomial.C (C (Q.coeff μ) * E ^ (D - ∑ j, μ j)) :
      MvPolynomial (Fin m) ℂ[X]) (D * e) := by
    apply (CoeffDegLe.C _).mono
    calc (C (Q.coeff μ) * E ^ (D - ∑ j, μ j)).natDegree
        ≤ (C (Q.coeff μ)).natDegree + (E ^ (D - ∑ j, μ j)).natDegree := natDegree_mul_le
      _ ≤ 0 + (D - ∑ j, μ j) * E.natDegree := add_le_add (by simp) natDegree_pow_le
      _ ≤ D * e := by
          rw [zero_add]
          exact Nat.mul_le_mul (Nat.sub_le _ _) hE
  have h2 : CoeffDegLe (∏ j, Xs j ^ μ j) (∑ j, μ j * c) :=
    CoeffDegLe.prod _ _ _ (fun j _ => (hX j).pow (μ j))
  apply (h1.mul h2).mono
  rw [← sum_mul]
  have := Nat.mul_le_mul_right c hμD
  omega

theorem totalDegree_homSubst_le {m k : ℕ} (Q : MvPolynomial (Fin k) ℂ) {D : ℕ}
    (hQ : Q.totalDegree ≤ D) (E : ℂ[X]) (Xs : Fin k → MvPolynomial (Fin m) ℂ[X])
    (hX : ∀ j, (Xs j).totalDegree ≤ 1) : (homSubst Q D E Xs).totalDegree ≤ D := by
  classical
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro μ hμ
  have hμD : ∑ j, μ j ≤ D := by
    have := MvPolynomial.le_totalDegree hμ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    omega
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc ∑ j, (Xs j ^ μ j).totalDegree ≤ ∑ j, μ j * 1 := by
        gcongr with j
        exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hX j))
    _ ≤ D := by simpa using hμD

/-- The polynomial in the square roots that represents `f_i * E`. -/
def sheetY {m : ℕ} (γ : Fin m → ℂ) (α β Δ : Fin m → ℂ[X]) (i : Fin m) :
    MvPolynomial (Fin m) ℂ[X] :=
  if γ i = 0 then -(MvPolynomial.C (β i * ∏ j ∈ univ.erase i, Δ j)) * MvPolynomial.X i
  else MvPolynomial.C (C (1 / (2 * γ i)) * radDen Δ) * MvPolynomial.X i -
    MvPolynomial.C (C (1 / (2 * γ i)) * α i * radDen Δ)

theorem evY_sheetY {m : ℕ} (γ : Fin m → ℂ) (α β : Fin m → ℂ[X]) (f : Fin m → ℂ → ℂ)
    (i : Fin m) (t : ℂ)
    (heq : γ i * f i t ^ 2 + (α i).eval t * f i t + (β i).eval t = 0) :
    evY (fun j t => 2 * γ j * f j t + (α j).eval t) t
        (sheetY γ α β (fun j => α j ^ 2 - C (4 * γ j) * β j) i) =
      f i t * (radDen (fun j => α j ^ 2 - C (4 * γ j) * β j)).eval t := by
  classical
  have hE := RadOn.radDen_eq_mul (Δ := fun j => α j ^ 2 - C (4 * γ j) * β j) i
  unfold sheetY
  split_ifs with hγ
  · rw [hE]
    beta_reduce
    generalize (∏ j ∈ univ.erase i, (α j ^ 2 - C (4 * γ j) * β j)) = Pp
    simp only [evY, map_mul, map_neg, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Polynomial.coe_evalRingHom, eval_mul, eval_sub, eval_pow, eval_C, hγ, mul_zero,
      zero_mul, zero_add, sub_zero] at heq ⊢
    linear_combination (-(α i).eval t * Pp.eval t) * heq
  · simp only [evY, map_mul, map_sub, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Polynomial.coe_evalRingHom, eval_mul, eval_C]
    have h2 : (2 : ℂ) * γ i ≠ 0 := mul_ne_zero two_ne_zero hγ
    field_simp
    ring

theorem coeffDegLe_sheetY {m : ℕ} (γ : Fin m → ℂ) (α β Δ : Fin m → ℂ[X])
    (hα : ∀ i, (α i).natDegree ≤ 1) (hβ : ∀ i, (β i).natDegree ≤ 2)
    (hΔ : ∀ i, (Δ i).natDegree ≤ 2) (i : Fin m) :
    CoeffDegLe (sheetY γ α β Δ i) (2 * m + 3) := by
  classical
  have hE := natDegree_radDen_le hΔ
  have hprod : (∏ j ∈ univ.erase i, Δ j).natDegree ≤ 2 * m := by
    calc (∏ j ∈ univ.erase i, Δ j).natDegree ≤ ∑ j ∈ univ.erase i, (Δ j).natDegree :=
          natDegree_prod_le _ _
      _ ≤ ∑ j : Fin m, (Δ j).natDegree := sum_le_sum_of_subset (erase_subset _ _)
      _ ≤ ∑ _j : Fin m, 2 := sum_le_sum (fun j _ => hΔ j)
      _ = 2 * m := by simp [mul_comm]
  unfold sheetY
  split_ifs with hγ
  · have h1 : CoeffDegLe (MvPolynomial.C (β i * ∏ j ∈ univ.erase i, Δ j) :
        MvPolynomial (Fin m) ℂ[X]) (2 * m + 3) := by
      apply (CoeffDegLe.C _).mono
      calc (β i * ∏ j ∈ univ.erase i, Δ j).natDegree
          ≤ (β i).natDegree + (∏ j ∈ univ.erase i, Δ j).natDegree := natDegree_mul_le
        _ ≤ 2 * m + 3 := by have := hβ i; omega
    simpa using h1.neg.mul (CoeffDegLe.X i)
  · have h1 : CoeffDegLe (MvPolynomial.C (C (1 / (2 * γ i)) * radDen Δ) :
        MvPolynomial (Fin m) ℂ[X]) (2 * m + 3) := by
      apply (CoeffDegLe.C _).mono
      calc (C (1 / (2 * γ i)) * radDen Δ).natDegree
          ≤ (C (1 / (2 * γ i))).natDegree + (radDen Δ).natDegree := natDegree_mul_le
        _ ≤ 2 * m + 3 := by rw [natDegree_C]; omega
    have h2 : CoeffDegLe (MvPolynomial.C (C (1 / (2 * γ i)) * α i * radDen Δ) :
        MvPolynomial (Fin m) ℂ[X]) (2 * m + 3) := by
      apply (CoeffDegLe.C _).mono
      calc (C (1 / (2 * γ i)) * α i * radDen Δ).natDegree
          ≤ (C (1 / (2 * γ i)) * α i).natDegree + (radDen Δ).natDegree := natDegree_mul_le
        _ ≤ ((C (1 / (2 * γ i))).natDegree + (α i).natDegree) + (radDen Δ).natDegree :=
            add_le_add natDegree_mul_le le_rfl
        _ ≤ 2 * m + 3 := by rw [natDegree_C]; have := hα i; omega
    exact (by simpa using h1.mul (CoeffDegLe.X i) : CoeffDegLe _ (2 * m + 3)).sub h2

theorem totalDegree_sheetY_le {m : ℕ} (γ : Fin m → ℂ) (α β Δ : Fin m → ℂ[X]) (i : Fin m) :
    (sheetY γ α β Δ i).totalDegree ≤ 1 := by
  classical
  unfold sheetY
  split_ifs
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]
      exact zero_le_one

/-- **Scalar jet propagation** (the scalar child of o113, with its exact frozen type). -/
theorem scalar_jet_propagation : ∀ m D : ℕ, ∃ N : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 2 ≤ A → ∀ (P : Fin m → MvPolynomial (Fin 2) ℂ) (f : Fin m → ℂ → ℂ) (Q : MvPolynomial (Fin (1 + m)) ℂ), (fun U : Set ℂ => (fun G : ℂ → ℂ => (∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) U ∧ ∀ t ∈ U, MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t)) (P i) = 0 ∧ MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t)) (MvPolynomial.pderiv (Fin.last 1) (P i)) ≠ 0) → Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V → (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j G 0‖ ≤ V) → ‖G 1‖ ≤ A ^ K * V) (fun t : ℂ => MvPolynomial.eval (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f i t)) Q)) (Metric.thickening (A⁻¹) (segment ℝ (0 : ℂ) 1)) := by
  intro m D
  obtain ⟨q, k, C₀, hC₀, hT⟩ := turan_jet_bound m (2 ^ m) D (D * (2 * m) + D * (2 * m + 3) + D)
  refine ⟨q, ((k + ⌈C₀⌉₊ : ℕ) : ℝ), ?_, ?_⟩
  · have : 0 < ⌈C₀⌉₊ := Nat.ceil_pos.mpr hC₀
    exact_mod_cast (by omega : 0 < k + ⌈C₀⌉₊)
  intro A hA P f Q hsheet hQ V hV hjet
  classical
  have hA0 : 0 < A := by linarith
  set ρ := A⁻¹ with hρdef
  have hρ : 0 < ρ := inv_pos.mpr hA0
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  change ∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) (tube ρ) ∧
    ∀ t ∈ tube ρ, MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t)) (P i) = 0 ∧
      MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t))
        (MvPolynomial.pderiv (Fin.last 1) (P i)) ≠ 0 at hsheet
  set G : ℂ → ℂ := fun t : ℂ =>
    MvPolynomial.eval (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f i t)) Q with hGdef
  choose γ α β hα hβ hPeq using fun i => exists_quadratic_in_last (P i) (hsheet i).2.1
  set s : Fin m → ℂ → ℂ := fun i t => 2 * γ i * f i t + (α i).eval t with hsdef
  set Δ : Fin m → ℂ[X] := fun i => α i ^ 2 - Polynomial.C (4 * γ i) * β i with hΔdef
  have hpd : ∀ i t w, MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) w)
      (MvPolynomial.pderiv (Fin.last 1) (P i)) = 2 * γ i * w + (α i).eval t := by
    intro i t w
    have h1 := hasDerivAt_eval_snoc (n := 1) (P i) (fun _ : Fin 1 => t) w
    have heq : (fun w' : ℂ => MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) w') (P i)) =
        fun w' => γ i * w' ^ 2 + (α i).eval t * w' + (β i).eval t := funext (hPeq i t)
    rw [heq] at h1
    have h2 : HasDerivAt (fun w' : ℂ => γ i * w' ^ 2 + (α i).eval t * w' + (β i).eval t)
        (2 * γ i * w + (α i).eval t) w := by
      have := (((hasDerivAt_pow 2 w).const_mul (γ i)).add
        ((hasDerivAt_id w).const_mul ((α i).eval t))).add_const ((β i).eval t)
      convert this using 1
      simp
      ring
    exact h1.unique h2
  have hRad : RadOn Δ s (tube ρ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact natDegree_pow_le.trans (by have := hα i; omega)
      · exact (natDegree_C_mul_le _ _).trans (hβ i)
    · intro i
      exact ((hsheet i).2.2.1.const_mul (2 * γ i)).add
        (Polynomial.differentiable (α i)).differentiableOn
    · intro i t ht
      have h0 := ((hsheet i).2.2.2 t ht).1
      rw [hPeq i t] at h0
      simp only [hsdef, hΔdef, eval_sub, eval_pow, eval_mul, eval_C]
      linear_combination (4 * γ i) * h0
    · intro i t ht
      have h0 := ((hsheet i).2.2.2 t ht).2
      rw [hpd i t] at h0
      exact h0
  -- the representation of `G`
  set Xs : Fin (1 + m) → MvPolynomial (Fin m) ℂ[X] :=
    Fin.append (fun _ : Fin 1 => MvPolynomial.C (X * radDen Δ)) (fun i => sheetY γ α β Δ i)
    with hXsdef
  set Qt := homSubst Q D (radDen Δ) Xs with hQtdef
  have hXs : ∀ t ∈ tube ρ, ∀ j, evY s t (Xs j) =
      (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f i t)) j * (radDen Δ).eval t := by
    intro t ht j
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j
    · simp only [hXsdef, Fin.append_left, evY, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_evalRingHom, eval_mul, eval_X]
    · simp only [hXsdef, Fin.append_right]
      have h0 := ((hsheet i).2.2.2 t ht).1
      rw [hPeq i t] at h0
      exact evY_sheetY γ α β f i t h0
  have hrep : ∀ t ∈ tube ρ, G t = radSum Δ s univ id 0 (reduceN Δ Qt) D t := by
    intro t ht
    have hE : (radDen Δ).eval t ≠ 0 := hRad.den_ne ht
    have h1 := evY_homSubst Q hQ (radDen Δ) Xs s t _ (hXs t ht)
    have h2 := eval_eq_sum_reduce Δ s Qt (t := t) (fun i => hRad.sq i t ht)
    have h3 : G t * (radDen Δ).eval t ^ D =
        ∑ T : Finset (Fin m), (reduceN Δ Qt T).eval t * radProd s T t := by
      rw [← h2]
      exact h1.symm
    rw [radSum, eval_zero, zero_add, ← sum_div]
    simp only [id]
    rw [← h3]
    field_simp
  have hdeg : ∀ T ∈ (univ : Finset (Finset (Fin m))),
      (reduceN Δ Qt T).natDegree ≤ D * (2 * m) + D * (2 * m + 3) + D := by
    intro T _
    have hc : CoeffDegLe Qt (D * (2 * m) + D * (2 * m + 3)) := by
      apply coeffDegLe_homSubst Q hQ (radDen Δ) (natDegree_radDen_le hRad.deg) Xs
      intro j
      refine Fin.addCases (fun j => ?_) (fun i => ?_) j
      · simp only [hXsdef, Fin.append_left]
        apply (CoeffDegLe.C _).mono
        calc (X * radDen Δ).natDegree ≤ X.natDegree + (radDen Δ).natDegree := natDegree_mul_le
          _ ≤ 2 * m + 3 := by
              have := natDegree_radDen_le hRad.deg
              rw [natDegree_X]
              omega
      · simp only [hXsdef, Fin.append_right]
        exact coeffDegLe_sheetY γ α β Δ hα hβ hRad.deg i
    have ht : Qt.totalDegree ≤ D := by
      apply totalDegree_homSubst_le Q hQ (radDen Δ) Xs
      intro j
      refine Fin.addCases (fun j => ?_) (fun i => ?_) j
      · simp only [hXsdef, Fin.append_left, MvPolynomial.totalDegree_C]
        exact zero_le_one
      · simp only [hXsdef, Fin.append_right]
        exact totalDegree_sheetY_le γ α β Δ i
    have := natDegree_reduceN_le hRad.deg hc T
    omega
  have hcard : (univ : Finset (Finset (Fin m))).card ≤ 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_finset]
  have hbound := hT ρ hρ hρ1 Δ s hRad (univ : Finset (Finset (Fin m))) id (reduceN Δ Qt) hcard
    hdeg G hrep V hjet 1 (right_mem_segment ℝ 0 1)
  change ‖G 1‖ ≤ A ^ ((k + ⌈C₀⌉₊ : ℕ) : ℝ) * V
  rw [Real.rpow_natCast]
  have hρinv : ρ⁻¹ = A := by rw [hρdef, inv_inv]
  rw [hρinv] at hbound
  have hCA : C₀ ≤ A ^ ⌈C₀⌉₊ := by
    calc C₀ ≤ ⌈C₀⌉₊ := Nat.le_ceil C₀
      _ ≤ 2 ^ ⌈C₀⌉₊ := by exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ A ^ ⌈C₀⌉₊ := pow_le_pow_left₀ (by norm_num) hA _
  calc ‖G 1‖ ≤ C₀ * A ^ k * V := hbound
    _ ≤ A ^ ⌈C₀⌉₊ * A ^ k * V := by gcongr
    _ = A ^ (k + ⌈C₀⌉₊) * V := by rw [pow_add]; ring

end

end Submission.Obl.k4_quadratic_sheet_continuation
