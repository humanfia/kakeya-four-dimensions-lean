import Mathlib

/-!
# Sums of polynomial multiples of products of square roots (algebra)

On an open set `Ω ⊆ ℂ`, let `s i` (`i : Fin m`) be nonvanishing holomorphic square roots of
polynomials `Δ i`.  We study functions of the form

  `P₀ t + ∑ ℓ ∈ L, N ℓ (t) * (∏ i ∈ τ ℓ, s i t) / E(t) ^ K`,   `E = ∏ i, Δ i`,

(`radSum`).  This class is closed under differentiation (`hasDerivAt_radSum`), and dividing by
one of its "nice" factors `∏ i ∈ τ ℓ₀, s i / E ^ K` turns the `ℓ₀`-term into a polynomial while
keeping the others in the class (`radSum_div_eq`).
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Polynomial Metric Set Filter Finset
open scoped Topology

noncomputable section

variable {m : ℕ}

/-- Product of the chosen square roots over `T`. -/
def radProd (s : Fin m → ℂ → ℂ) (T : Finset (Fin m)) (t : ℂ) : ℂ := ∏ i ∈ T, s i t

/-- The common denominator: the product of all radicands. -/
def radDen (Δ : Fin m → ℂ[X]) : ℂ[X] := ∏ i, Δ i

/-- Numerator of the logarithmic derivative of `radProd s U` over the denominator `radDen Δ`. -/
def radLog (Δ : Fin m → ℂ[X]) (U : Finset (Fin m)) : ℂ[X] :=
  ∑ i ∈ U, C (1 / 2 : ℂ) * derivative (Δ i) * ∏ j ∈ univ.erase i, Δ j

/-- The class formula. -/
def radSum (Δ : Fin m → ℂ[X]) (s : Fin m → ℂ → ℂ) {ι : Type*} (L : Finset ι)
    (τ : ι → Finset (Fin m)) (P₀ : ℂ[X]) (N : ι → ℂ[X]) (K : ℕ) (t : ℂ) : ℂ :=
  P₀.eval t + ∑ ℓ ∈ L, (N ℓ).eval t * radProd s (τ ℓ) t / (radDen Δ).eval t ^ K

/-- One differentiation step on the numerators. -/
def radStep (Δ : Fin m → ℂ[X]) {ι : Type*} (τ : ι → Finset (Fin m)) (K : ℕ)
    (N : ι → ℂ[X]) (ℓ : ι) : ℂ[X] :=
  derivative (N ℓ) * radDen Δ + N ℓ * radLog Δ (τ ℓ) - C (K : ℂ) * N ℓ * derivative (radDen Δ)

/-- Iterated differentiation steps on the numerators. -/
def radIter (Δ : Fin m → ℂ[X]) {ι : Type*} (τ : ι → Finset (Fin m)) (K : ℕ) :
    ℕ → (ι → ℂ[X]) → (ι → ℂ[X])
  | 0, N => N
  | j + 1, N => radStep Δ τ (K + j) (radIter Δ τ K j N)

/-- Nonvanishing holomorphic square roots of polynomials of degree at most two on `Ω`. -/
structure RadOn (Δ : Fin m → ℂ[X]) (s : Fin m → ℂ → ℂ) (Ω : Set ℂ) : Prop where
  deg : ∀ i, (Δ i).natDegree ≤ 2
  diff : ∀ i, DifferentiableOn ℂ (s i) Ω
  sq : ∀ i, ∀ t ∈ Ω, s i t ^ 2 = (Δ i).eval t
  ne : ∀ i, ∀ t ∈ Ω, s i t ≠ 0

namespace RadOn

variable {Δ : Fin m → ℂ[X]} {s : Fin m → ℂ → ℂ} {Ω : Set ℂ}

theorem delta_ne (h : RadOn Δ s Ω) (i : Fin m) {t : ℂ} (ht : t ∈ Ω) : (Δ i).eval t ≠ 0 := by
  rw [← h.sq i t ht]
  exact pow_ne_zero 2 (h.ne i t ht)

theorem den_ne (h : RadOn Δ s Ω) {t : ℂ} (ht : t ∈ Ω) : (radDen Δ).eval t ≠ 0 := by
  rw [radDen, eval_prod]
  exact prod_ne_zero_iff.mpr (fun i _ => h.delta_ne i ht)

theorem radProd_ne (h : RadOn Δ s Ω) (T : Finset (Fin m)) {t : ℂ} (ht : t ∈ Ω) :
    radProd s T t ≠ 0 := by
  rw [radProd]
  exact prod_ne_zero_iff.mpr (fun i _ => h.ne i t ht)

theorem hasDerivAt_s (h : RadOn Δ s Ω) (hΩ : IsOpen Ω) (i : Fin m) {t : ℂ} (ht : t ∈ Ω) :
    HasDerivAt (s i) ((Δ i).derivative.eval t / (2 * s i t)) t := by
  have hd : HasDerivAt (s i) (deriv (s i) t) t :=
    ((h.diff i).differentiableAt (hΩ.mem_nhds ht)).hasDerivAt
  have h1 : HasDerivAt (fun x => s i x ^ 2) (2 * s i t * deriv (s i) t) t := by
    convert hd.pow 2 using 1
    ring
  have h2 : HasDerivAt (fun x => s i x ^ 2) ((Δ i).derivative.eval t) t := by
    apply (Polynomial.hasDerivAt (Δ i) t).congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds ht] with x hx
    exact h.sq i x hx
  have heq := h1.unique h2
  have hne : (2 : ℂ) * s i t ≠ 0 := mul_ne_zero two_ne_zero (h.ne i t ht)
  rw [← heq]
  convert hd using 1
  rw [mul_div_cancel_left₀ _ hne]

theorem radDen_eq_mul (i : Fin m) :
    radDen Δ = Δ i * ∏ j ∈ univ.erase i, Δ j := by
  rw [radDen, mul_prod_erase _ _ (mem_univ i)]

theorem hasDerivAt_radProd (h : RadOn Δ s Ω) (hΩ : IsOpen Ω) (U : Finset (Fin m)) {t : ℂ}
    (ht : t ∈ Ω) :
    HasDerivAt (radProd s U)
      (radProd s U t * (radLog Δ U).eval t / (radDen Δ).eval t) t := by
  classical
  have hprod := HasDerivAt.finsetProd (u := U) (f := s)
    (fun i _ => h.hasDerivAt_s hΩ i ht)
  have hfun : (∏ i ∈ U, s i) = radProd s U := by
    funext x
    simp [radProd, Finset.prod_apply]
  rw [hfun] at hprod
  convert hprod using 1
  rw [radLog, eval_finsetSum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hEi := congrArg (Polynomial.eval t) (radDen_eq_mul (Δ := Δ) i)
  rw [eval_mul] at hEi
  have hΔ : (Δ i).eval t ≠ 0 := h.delta_ne i ht
  have hsi : s i t ≠ 0 := h.ne i t ht
  have hrest : (∏ j ∈ univ.erase i, Δ j).eval t ≠ 0 := by
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr (fun j _ => h.delta_ne j ht)
  have hU : radProd s U t = s i t * ∏ j ∈ U.erase i, s j t := by
    rw [radProd, mul_prod_erase _ (fun j => s j t) hi]
  rw [hEi, hU, smul_eq_mul, eval_mul, eval_mul, eval_C, ← h.sq i t ht]
  field_simp

theorem hasDerivAt_radSum (h : RadOn Δ s Ω) (hΩ : IsOpen Ω) {ι : Type*} (L : Finset ι)
    (τ : ι → Finset (Fin m)) (P₀ : ℂ[X]) (N : ι → ℂ[X]) (K : ℕ) {t : ℂ} (ht : t ∈ Ω) :
    HasDerivAt (radSum Δ s L τ P₀ N K)
      (radSum Δ s L τ (derivative P₀) (radStep Δ τ K N) (K + 1) t) t := by
  have hE := h.den_ne ht
  have hterm : ∀ ℓ ∈ L, HasDerivAt
      (fun x => (N ℓ).eval x * radProd s (τ ℓ) x / (radDen Δ).eval x ^ K)
      ((radStep Δ τ K N ℓ).eval t * radProd s (τ ℓ) t / (radDen Δ).eval t ^ (K + 1)) t := by
    intro ℓ _
    have h1 := ((Polynomial.hasDerivAt (N ℓ) t).mul (h.hasDerivAt_radProd hΩ (τ ℓ) ht)).div
      ((Polynomial.hasDerivAt (radDen Δ) t).pow K) (pow_ne_zero K hE)
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    convert h1 using 1
    rw [radStep]
    simp only [eval_add, eval_sub, eval_mul, eval_C]
    set n0 := (N ℓ).eval t
    set n1 := (derivative (N ℓ)).eval t
    set e := radProd s (τ ℓ) t
    set lg := (radLog Δ (τ ℓ)).eval t
    set E0 := (radDen Δ).eval t
    set E1 := (derivative (radDen Δ)).eval t
    rcases K with _ | K
    · simp only [pow_zero, Nat.cast_zero, zero_mul, sub_zero, one_pow, div_one, zero_add,
        pow_one, mul_one]
      field_simp
      ring
    · rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have hsum := HasDerivAt.sum hterm
  have hfun : radSum Δ s L τ P₀ N K =
      fun x => P₀.eval x + ∑ ℓ ∈ L, (N ℓ).eval x * radProd s (τ ℓ) x / (radDen Δ).eval x ^ K := by
    funext x
    rfl
  rw [hfun]
  have hsum' : HasDerivAt (fun x => ∑ ℓ ∈ L, (N ℓ).eval x * radProd s (τ ℓ) x /
      (radDen Δ).eval x ^ K)
      (∑ ℓ ∈ L, (radStep Δ τ K N ℓ).eval t * radProd s (τ ℓ) t /
        (radDen Δ).eval t ^ (K + 1)) t := by
    convert hsum using 1
    funext x
    simp [Finset.sum_apply]
  exact (Polynomial.hasDerivAt P₀ t).add hsum'

theorem iteratedDeriv_eq_radSum (h : RadOn Δ s Ω) (hΩ : IsOpen Ω) {ι : Type*} (L : Finset ι)
    (τ : ι → Finset (Fin m)) (P₀ : ℂ[X]) (N : ι → ℂ[X]) (K : ℕ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ Ω, G t = radSum Δ s L τ P₀ N K t) (j : ℕ) :
    ∀ t ∈ Ω, iteratedDeriv j G t =
      radSum Δ s L τ (derivative^[j] P₀) (radIter Δ τ K j N) (K + j) t := by
  induction j with
  | zero =>
    intro t ht
    simpa [radIter] using hG t ht
  | succ j ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j G =ᶠ[𝓝 t]
        radSum Δ s L τ (derivative^[j] P₀) (radIter Δ τ K j N) (K + j) := by
      filter_upwards [hΩ.mem_nhds ht] with x hx
      exact ih x hx
    rw [hev.deriv_eq, (h.hasDerivAt_radSum hΩ L τ _ _ _ ht).deriv]
    rw [Function.iterate_succ_apply']
    rfl

theorem radProd_mul_radProd (h : RadOn Δ s Ω) {t : ℂ} (ht : t ∈ Ω) (U V : Finset (Fin m)) :
    radProd s U t * radProd s V t =
      radProd s (symmDiff U V) t * ∏ i ∈ U ∩ V, (Δ i).eval t := by
  classical
  have hU : radProd s U t = (∏ i ∈ U ∩ V, s i t) * ∏ i ∈ U \ V, s i t := by
    rw [radProd, prod_inter_mul_prod_sdiff]
  have hV : radProd s V t = (∏ i ∈ U ∩ V, s i t) * ∏ i ∈ V \ U, s i t := by
    rw [radProd, inter_comm U V, prod_inter_mul_prod_sdiff]
  have hS : radProd s (symmDiff U V) t = (∏ i ∈ U \ V, s i t) * ∏ i ∈ V \ U, s i t := by
    rw [radProd, symmDiff_def, Finset.sup_eq_union, prod_union disjoint_sdiff_sdiff]
  have hsq : ∏ i ∈ U ∩ V, (Δ i).eval t = (∏ i ∈ U ∩ V, s i t) ^ 2 := by
    rw [← Finset.prod_pow]
    exact prod_congr rfl (fun i hi => (h.sq i t ht).symm)
  rw [hU, hV, hS, hsq]
  ring

theorem radDen_eval_eq (h : RadOn Δ s Ω) {t : ℂ} (ht : t ∈ Ω) (V : Finset (Fin m)) :
    (radDen Δ).eval t = radProd s V t ^ 2 * ∏ i ∈ Vᶜ, (Δ i).eval t := by
  classical
  rw [radDen, eval_prod, ← prod_mul_prod_compl V, radProd, ← Finset.prod_pow]
  congr 1
  exact prod_congr rfl (fun i _ => (h.sq i t ht).symm)

/-- Dividing by the factor of one term turns that term into a polynomial. -/
theorem radSum_div_eq (h : RadOn Δ s Ω) {ι : Type*} [DecidableEq ι] (L : Finset ι)
    (τ : ι → Finset (Fin m)) (N : ι → ℂ[X]) (K : ℕ) {ℓ₀ : ι} (hℓ₀ : ℓ₀ ∈ L) {t : ℂ}
    (ht : t ∈ Ω) :
    radSum Δ s L τ 0 N K t * (radDen Δ).eval t ^ K / radProd s (τ ℓ₀) t =
      radSum Δ s (L.erase ℓ₀) (fun ℓ => symmDiff (τ ℓ) (τ ℓ₀)) (N ℓ₀)
        (fun ℓ => N ℓ * (∏ i ∈ τ ℓ ∩ τ ℓ₀, Δ i) * ∏ i ∈ (τ ℓ₀)ᶜ, Δ i) 1 t := by
  classical
  have hE := h.den_ne ht
  have he0 := h.radProd_ne (τ ℓ₀) ht
  have hc : (∏ i ∈ (τ ℓ₀)ᶜ, (Δ i).eval t) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => h.delta_ne i ht)
  rw [radSum, radSum, eval_zero, zero_add, ← add_sum_erase L _ hℓ₀, add_mul, add_div,
    sum_mul, sum_div, pow_one]
  congr 1
  · field_simp
  · apply sum_congr rfl
    intro ℓ _
    have hk := h.radProd_mul_radProd ht (τ ℓ) (τ ℓ₀)
    have hd := h.radDen_eval_eq ht (τ ℓ₀)
    rw [eval_mul, eval_mul, eval_prod, eval_prod]
    rw [hd]
    field_simp
    rw [mul_assoc (eval t (N ℓ)), hk]
    ring

end RadOn

theorem natDegree_radDen_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2) :
    (radDen Δ).natDegree ≤ 2 * m := by
  calc (radDen Δ).natDegree ≤ ∑ i, (Δ i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin m, 2 := sum_le_sum (fun i _ => hΔ i)
    _ = 2 * m := by simp [mul_comm]

theorem natDegree_radLog_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2)
    (U : Finset (Fin m)) : (radLog Δ U).natDegree ≤ 2 * m := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i _
  calc (C (1 / 2 : ℂ) * derivative (Δ i) * ∏ j ∈ univ.erase i, Δ j).natDegree
      ≤ (C (1 / 2 : ℂ) * derivative (Δ i)).natDegree + (∏ j ∈ univ.erase i, Δ j).natDegree :=
        natDegree_mul_le
    _ ≤ (Δ i).natDegree + ∑ j ∈ univ.erase i, (Δ j).natDegree := by
        gcongr
        · calc (C (1 / 2 : ℂ) * derivative (Δ i)).natDegree
              ≤ (C (1 / 2 : ℂ)).natDegree + (derivative (Δ i)).natDegree := natDegree_mul_le
            _ ≤ 0 + (Δ i).natDegree := by
                gcongr
                · simp
                · exact (natDegree_derivative_le _).trans (Nat.sub_le _ _)
            _ = (Δ i).natDegree := zero_add _
        · exact natDegree_prod_le _ _
    _ = ∑ j, (Δ j).natDegree := add_sum_erase _ (fun j => (Δ j).natDegree) (mem_univ i)
    _ ≤ ∑ _j : Fin m, 2 := sum_le_sum (fun j _ => hΔ j)
    _ = 2 * m := by simp [mul_comm]

theorem natDegree_radStep_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2) {ι : Type*}
    (τ : ι → Finset (Fin m)) (K : ℕ) (N : ι → ℂ[X]) (ℓ : ι) :
    (radStep Δ τ K N ℓ).natDegree ≤ (N ℓ).natDegree + 2 * m := by
  have hE := natDegree_radDen_le hΔ
  have hL := natDegree_radLog_le hΔ (τ ℓ)
  rw [radStep]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have := natDegree_derivative_le (N ℓ)
      omega
    · apply natDegree_mul_le.trans
      omega
  · apply natDegree_mul_le.trans
    have h1 : (C (K : ℂ) * N ℓ).natDegree ≤ (N ℓ).natDegree :=
      natDegree_mul_le.trans (by simp)
    have h2 := natDegree_derivative_le (radDen Δ)
    omega

theorem natDegree_radIter_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2) {ι : Type*}
    (τ : ι → Finset (Fin m)) (K : ℕ) (N : ι → ℂ[X]) (ℓ : ι) (j : ℕ) :
    (radIter Δ τ K j N ℓ).natDegree ≤ (N ℓ).natDegree + j * (2 * m) := by
  induction j with
  | zero => simp [radIter]
  | succ j ih =>
    rw [radIter]
    have := natDegree_radStep_le hΔ τ (K + j) (radIter Δ τ K j N) ℓ
    rw [Nat.succ_mul]
    omega

theorem natDegree_kill_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2) (P : ℂ[X])
    (U V : Finset (Fin m)) :
    (P * (∏ i ∈ U, Δ i) * ∏ i ∈ V, Δ i).natDegree ≤ P.natDegree + 4 * m := by
  have hprod : ∀ W : Finset (Fin m), (∏ i ∈ W, Δ i).natDegree ≤ 2 * m := by
    intro W
    calc (∏ i ∈ W, Δ i).natDegree ≤ ∑ i ∈ W, (Δ i).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _i ∈ W, 2 := sum_le_sum (fun i _ => hΔ i)
      _ = 2 * W.card := by simp [mul_comm]
      _ ≤ 2 * m := by
          have := card_le_univ W
          simp only [Fintype.card_fin] at this
          omega
  have h1 := hprod U
  have h2 := hprod V
  apply natDegree_mul_le.trans
  have h3 : (P * ∏ i ∈ U, Δ i).natDegree ≤ P.natDegree + 2 * m :=
    natDegree_mul_le.trans (by omega)
  omega

end

end Submission.Obl.k4_quadratic_sheet_continuation
