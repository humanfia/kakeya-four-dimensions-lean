import Mathlib
import Submission.Obl.k4_algebraic_sheet_remez.Rolle
import Submission.Obl.k4_algebraic_sheet_remez.PolynomialDerivatives

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Polynomial

/-- Lagrange's interpolation remainder at the left endpoint, with positive
ordered interpolation nodes. -/
theorem interpolation_remainder_zero (q : ℕ) {g : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hg : ContDiffOn ℝ q g (Ioo (-2 : ℝ) 2))
    (t : Fin q → ℝ) (htmono : StrictMono t)
    (htpos : ∀ i, 0 < t i) (htI : ∀ i, t i ∈ Icc (0 : ℝ) T) :
    ∃ ξ ∈ Icc (0 : ℝ) T,
      g 0 - (Lagrange.interpolate Finset.univ t (fun i => g (t i))).eval 0 =
        iteratedDeriv q g ξ / (q.factorial : ℝ) * ∏ i, (0 - t i) := by
  classical
  let p := Lagrange.interpolate Finset.univ t (fun i => g (t i))
  let w : Polynomial ℝ := ∏ i : Fin q, (Polynomial.X - Polynomial.C (t i))
  have hwdeg : w.natDegree = q := by
    simp only [w, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hwmonic : w.Monic := Polynomial.monic_prod_X_sub_C t Finset.univ
  have hwcoeff : w.coeff q = 1 := by
    rw [← hwdeg]
    exact hwmonic
  have hwval (z : ℝ) : w.eval z = ∏ i, (z - t i) := by
    dsimp only [w]
    rw [Polynomial.eval_prod]
    simp
  have hw0 : w.eval 0 ≠ 0 := by
    rw [hwval]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (htpos i).ne)
  have hwinode (i : Fin q) : w.eval (t i) = 0 := by
    rw [hwval]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hpnode (i : Fin q) : p.eval (t i) = g (t i) :=
    Lagrange.eval_interpolate_at_node _ htmono.injective.injOn (Finset.mem_univ i)
  have hpdeg : p.degree < (q : WithBot ℕ) := by
    simpa only [p, Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (fun i => g (t i)) htmono.injective.injOn
  have hpderiv (z : ℝ) : iteratedDeriv q (fun u : ℝ => p.eval u) z = 0 := by
    rw [iteratedDeriv_polynomial_eval,
      Polynomial.iterate_derivative_eq_zero_of_degree_lt hpdeg]
    simp
  have hwderiv (z : ℝ) : iteratedDeriv q (fun u : ℝ => w.eval u) z = q.factorial := by
    rw [iteratedDeriv_polynomial_top w q hwdeg.le z, hwcoeff, mul_one]
  have hpcont : ContDiff ℝ q (fun u : ℝ => p.eval u) := by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) p q
  have hwcont : ContDiff ℝ q (fun u : ℝ => w.eval u) := by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) w q
  let a := (g 0 - p.eval 0) / w.eval 0
  let h : ℝ → ℝ := fun u => g u - p.eval u - a * w.eval u
  have hh : ContDiffOn ℝ q h (Ioo (-2 : ℝ) 2) :=
    (hg.sub hpcont.contDiffOn).sub (contDiff_const.mul hwcont).contDiffOn
  have hh0 : h 0 = 0 := by
    change g 0 - p.eval 0 - ((g 0 - p.eval 0) / w.eval 0) * w.eval 0 = 0
    rw [div_mul_cancel₀ _ hw0, sub_self]
  have hhnode (i : Fin q) : h (t i) = 0 := by
    simp only [h, hpnode, hwinode, mul_zero, sub_self, sub_zero]
  let u : Fin (q + 1) → ℝ := Fin.cons (0 : ℝ) t
  have hconsmono : StrictMono u := Fin.strictMono_cons.mpr ⟨htpos, htmono⟩
  have hconsI : ∀ i, u i ∈ Icc (0 : ℝ) T := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨le_rfl, hT⟩
    · exact htI j
  have hconszero : ∀ i, h (u i) = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hh0
    · exact hhnode j
  obtain ⟨ξ, hξ, hhξ⟩ := exists_iteratedDeriv_eq_zero q hT1 hh
    u hconsmono hconsI hconszero
  have hξU : ξ ∈ Ioo (-2 : ℝ) 2 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hgf := hg.contDiffAt (isOpen_Ioo.mem_nhds hξU)
  have hpf := hpcont.contDiffAt (x := ξ)
  have hwf : ContDiffAt ℝ q (fun u : ℝ => a * w.eval u) ξ :=
    (contDiff_const.mul hwcont).contDiffAt
  have hderiv : iteratedDeriv q h ξ = iteratedDeriv q g ξ - a * (q.factorial : ℝ) := by
    dsimp only [h]
    rw [iteratedDeriv_fun_sub (hgf.sub hpf) hwf,
      iteratedDeriv_fun_sub hgf hpf, hpderiv,
      iteratedDeriv_const_mul_field, hwderiv, sub_zero]
  have haeq : a = iteratedDeriv q g ξ / (q.factorial : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast (Nat.factorial_ne_zero q))).mpr
    linarith [hderiv, hhξ]
  refine ⟨ξ, hξ, ?_⟩
  change g 0 - p.eval 0 = _
  calc
    _ = a * w.eval 0 := (div_mul_cancel₀ _ hw0).symm
    _ = iteratedDeriv q g ξ / (q.factorial : ℝ) * ∏ i, (0 - t i) := by rw [haeq, hwval]

end Submission.Obl.k4_algebraic_sheet_remez
