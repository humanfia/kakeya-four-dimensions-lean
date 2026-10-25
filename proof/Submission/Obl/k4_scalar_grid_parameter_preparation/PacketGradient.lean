/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PacketGradient.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialComparison
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

/-! Whole-block scalar packet fits control the physical directional derivative. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set

theorem exists_polynomial_interval_derivative_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : Polynomial ℝ) (a h E : ℝ), p.natDegree ≤ D → 0 < h → 0 ≤ E →
      (∀ t ∈ Set.Icc a (a + h), |p.eval t| ≤ E) →
      ∀ t ∈ Set.Icc a (a + h), |p.derivative.eval t| ≤ C * E / h := by
  obtain ⟨C, hC, hderiv⟩ := exists_polynomial_derivative_bound D
  refine ⟨C, hC, ?_⟩
  intro p a h E hp hh hE hbound
  let A : Polynomial ℝ := Polynomial.C a + Polynomial.C h * Polynomial.X
  let q := p.comp A
  have hA : A.natDegree ≤ 1 := by dsimp [A]; compute_degree!
  have hq : q.natDegree ≤ D := by
    exact (Polynomial.natDegree_comp_le).trans
      ((Nat.mul_le_mul hp hA).trans_eq (Nat.mul_one _))
  have hqeval (s : ℝ) : q.eval s = p.eval (a + h * s) := by
    simp [q, A]
  have hqderiv (s : ℝ) : q.derivative.eval s = h * p.derivative.eval (a + h * s) := by
    simp only [q, A, Polynomial.derivative_comp, Polynomial.derivative_add,
      Polynomial.derivative_C, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
      Polynomial.eval_C, Polynomial.eval_X, zero_add, zero_mul, mul_one]
  have hqbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, |q.eval s| ≤ E := by
    intro s hs
    rw [hqeval]
    apply hbound
    constructor <;> nlinarith [mul_nonneg hh.le hs.1, mul_nonneg hh.le (sub_nonneg.mpr hs.2)]
  intro t ht
  let s := (t - a) / h
  have hs : s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht.1) hh.le, (div_le_one hh).mpr (by linarith [ht.2])⟩
  have htime : a + h * s = t := by dsimp [s]; field_simp; ring
  have hb := hderiv q E hq hE hqbound s hs
  rw [hqderiv, htime, abs_mul, abs_of_pos hh] at hb
  exact (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hb)

/-- Unlike a general algebraic prediction, the frozen scalar packet is a quadratic
polynomial fitted on the whole block, so its directional error needs no time pruning. -/
theorem exists_scalar_packet_directional_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : MvPolynomial (Fin 2) ℝ) (a : Fin 5 → ℝ) (t₀ h E : ℝ),
      F.totalDegree ≤ 2 → 0 < h → 0 ≤ E →
      (∀ t ∈ Set.Icc t₀ (t₀ + h),
        |a 2 + t * a 3 + t ^ 2 * a 4 - MvPolynomial.eval ![t, a 0 + t * a 1] F| ≤ E) →
      ∀ t ∈ Set.Icc t₀ (t₀ + h),
        |MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 0 F) +
          a 1 * MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 1 F) -
          (a 3 + 2 * t * a 4)| ≤ C * E / h := by
  obtain ⟨C, hC, hderiv⟩ := exists_polynomial_interval_derivative_bound 2
  refine ⟨C, hC, ?_⟩
  intro F a t₀ h E hF hh hE hfit
  let f : Polynomial ℝ := Polynomial.C (a 2) + Polynomial.C (a 3) * Polynomial.X +
    Polynomial.C (a 4) * Polynomial.X ^ 2
  let g := Submission.Lib.K4PolynomialPotential.scalarLineHom (a 0) (a 1) F - f
  have hf : f.natDegree ≤ 2 := by dsimp [f]; compute_degree!
  have hg : g.natDegree ≤ 2 := (Polynomial.natDegree_sub_le _ _).trans
    (max_le ((Submission.Lib.K4PolynomialPotential.natDegree_scalarLineHom_le F _ _).trans hF) hf)
  have hfeval (t : ℝ) : f.eval t = a 2 + t * a 3 + t ^ 2 * a 4 := by simp [f]; ring
  have hfderiv (t : ℝ) : f.derivative.eval t = a 3 + 2 * t * a 4 := by simp [f]; ring
  have hbound : ∀ t ∈ Set.Icc t₀ (t₀ + h), |g.eval t| ≤ E := by
    intro t ht
    simpa only [g, Polynomial.eval_sub, hfeval,
      Submission.Lib.K4PolynomialPotential.eval_scalarLineHom, abs_sub_comm] using hfit t ht
  intro t ht
  have hd := hderiv g t₀ h E hg hh hE hbound t ht
  simpa only [g, Polynomial.derivative_sub, Polynomial.eval_sub, hfderiv,
    Submission.Lib.K4PolynomialPotential.eval_derivative_scalarLineHom] using hd

/-- The actual packet rate turns the derivative error into a bound independent of
the packet's scale and duration. -/
theorem exists_scalar_packet_field_bound : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : MvPolynomial (Fin 2) ℝ) (a : Fin 5 → ℝ) (K t₀ h ξ : ℝ),
      F.totalDegree ≤ 2 → 1 ≤ K → (∀ e, |a e| ≤ K) → 0 ≤ t₀ → t₀ + h ≤ 1 →
      0 < h → 0 < ξ → ξ ≤ K * h →
      (∀ t ∈ Set.Icc t₀ (t₀ + h),
        |a 2 + t * a 3 + t ^ 2 * a 4 - MvPolynomial.eval ![t, a 0 + t * a 1] F| ≤ K * ξ) →
      ∀ t ∈ Set.Icc t₀ (t₀ + h),
        |MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 0 F) +
          a 1 * MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 1 F)| ≤ C * K ^ 2 := by
  obtain ⟨C, hC, hdir⟩ := exists_scalar_packet_directional_bound
  refine ⟨C + 3, by linarith, ?_⟩
  intro F a K t₀ h ξ hF hK ha ht₀ ht₁ hh hξ hrate hfit t ht
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have htime : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht₀.trans ht.1, ht.2.trans ht₁⟩
  have hx' : |a 3 + 2 * t * a 4| ≤ 3 * K := by
    calc
      _ ≤ |a 3| + 2 * |t| * |a 4| := by
        simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
          abs_add_le (a 3) (2 * t * a 4)
      _ ≤ K + 2 * 1 * K := by
        apply add_le_add (ha 3)
        apply mul_le_mul _ (ha 4) (abs_nonneg _) (by norm_num)
        exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg htime.1]; exact htime.2) (by norm_num)
      _ = _ := by ring
  have herror : C * (K * ξ) / h ≤ C * K ^ 2 := by
    calc
      _ = (C * K) * (ξ / h) := by ring
      _ ≤ (C * K) * K := mul_le_mul_of_nonneg_left ((div_le_iff₀ hh).mpr hrate) (by positivity)
      _ = _ := by ring
  have hd := hdir F a t₀ h (K * ξ) hF hh (mul_nonneg hK₀ hξ.le) hfit t ht
  have hfield := (abs_sub_le
    (MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 0 F) +
      a 1 * MvPolynomial.eval ![t, a 0 + t * a 1] (MvPolynomial.pderiv 1 F))
    (a 3 + 2 * t * a 4) 0)
  simp only [sub_zero] at hfield
  have hKsq : K ≤ K ^ 2 := by nlinarith
  linarith [hd.trans herror]

end Submission.Obl.k4_scalar_grid_parameter_preparation
