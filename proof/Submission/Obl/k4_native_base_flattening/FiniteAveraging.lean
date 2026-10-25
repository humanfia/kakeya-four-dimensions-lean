import Submission.Obl.k4_native_base_flattening.PolynomialAveraging

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Lib.K4ModelReduction
open scoped ENNReal

/-- Marginal-independent L1 estimate for a finite mixture of component densities. -/
theorem densityL1Distance_sum_le {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (f g : ι → X → ℝ)
    (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j)) :
    densityL1Distance μ (fun x => ∑ j, g j x) (fun x => ∑ j, f j x) ≤
      ∑ j, densityL1Distance μ (g j) (f j) := by
  classical
  unfold densityL1Distance
  calc
    _ ≤ ∫⁻ x, ∑ j, ENNReal.ofReal |g j x - f j x| ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← Finset.sum_sub_distrib]
      exact (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans_eq
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _))
    _ = _ := lintegral_finsetSum _
      (fun j _ => ENNReal.measurable_ofReal.comp ((hg j).sub (hf j)).abs)

/-- Uniform quantitative flattening of all the finitely many native source components.
The upper bound `T` controls the number, weights, supports and number of tests of the components. -/
theorem finite_native_flattening {m : ℕ}
    (T : ℝ) (hT : 1 ≤ T) (D : ℕ) (hm : (m : ℝ) ≤ T)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ T)
    (A : Fin m → Set (Fin 6 → ℝ)) (B : Fin m → Set (Fin 7 → ℝ))
    (hA : ∀ j, ∃ mA : ℕ, (mA : ℝ) ≤ T ∧
      ∃ pA : Fin mA → MvPolynomial (Fin 6) ℝ, (∀ a, (pA a).totalDegree ≤ D) ∧
      ∃ bA : (Fin mA → Bool) → Bool, ∀ a, a ∈ A j ↔
        bA (fun l => decide (0 ≤ MvPolynomial.eval a (pA l))) = true)
    (hB : ∀ j, ∃ mB : ℕ, (mB : ℝ) ≤ T ∧
      ∃ pB : Fin mB → MvPolynomial (Fin 7) ℝ, (∀ a, (pB a).totalDegree ≤ D) ∧
      ∃ bB : (Fin mB → Bool) → Bool, ∀ a, a ∈ B j ↔
        bB (fun l => decide (0 ≤ MvPolynomial.eval a (pB l))) = true)
    (hsA : ∀ j a, a ∈ A j → ∀ l, |a l| ≤ T)
    (hsB : ∀ j a, a ∈ B j → a 6 ∈ Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : (Fin 7 → ℝ) → ℝ, Measurable g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ T ^ 2) ∧
      (∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
        (∀ i ∈ baseCoordinates, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g x = g y) ∧
      supportedInCube g (2 * T + 3 * ρ) ∧
      densityL1Distance volume g (fun x => ∑ j, nativeComponentDensity (c j) (A j) (B j) x) ≤
        ENNReal.ofReal (98304 * (D : ℝ) * T ^ 9 * ρ) := by
  classical
  let e : ℝ := 24 * (D : ℝ) * T ^ 2 * ρ * (4 * T) ^ 6
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hcomp (j : Fin m) : ∃ g : (Fin 7 → ℝ) → ℝ,
      Measurable (nativeComponentDensity (c j) (A j) (B j)) ∧
      Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ c j) ∧
      (∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
        (∀ i ∈ baseCoordinates, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g x = g y) ∧
      supportedInCube g (2 * T + 3 * ρ) ∧
      densityL1Distance volume g (nativeComponentDensity (c j) (A j) (B j)) ≤
        ENNReal.ofReal e := by
    obtain ⟨mA, hmA, pA, hdA, bA, hfA⟩ := hA j
    obtain ⟨mB, hmB, pB, hdB, bB, hfB⟩ := hB j
    obtain ⟨g, hgm, hgb, _, hcell, hs, he⟩ :=
      native_component_flattening (c j) T (hc j).1 hT D (A j) (B j)
        pA pB bA bB hdA hdB hfA hfB (hsA j) (hsB j) hρ
    refine ⟨g, nativeComponentDensity_measurable _ _ _
      (measurableSet_of_polynomial_description _ _ _ hfA)
      (measurableSet_of_polynomial_description _ _ _ hfB), hgm, hgb, hcell, hs,
      he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hdeg : (((mA + mB) * D : ℕ) : ℝ) ≤ 2 * T * (D : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) D]
    calc
      _ ≤ 12 * T * (2 * T * (D : ℝ)) * ρ * (4 * T) ^ 6 := by gcongr; exact (hc j).2
      _ = e := by dsimp [e]; ring
  choose g hf hg hgb hcell hs he using hcomp
  refine ⟨fun x => ∑ j, g j x, Finset.measurable_sum _ (fun j _ => hg j), ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨Finset.sum_nonneg (fun j _ => (hgb j x).1), ?_⟩
    calc
      _ ≤ ∑ _j : Fin m, T := Finset.sum_le_sum (fun j _ => (hgb j x).2.trans (hc j).2)
      _ = (m : ℝ) * T := by simp
      _ ≤ T ^ 2 := by nlinarith
  · intro x y ho hb
    exact Finset.sum_congr rfl (fun j _ => hcell j x y ho hb)
  · intro x i hi
    exact Finset.sum_eq_zero (fun j _ => hs j x i hi)
  · calc
      _ ≤ ∑ j, densityL1Distance volume (g j) (nativeComponentDensity (c j) (A j) (B j)) :=
        densityL1Distance_sum_le volume _ _ hf hg
      _ ≤ ∑ _j : Fin m, ENNReal.ofReal e := Finset.sum_le_sum (fun j _ => he j)
      _ = ENNReal.ofReal ((m : ℝ) * e) := by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (T * e) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hm he0)
      _ = _ := by congr 1; dsimp [e]; ring

end Submission.Obl.k4_native_base_flattening
