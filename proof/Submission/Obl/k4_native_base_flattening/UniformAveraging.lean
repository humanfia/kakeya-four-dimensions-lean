import Submission.Obl.k4_native_base_flattening.FiniteAveraging
import Submission.Obl.k4_native_base_flattening.Powers

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Lib.K4ModelReduction
open scoped ENNReal

/-- The sum of the sheared component densities in a polynomial-format native law. -/
def NativeMixtureFormat (n : ℝ) (M D : ℕ) (f : (Fin 7 → ℝ) → ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ)
    (A : Fin m → Set (Fin 6 → ℝ)) (B : Fin m → Set (Fin 7 → ℝ)),
    (m : ℝ) ≤ n ^ M ∧ (∀ j, 0 ≤ c j ∧ c j ≤ n ^ M) ∧
    (∀ j, ∃ mA : ℕ, (mA : ℝ) ≤ n ^ M ∧
      ∃ pA : Fin mA → MvPolynomial (Fin 6) ℝ, (∀ a, (pA a).totalDegree ≤ D) ∧
      ∃ bA : (Fin mA → Bool) → Bool, ∀ a, a ∈ A j ↔
        bA (fun l => decide (0 ≤ MvPolynomial.eval a (pA l))) = true) ∧
    (∀ j, ∃ mB : ℕ, (mB : ℝ) ≤ n ^ M ∧
      ∃ pB : Fin mB → MvPolynomial (Fin 7) ℝ, (∀ a, (pB a).totalDegree ≤ D) ∧
      ∃ bB : (Fin mB → Bool) → Bool, ∀ a, a ∈ B j ↔
        bB (fun l => decide (0 ≤ MvPolynomial.eval a (pB l))) = true) ∧
    (∀ j a, a ∈ A j → ∀ l, |a l| ≤ n ^ M) ∧
    (∀ j a, a ∈ B j → a 6 ∈ Icc (0 : ℝ) 1) ∧
    f = fun x => ∑ j, nativeComponentDensity (c j) (A j) (B j) x

/-- One polynomial mesh works for all resolutions and all component data with the fixed
format exponents. The approximation error can be made any specified inverse power. -/
theorem uniform_native_flattening (M D q : ℕ) :
    ∃ H : ℕ, ∀ n : ℝ, 2 ≤ n → ∀ f : (Fin 7 → ℝ) → ℝ,
      NativeMixtureFormat n M D f →
      ∃ g : (Fin 7 → ℝ) → ℝ, Measurable g ∧
        (∀ x, 0 ≤ g x ∧ g x ≤ n ^ (2 * M)) ∧
        (∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
          (∀ i ∈ baseCoordinates, ⌊n ^ H * x i⌋ = ⌊n ^ H * y i⌋) → g x = g y) ∧
        supportedInCube g (n ^ (M + 3)) ∧
        densityL1Distance volume g f ≤ ENNReal.ofReal ((n ^ q)⁻¹) := by
  obtain ⟨H, hH⟩ := exists_uniform_mesh_exponent M (98304 * (D : ℝ)) q
  refine ⟨H, ?_⟩
  intro n hn f hf
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hT : 1 ≤ n ^ M := one_le_pow₀ hn1
  let ρ : ℝ := (n ^ H)⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (hH n hn).2
  rcases hf with ⟨m, c, A, B, hm, hc, hA, hB, hsA, hsB, rfl⟩
  obtain ⟨g, hg, hgb, hcell, hs, he⟩ := finite_native_flattening
    (n ^ M) hT D hm c hc A B hA hB hsA hsB hρ
  refine ⟨g, hg, ?_, ?_, ?_, he.trans (ENNReal.ofReal_le_ofReal (hH n hn).1)⟩
  · intro x
    refine ⟨(hgb x).1, (hgb x).2.trans_eq ?_⟩
    rw [← pow_mul]
    congr 1
    omega
  · intro x y ho hb
    apply hcell x y ho
    intro i hi
    simpa only [ρ, div_inv_eq_mul, mul_comm] using hb i hi
  · have h5 : (5 : ℝ) ≤ n ^ 3 := by
      calc
        (5 : ℝ) ≤ 2 ^ 3 := by norm_num
        _ ≤ n ^ 3 := pow_le_pow_left₀ (by norm_num) hn _
    have hR : 2 * n ^ M + 3 * ρ ≤ n ^ (M + 3) := by
      rw [pow_add]
      nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ n ^ M)]
    intro x i hi
    exact hs x i (lt_of_le_of_lt hR hi)

end Submission.Obl.k4_native_base_flattening
