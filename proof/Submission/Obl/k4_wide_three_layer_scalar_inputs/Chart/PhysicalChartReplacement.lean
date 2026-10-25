/- Adapted from this LOT tree o218, branch x0760, commit 5db19453bd17cc371d54c5ac350db64cdc0ec595,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/PhysicalChartReplacement.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.ChartReplacement
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MvPolynomial

private noncomputable def wideQuadraticExponent : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
    Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2]

private noncomputable def wideQuadraticPolynomial (G : Fin 6 → ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ i : Fin 6, monomial (wideQuadraticExponent i) (G i)

private theorem eval_wideQuadraticPolynomial (G : Fin 6 → ℝ) (t Y : ℝ) :
    eval ![t, Y] (wideQuadraticPolynomial G) =
      G 0 + G 1 * t + G 2 * Y + G 3 * t ^ 2 + G 4 * (t * Y) + G 5 * Y ^ 2 := by
  simp [wideQuadraticPolynomial, wideQuadraticExponent, Fin.sum_univ_succ,
    eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, add_assoc]

private theorem coeff_yy_wideQuadraticPolynomial (G : Fin 6 → ℝ) :
    (wideQuadraticPolynomial G).coeff (Finsupp.single 1 2) = G 5 := by
  norm_num [wideQuadraticPolynomial, wideQuadraticExponent, Fin.sum_univ_succ,
    coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two]

private theorem wideQuadraticExponent_injective :
    Function.Injective wideQuadraticExponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [wideQuadraticExponent, Finsupp.ext_iff, Fin.forall_fin_two] at *

private theorem coeff_wideQuadraticPolynomial (G : Fin 6 → ℝ) (i : Fin 6) :
    (wideQuadraticPolynomial G).coeff (wideQuadraticExponent i) = G i := by
  classical
  simp [wideQuadraticPolynomial, coeff_monomial, wideQuadraticExponent_injective.eq_iff]

private theorem wideQuadraticPolynomial_of_evaluation (P : MvPolynomial (Fin 2) ℝ)
    (G : Fin 6 → ℝ)
    (hG : ∀ t Y, eval ![t, Y] P =
      G 0 + G 1 * t + G 2 * Y + G 3 * t ^ 2 + G 4 * (t * Y) + G 5 * Y ^ 2) :
    P = wideQuadraticPolynomial G := by
  apply MvPolynomial.funext
  intro z
  have hz : (![z 0, z 1] : Fin 2 → ℝ) = z := by
    funext i
    fin_cases i <;> rfl
  calc
    eval z P = eval ![z 0, z 1] P := by rw [hz]
    _ = _ := hG _ _
    _ = eval ![z 0, z 1] (wideQuadraticPolynomial G) :=
      (eval_wideQuadraticPolynomial G _ _).symm
    _ = eval z (wideQuadraticPolynomial G) := by rw [hz]

/-- A physical quadratic representation has the original polynomial's exact
Y-squared coefficient; no new coefficient bound is being assumed. -/
theorem quadratic_representation_coeff_yy (P : MvPolynomial (Fin 2) ℝ)
    (G : Fin 6 → ℝ)
    (hG : ∀ t Y, eval ![t, Y] P =
      G 0 + G 1 * t + G 2 * Y + G 3 * t ^ 2 + G 4 * (t * Y) + G 5 * Y ^ 2) :
    G 5 = P.coeff (Finsupp.single 1 2) := by
  rw [wideQuadraticPolynomial_of_evaluation P G hG, coeff_yy_wideQuadraticPolynomial]

/-- Every coefficient in any valid physical representation inherits its
bound from the ORIGINAL physical polynomial coefficient. -/
theorem quadratic_representation_coeff_bound (P : MvPolynomial (Fin 2) ℝ)
    (G : Fin 6 → ℝ)
    (hG : ∀ t Y, eval ![t, Y] P =
      G 0 + G 1 * t + G 2 * Y + G 3 * t ^ 2 + G 4 * (t * Y) + G 5 * Y ^ 2)
    {B : ℝ} (hB : ∀ d, |P.coeff d| ≤ B) : ∀ i, |G i| ≤ B := by
  intro i
  have h := hB (wideQuadraticExponent i)
  rw [wideQuadraticPolynomial_of_evaluation P G hG, coeff_wideQuadraticPolynomial] at h
  exact h

/-- The actual linear U coefficient is read from physical evaluations. The
constant and linear-in-base parts of the native affine field cancel. -/
noncomputable def physicalTransverseLinear (P : MvPolynomial (Fin 2) ℝ)
    (c : Fin 5 → ℝ) (nativeSlope a m t Z : ℝ) : ℝ :=
  (eval ![t, c 2 + t * c 3 + c 4 * Z + m] P -
    eval ![t, c 2 + t * c 3 + c 4 * Z - m] P - 2 * m * nativeSlope) / (2 * a)

/-- This physical coefficient agrees exactly with any valid six-coefficient
quadratic representation, including the one returned by the accepted API. -/
theorem physicalTransverseLinear_eq (P : MvPolynomial (Fin 2) ℝ) (G : Fin 6 → ℝ)
    (hG : ∀ t Y, eval ![t, Y] P =
      G 0 + G 1 * t + G 2 * Y + G 3 * t ^ 2 + G 4 * (t * Y) + G 5 * Y ^ 2)
    (c : Fin 5 → ℝ) {nativeSlope a m t Z : ℝ} (ha : a ≠ 0) :
    physicalTransverseLinear P c nativeSlope a m t Z =
      transverseLinear G c nativeSlope a m t Z := by
  simp only [physicalTransverseLinear, hG, transverseLinear]
  field_simp
  <;> ring

/-- The actual polynomial coefficient bound supplies the chart-replacement
estimate directly. Its representation is obtained by IMPORTING the accepted
quadratic-evaluation theorem. -/
theorem eventually_physical_transverse_chart_replacement
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    {s₀ sp κ M : ℝ} (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2)
    (hκ : κ ≤ 1) (hM : 100 * s₀ < M) :
    ∀ᶠ k in Filter.atTop, ∀ η : ℝ, η ≤ s₀ →
      ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ 2 →
      ∀ (c : Fin 5 → ℝ) (nativeSlope m t Z Z' : ℝ),
      0 ≤ m → m ≤ 1 →
      |P.coeff (Finsupp.single 1 2)| ≤ N k ^ (4 * κ * s₀ + η) →
      |c 4| ≤ N k ^ η → |Z - Z'| ≤ 2 * N k ^ (-M) →
      |physicalTransverseLinear P c nativeSlope (N k ^ (-sp)) m t Z -
        physicalTransverseLinear P c nativeSlope (N k ^ (-sp)) m t Z'| ≤ N k ^ (-M / 2) := by
  filter_upwards [eventually_transverse_chart_replacement N hN hNt hs₀ hsp hκ hM] with k hk
  intro η hη P hP c nativeSlope m t Z Z' hm hm1 hPcoeff hc hZ
  obtain ⟨G, hG⟩ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.isQuad2_eval P hP
  have ha : N k ^ (-sp) ≠ 0 := (Real.rpow_pos_of_pos (by linarith [hN k]) _).ne'
  rw [physicalTransverseLinear_eq P G hG c ha,
    physicalTransverseLinear_eq P G hG c ha]
  exact hk η hη G c nativeSlope m t Z Z' hm hm1
    (by rw [quadratic_representation_coeff_yy P G hG]; exact hPcoeff) hc hZ

end Submission.Obl.k4_wide_three_layer_scalar_inputs
