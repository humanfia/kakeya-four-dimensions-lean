-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/TransportBounds.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/TransportBounds.lean.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.AffineTransport
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.CoefficientBounds

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

open MvPolynomial

lemma coefficientMass_coordinateSubstitution_le (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hc : ∀ i, |c i| ≤ H) (hM : ∀ i j, |M i j| ≤ H) (hB : |B| ≤ H)
    (i : Fin 4) : coefficientMass (coordinateSubstitution c M B i) ≤ 4 * H := by
  have hlin (a : ℝ) (j : Fin 4) : coefficientMass (C a * X j : Poly) ≤ |a| := by
    simpa using coefficientMass_mul_le (C a : Poly) (X j)
  have hbase (a : ℝ) (v : Fin 3 → ℝ) (ha : |a| ≤ H) (hv : ∀ j, |v j| ≤ H) :
      coefficientMass (C a + ∑ j : Fin 3, C (v j) * X j.castSucc : Poly) ≤ 4 * H := by
    calc
      coefficientMass (C a + ∑ j : Fin 3, C (v j) * X j.castSucc : Poly)
          ≤ coefficientMass (C a : Poly) +
            coefficientMass (∑ j : Fin 3, C (v j) * X j.castSucc : Poly) :=
        coefficientMass_add_le _ _
      _ ≤ H + ∑ j : Fin 3, H := by
        apply add_le_add
        · simpa using ha
        · exact (coefficientMass_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => (hlin _ _).trans (hv j))
      _ = 4 * H := by simp; ring
  fin_cases i
  · exact hbase _ _ (hc 0) (hM 0)
  · exact hbase _ _ (hc 1) (hM 1)
  · exact hbase _ _ (hc 2) (hM 2)
  · exact (hlin _ _).trans (hB.trans (by linarith))

/-- Affine transport of a quadratic has a uniform cubic coefficient budget. -/
theorem transportPolynomial_coeff_bound (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly)
    {H Z : ℝ} (hH : 1 ≤ H) (hZ : 0 ≤ Z)
    (hc : ∀ i, |c i| ≤ H) (hM : ∀ i j, |M i j| ≤ H) (hB : |B| ≤ H)
    (hdeg : P.totalDegree ≤ 2) (hcoeff : ∀ e, |P.coeff e| ≤ Z)
    (e : Fin 4 →₀ ℕ) :
    |(transportPolynomial c M B P).coeff e| ≤ 1296 * Z * H ^ 2 := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have h4H : 1 ≤ 4 * H := by linarith
  calc
    |(transportPolynomial c M B P).coeff e|
        ≤ coefficientMass (transportPolynomial c M B P) := abs_coeff_le_coefficientMass _ _
    _ ≤ coefficientMass P * (4 * H) ^ P.totalDegree :=
      coefficientMass_bind_le _ _ h4H
        (coefficientMass_coordinateSubstitution_le c M B hH0 hc hM hB)
    _ ≤ (81 * Z) * (4 * H) ^ 2 := by
      apply mul_le_mul
      · simpa using coefficientMass_le_of_degree P hdeg hZ hcoeff
      · exact pow_le_pow_right₀ h4H hdeg
      · positivity
      · positivity
    _ = 1296 * Z * H ^ 2 := by ring

/-- The coefficient exponent depends on the original format and the universal
restoration exponent; it can therefore be fixed before final asymptotic slack. -/
theorem transportPolynomial_coeff_power_bound (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (P : Poly)
    {N : ℝ} (hN : 2 ≤ N) (a b : ℕ)
    (hc : ∀ i, |c i| ≤ N ^ b) (hM : ∀ i j, |M i j| ≤ N ^ b)
    (hB : |B| ≤ N ^ b) (hdeg : P.totalDegree ≤ 2)
    (hcoeff : ∀ e, |P.coeff e| ≤ N ^ a) (e : Fin 4 →₀ ℕ) :
    |(transportPolynomial c M B P).coeff e| ≤ N ^ (a + 2 * b + 11) := by
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hconst : (1296 : ℝ) ≤ N ^ 11 := by
    exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 11)
  calc
    |(transportPolynomial c M B P).coeff e|
        ≤ 1296 * N ^ a * (N ^ b) ^ 2 :=
      transportPolynomial_coeff_bound c M B P (one_le_pow₀ hN1) (by positivity)
        hc hM hB hdeg hcoeff e
    _ ≤ N ^ 11 * N ^ a * (N ^ b) ^ 2 := by gcongr
    _ = N ^ (a + 2 * b + 11) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
