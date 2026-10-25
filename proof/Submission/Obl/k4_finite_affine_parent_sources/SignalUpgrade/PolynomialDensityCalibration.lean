-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/PolynomialDensityCalibration.lean.
-- Only the namespace and own-module import prefix are changed here.
-- From this same obligation, x0734, commit bcc5fc2c; power rewrite repaired by x0735.
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration

/-! Fixed polynomial density losses require only a fixed enlargement of the
base-mesh exponent. All thresholds precede the law and the polynomial. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

open MeasureTheory Set
open scoped ENNReal

/-- Quadratic coefficients have a fixed polynomial bound when the base
cap divided by the retained mass has a fixed polynomial bound. -/
theorem polynomial_density_grid_calibration (B : ℝ) (hB : 0 ≤ B) :
    ∃ a M N₀ : ℝ, 0 < a ∧ 1 ≤ M ∧ 2 ≤ N₀ ∧
      ∀ N K β m E : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N →
        0 < β → 0 < m → β / m ≤ N ^ B → 0 ≤ E →
        ∀ (μ : Measure (Fin 3 → ℝ)), IsFiniteMeasure μ →
          ENNReal.ofReal m ≤ μ univ →
          (∀ q : Fin 3 → ℤ, μ {z | (fun i => ⌊z i / N ^ (-a)⌋) = q} ≤
            ENNReal.ofReal (β * (N ^ (-a)) ^ (3 : ℕ))) →
          ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
            (∀ᵐ z ∂μ, (∀ i, |z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E) →
            ∀ e, |G.coeff e| ≤ N ^ M * E := by
  obtain ⟨C, hC, hcal⟩ := Submission.k4_quadratic_mesh_coefficient_calibration
  let M : ℝ := 1 + 2 * C + 6 * (B + 1)
  refine ⟨M + 1, M, max 2 C, ?_, ?_, le_max_left _ _, ?_⟩
  · dsimp [M]
    linarith
  · dsimp [M]
    linarith
  intro N K β m E hN hK hKN hβ hm hratio hE μ hfin hmass hcap G hG hgood e
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hCN : C ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hNB : 1 ≤ N ^ B := Real.one_le_rpow hN1 hB
  have hbase : 1 + K ≤ N ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hratio' : 1 + β / m ≤ N ^ (B + 1) := by
    calc
      _ ≤ 2 * N ^ B := by linarith
      _ ≤ N * N ^ B := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = N ^ (B + 1) := by rw [Real.rpow_add hNpos, Real.rpow_one]; ring
  have hpowC : (1 + K) ^ C ≤ N ^ (2 * C) := by
    calc
      _ ≤ (N ^ (2 : ℝ)) ^ C := Real.rpow_le_rpow (by linarith) hbase (by linarith)
      _ = _ := (Real.rpow_mul hNpos.le _ _).symm
  have hpow6 : (1 + β / m) ^ (6 : ℕ) ≤ N ^ (6 * (B + 1)) := by
    calc
      _ ≤ (N ^ (B + 1)) ^ (6 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hratio' _
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
  have hcost : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) ≤ N ^ M := by
    calc
      _ ≤ N * N ^ (2 * C) * N ^ (6 * (B + 1)) := by gcongr
      _ = N ^ (1 : ℝ) * N ^ (2 * C) * N ^ (6 * (B + 1)) := by
        rw [Real.rpow_one]
      _ = N ^ M := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  have hsmall : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * N ^ (-(M + 1)) ≤ 1 / 2 := by
    calc
      _ ≤ N ^ M * N ^ (-(M + 1)) :=
        mul_le_mul_of_nonneg_right hcost (by positivity)
      _ = N ^ (-1 : ℝ) := by rw [← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one]
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hN2
  exact (hcal K β m E (N ^ (-(M + 1))) hK hβ hm hE (by positivity)
    hsmall μ hfin hmass hcap G hG hgood e).trans
      (mul_le_mul_of_nonneg_right hcost hE)

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
