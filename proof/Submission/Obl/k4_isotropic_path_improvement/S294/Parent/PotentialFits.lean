-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.PotentialFits, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/PotentialFits.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSignal
import Submission.Lib.K4CubicTests.PolynomialPotential
import Submission.Lib.K4PolynomialNorming.WholeBlockLineField

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open Set MeasureTheory MvPolynomial
open scoped BigOperators

noncomputable section

namespace PotentialFits

abbrev Row := Fin 3 → MvPolynomial (Fin 3) ℝ

def direction (l : Ln) : Fin 3 → ℝ := ![1, l.2 3, l.2 4]

def clock (T : ℕ) : ℝ := ((2 : ℝ) ^ T)⁻¹

def start (T j : ℕ) : ℝ := (j : ℝ) * clock T

theorem clock_pos (T : ℕ) : 0 < clock T := by unfold clock; positivity

theorem packetBase_normalized (T j : ℕ) (c u : P2) (l : Ln) (s : ℝ) :
    (fun i => packetBase T j c u (l, start T j + clock T * s) i) =
      (fun i => packetBase T j c u (l, start T j) i) + s • direction l := by
  funext i
  fin_cases i
  · change (start T j + clock T * s - start T j) / clock T =
      (start T j - start T j) / clock T + s * 1
    field_simp [ne_of_gt (clock_pos T)]
    <;> ring
  · change (l.2 0 + (start T j + clock T * s) * l.2 3 -
      (c 0 + start T j * u 0)) / clock T =
      (l.2 0 + start T j * l.2 3 - (c 0 + start T j * u 0)) / clock T + s * l.2 3
    field_simp [ne_of_gt (clock_pos T)]
    <;> ring
  · change (l.2 1 + (start T j + clock T * s) * l.2 4 -
      (c 1 + start T j * u 1)) / clock T =
      (l.2 1 + start T j * l.2 4 - (c 1 + start T j * u 1)) / clock T + s * l.2 4
    field_simp [ne_of_gt (clock_pos T)]
    <;> ring

theorem hasDerivAt_base (T j : ℕ) (c u : P2) (l : Ln) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => packetBase T j c u (l, s) i) (direction l i / clock T) t := by
  fin_cases i
  · simpa [packetBase, start, clock, direction] using
      ((hasDerivAt_id t).sub_const ((j : ℝ) * clock T)).div_const (clock T)
  · simpa [packetBase, clock, xp, direction] using
      ((((hasDerivAt_id t).mul_const (l.2 3)).const_add (l.2 0)).sub_const
        (c 0 + ((j : ℝ) * clock T) * u 0)).div_const (clock T)
  · simpa [packetBase, clock, xp, direction] using
      ((((hasDerivAt_id t).mul_const (l.2 4)).const_add (l.2 1)).sub_const
        (c 1 + ((j : ℝ) * clock T) * u 1)).div_const (clock T)

/-- The accepted radial construction has bounded coefficients before any
packet clock is introduced. -/
theorem radial_coeff_le (T : Row) (D : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hT : ∀ i e, |(T i).coeff e| ≤ A) (e : Fin 3 →₀ ℕ) :
    |(Submission.Lib.K4CubicTests.polynomialRadialPotential T D).coeff e| ≤
      ((D + 1 : ℕ) : ℝ) * 3 * A := by
  classical
  unfold Submission.Lib.K4CubicTests.polynomialRadialPotential
  rw [coeff_sum]
  calc
    _ ≤ ∑ n ∈ Finset.range (D + 1),
      |(Submission.Lib.K4CubicTests.radialHomogeneousPotential
        (fun i => homogeneousComponent n (T i)) n).coeff e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (D + 1), 3 * A := by
      apply Finset.sum_le_sum
      intro n hn
      unfold Submission.Lib.K4CubicTests.radialHomogeneousPotential
      rw [coeff_C_mul, abs_mul]
      have hf : |((n : ℝ) + 1)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ (by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith)
      have hsum : |(∑ i : Fin 3, X i * homogeneousComponent n (T i)).coeff e| ≤ 3 * A := by
        rw [coeff_sum]
        calc
          _ ≤ ∑ i : Fin 3, |(X i * homogeneousComponent n (T i)).coeff e| :=
            Finset.abs_sum_le_sum_abs
              (fun i : Fin 3 => (X i * homogeneousComponent n (T i)).coeff e) Finset.univ
          _ ≤ ∑ _i : Fin 3, A := by
            apply Finset.sum_le_sum
            intro i hi
            rw [coeff_X_mul']
            split_ifs
            · rw [coeff_homogeneousComponent]
              split_ifs
              · exact hT i _
              · simpa using hA
            · simpa using hA
          _ = 3 * A := by simp
      simpa only [one_mul] using mul_le_mul hf hsum
        (abs_nonneg ((∑ i : Fin 3, X i * homogeneousComponent n (T i)).coeff e)) zero_le_one
    _ = ((D + 1 : ℕ) : ℝ) * 3 * A := by simp; ring

/-- `clock * Q` is a potential in physical height units. Its derivative
along the normalized packet base has no inverse-clock cost. -/
theorem hasDerivAt_scaled_potential (T j : ℕ) (c u : P2) (l : Ln)
    (Q : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt
      (fun s => eval (fun i => packetBase T j c u (l, s) i) (C (clock T) * Q))
      (∑ i : Fin 3, eval (fun i => packetBase T j c u (l, t) i) (pderiv i Q) * direction l i) t := by
  have hd := Submission.Lib.K4CubicTests.hasDerivAt_eval_finite_polynomial_curve
    Q (fun s i => packetBase T j c u (l, s) i) (fun i => direction l i / clock T) t
    (fun i => hasDerivAt_base T j c u l i t)
  have heq : clock T * (∑ i : Fin 3,
      eval (fun i => packetBase T j c u (l, t) i) (pderiv i Q) *
        (direction l i / clock T)) =
      ∑ i : Fin 3, eval (fun i => packetBase T j c u (l, t) i) (pderiv i Q) * direction l i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (clock_pos T)]
  simpa only [map_mul, eval_C, heq] using hd.const_mul (clock T)

end PotentialFits

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
