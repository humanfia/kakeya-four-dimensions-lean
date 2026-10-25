import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport
import Submission.Obl.k4_tempered_grid_selection.Exponents

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A fixed polynomial chart bound also controls its inverse determinant. -/
lemma abs_det_le_entry_sum_sq (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    |Matrix.det Q| ≤ (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ^ 2 := by
  simp only [Matrix.det_fin_two, Fin.sum_univ_two]
  calc
    |Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0| ≤
        |Q 0 0| * |Q 1 1| + |Q 0 1| * |Q 1 0| := by
      simpa only [abs_mul] using abs_sub (Q 0 0 * Q 1 1) (Q 0 1 * Q 1 0)
    _ ≤ _ := by
      nlinarith [abs_nonneg (Q 0 0), abs_nonneg (Q 0 1),
        abs_nonneg (Q 1 0), abs_nonneg (Q 1 1),
        mul_nonneg (abs_nonneg (Q 0 0)) (abs_nonneg (Q 0 1)),
        mul_nonneg (abs_nonneg (Q 0 0)) (abs_nonneg (Q 1 0)),
        mul_nonneg (abs_nonneg (Q 0 1)) (abs_nonneg (Q 1 1)),
        mul_nonneg (abs_nonneg (Q 1 0)) (abs_nonneg (Q 1 1))]

lemma chart_width_lower {N κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set Point} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex : Prop}
    (hN : 0 < N) (hc : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    N ^ (-(2 * (M : ℝ))) ≤ |Matrix.det Q| * (4 : ℝ) ^ T := by
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ≤ N ^ M := by
    apply le_trans ?_ hc.2.2.1
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_left (abs_nonneg (Q i j))
  have hi := (abs_det_le_entry_sum_sq Q⁻¹).trans
    (pow_le_pow_left₀ (by positivity) hsum 2)
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv] at hi
  have hd : 0 < |Q.det| := abs_pos.mpr hc.1
  have hlo : ((N ^ M) ^ 2)⁻¹ ≤ |Q.det| :=
    (inv_le_comm₀ hd (by positivity)).mp hi
  have heq : ((N ^ M) ^ 2)⁻¹ = N ^ (-(2 * (M : ℝ))) := by
    rw [Real.rpow_neg hN.le, mul_comm (2 : ℝ), Real.rpow_mul hN.le,
      Real.rpow_natCast]
    simp only [Real.rpow_two]
  rw [heq] at hlo
  exact hlo.trans (le_mul_of_one_le_right hd.le (one_le_pow₀ (by norm_num)))

/-- A chart has an exact logarithmic width in a fixed polynomial interval.
The output interval is independent of the requested slack exponent. -/
lemma chart_log_width {N κ j r Bv τ : ℝ} {M D T : ℕ}
    {Ev : Set Point} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex : Prop}
    (hN : 1 < N) (hκ : 0 ≤ κ) (hκN : κ ≤ N ^ τ) (hτ : τ ≤ 1)
    (hc : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    ∃ v : ℝ, |v| ≤ (2 * M + 2 : ℕ) ∧
      N ^ (-v) = |Matrix.det Q| * (4 : ℝ) ^ T := by
  let width := |Matrix.det Q| * (4 : ℝ) ^ T
  let V : ℝ := (2 * M + 2 : ℕ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlo : N ^ (-V) ≤ width := by
    apply (Real.rpow_le_rpow_of_exponent_le hN.le (show -V ≤ -(2 * (M : ℝ)) by
      dsimp [V]; push_cast; linarith)).trans
    exact chart_width_lower (by linarith) hc
  have hhi : width ≤ N ^ V := by
    have hbound := (det_time_bound hκ hc).trans (pow_le_pow_left₀ hκ hκN 2)
    have hp : (N ^ τ) ^ 2 = N ^ (2 * τ) := by
      rw [← Real.rpow_natCast (N ^ τ) 2, ← Real.rpow_mul (by linarith : 0 ≤ N)]
      congr 1
      ring
    rw [hp] at hbound
    exact hbound.trans (Real.rpow_le_rpow_of_exponent_le hN.le (by
      dsimp [V]; push_cast; nlinarith))
  refine ⟨k4_tempered_grid_selection.boundedExponent V N width,
    k4_tempered_grid_selection.abs_boundedExponent V N width hV, ?_⟩
  rw [k4_tempered_grid_selection.boundedExponent_eq hN hlo hhi]
  exact k4_tempered_grid_selection.rpow_neg_logarithmicExponent hN
    ((Real.rpow_pos_of_pos (by linarith) _).trans_le hlo)

lemma width_exponent_lower {N width v w τ : ℝ} (hN : 1 < N)
    (hv : N ^ (-v) = width) (hwidth : width ≤ N ^ (-w + τ)) : w - τ ≤ v := by
  rw [← hv] at hwidth
  have := (Real.rpow_le_rpow_left_iff hN).1 hwidth
  linarith

end
end Submission.Obl.k4_raw_critical_segment_forests
