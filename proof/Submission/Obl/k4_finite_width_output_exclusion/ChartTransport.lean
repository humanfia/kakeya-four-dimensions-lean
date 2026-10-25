import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma delta_pos (N r : ℝ) : 0 < δ N r := by
  exact k4_profile_density_bounds.width_pos N r

lemma delta_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  k4_profile_density_bounds.width_bounds hN r

lemma fmt_mono {n D : ℕ} {H H' : ℝ} {A : Set (Fin n → ℝ)}
    (h : H ≤ H') (hf : fmt n H D A) : fmt n H' D A := by
  rcases hf with ⟨m, hm, p, hp, b, hb⟩
  exact ⟨m, hm.trans h, p, hp, b, hb⟩

lemma chart_transport {N N' κ κ' j r r' Bv : ℝ} {M M' D T : ℕ}
    {Ev : Set Point} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex ex' : Prop}
    (hbound : N ^ M ≤ N' ^ M') (hκ : 0 < κ) (hκκ : κ ≤ κ') (hB : 0 ≤ Bv)
    (hvalue : κ * δ N r ≤ κ' * δ N' r')
    (hcurve : κ / δ N r ≤ κ' / δ N' r') (hex : ex → ex')
    (hc : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    chart N' M' D κ' T j r' Bv Ev c u Q R A F ex' := by
  rcases hc with ⟨hdet, hcu, hQ, hQs, hdeg, hcoeff, hA, hF, hfmt, htraj, hsel, hx⟩
  refine ⟨hdet, hcu.trans hbound, hQ.trans hbound, ?_, hdeg,
    fun b => (hcoeff b).trans hbound, hA, hF, ?_, ?_, ?_, hex hx⟩
  · exact hQs.trans (div_le_div_of_nonneg_right hκκ (by positivity))
  · intro i
    exact ⟨fmt_mono hbound (hfmt i).1, fmt_mono hbound (hfmt i).2⟩
  · intro l hl
    refine ⟨(htraj l hl).1.trans hbound,
      fun e => ((htraj l hl).2.1 e).trans hbound, ?_⟩
    intro t ht
    rcases (htraj l hl).2.2 t ht with ⟨h1, h2, h3, h4⟩
    refine ⟨h1.trans hκκ, h2.trans hvalue,
      h3.trans (mul_le_mul_of_nonneg_right hκκ hB), ?_⟩
    apply h4.trans
    convert mul_le_mul_of_nonneg_right hcurve (sq_nonneg Bv) using 1 <;> ring
  · intro p hp
    rcases hsel p hp with ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    exact (div_le_div_of_nonneg_left hB hκ hκκ).trans h4

lemma chart_enlarge {N κ κ' j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set Point} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex ex' : Prop}
    (hκ : 0 < κ) (hκκ : κ ≤ κ') (hB : 0 ≤ Bv) (hex : ex → ex')
    (hc : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    chart N M D κ' T j r Bv Ev c u Q R A F ex' :=
  chart_transport le_rfl hκ hκκ hB
    (mul_le_mul_of_nonneg_right hκκ (delta_pos N r).le)
    (div_le_div_of_nonneg_right hκκ (delta_pos N r).le) hex hc

lemma det_time_bound {N κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set Point} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex : Prop}
    (hκ : 0 ≤ κ) (hc : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ κ ^ 2 := by
  have hsum := hc.2.2.2.1
  have hQ : |Matrix.det Q| ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ^ 2 := by
    simp only [Matrix.det_fin_two, Fin.sum_univ_two]
    calc
      |Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0| ≤
          |Q 0 0| * |Q 1 1| + |Q 0 1| * |Q 1 0| := by
        simpa only [abs_mul] using abs_sub (Q 0 0 * Q 1 1) (Q 0 1 * Q 1 0)
      _ ≤ (|Q 0 0| + |Q 0 1| + (|Q 1 0| + |Q 1 1|)) ^ 2 := by
        nlinarith [abs_nonneg (Q 0 0), abs_nonneg (Q 0 1),
          abs_nonneg (Q 1 0), abs_nonneg (Q 1 1),
          mul_nonneg (abs_nonneg (Q 0 0)) (abs_nonneg (Q 0 1)),
          mul_nonneg (abs_nonneg (Q 0 0)) (abs_nonneg (Q 1 0)),
          mul_nonneg (abs_nonneg (Q 0 1)) (abs_nonneg (Q 1 1)),
          mul_nonneg (abs_nonneg (Q 1 0)) (abs_nonneg (Q 1 1))]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) hsum 2
  have hid : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
    rw [← pow_mul, mul_comm T 2, pow_mul]
    norm_num
  calc
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ (κ / (2 : ℝ) ^ T) ^ 2 * (4 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_right (hQ.trans hsq) (by positivity)
    _ = κ ^ 2 := by rw [hid]; field_simp

end
end Submission.Obl.k4_finite_width_output_exclusion
