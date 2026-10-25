/- Adapted from this LOT tree, o197, session x0690, Pairing/VelocityPinning.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
/- Adapted from this LOT tree, o178, session x0596, commit aff0309c5b5be9920172fe7e367c31d64a3a01e3;
   Submission/Obl/k4_unbounded_geometric_packet_reduction/VelocityPinning.lean.
   The original file and its provenance are preserved below. -/
import Mathlib

/-!
# Two transverse normal constraints pin a planar vector

If two unit normals are separated (modulo sign) by more than `θ`, then the two
scalar constraints `|⟪n₁, w⟫| ≤ a` and `|⟪n₂, w⟫| ≤ b` force `‖w‖ ≤ 4 (a + b) / θ`.
This is the elementary geometry behind the angle-failure estimate of the
full-time localization (paper, Section 10, proof of Proposition 10.2): a
trajectory whose velocity satisfies two transverse chart strips has its
velocity pinned to a small ball.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing

open Real

noncomputable section

/-- The planar cross product of two vectors of `ℝ²`. -/
def cross2 (n m : EuclideanSpace ℝ (Fin 2)) : ℝ := n 0 * m 1 - n 1 * m 0

theorem inner_fin2 (n w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ n w = n 0 * w 0 + n 1 * w 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
  ring

theorem norm_sq_fin2' (n : EuclideanSpace ℝ (Fin 2)) : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

/-- Cramer's rule for the two constraints. -/
theorem cross2_mul_coord0 (n m w : EuclideanSpace ℝ (Fin 2)) :
    cross2 n m * w 0 = inner ℝ n w * m 1 - inner ℝ m w * n 1 := by
  rw [inner_fin2, inner_fin2, cross2]; ring

theorem cross2_mul_coord1 (n m w : EuclideanSpace ℝ (Fin 2)) :
    cross2 n m * w 1 = inner ℝ m w * n 0 - inner ℝ n w * m 0 := by
  rw [inner_fin2, inner_fin2, cross2]; ring

theorem norm_le_abs_add_abs_fin2 (w : EuclideanSpace ℝ (Fin 2)) : ‖w‖ ≤ |w 0| + |w 1| := by
  have h := norm_sq_fin2' w
  have h0 : 0 ≤ |w 0| + |w 1| := by positivity
  rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  rw [h]
  nlinarith [sq_abs (w 0), sq_abs (w 1), abs_nonneg (w 0), abs_nonneg (w 1),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1))]

theorem abs_coord_le_norm_fin2 (n : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |n i| ≤ ‖n‖ := by
  have := norm_sq_fin2' n
  rw [← Real.sqrt_sq (abs_nonneg (n i)), ← Real.sqrt_sq (norm_nonneg n)]
  apply Real.sqrt_le_sqrt
  rw [this, sq_abs]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]

/-- For unit vectors, the squared cross product is `‖n - m‖² ‖n + m‖² / 4`. -/
theorem cross2_sq_unit {n m : EuclideanSpace ℝ (Fin 2)} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) :
    cross2 n m ^ 2 = ‖n - m‖ ^ 2 * ‖n + m‖ ^ 2 / 4 := by
  have hn2 := norm_sq_fin2' n
  have hm2 := norm_sq_fin2' m
  have hs := norm_sq_fin2' (n - m)
  have ha := norm_sq_fin2' (n + m)
  rw [hn] at hn2; rw [hm] at hm2
  simp only [PiLp.sub_apply, PiLp.add_apply] at hs ha
  rw [hs, ha, cross2]
  nlinarith [hn2, hm2]

/-- Separation modulo sign bounds the cross product from below. -/
theorem cross2_sq_lower {n m : EuclideanSpace ℝ (Fin 2)} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (hsep : θ < min ‖n - m‖ ‖n + m‖) :
    θ ^ 2 / 2 ≤ cross2 n m ^ 2 := by
  rw [cross2_sq_unit hn hm]
  have h1 : θ < ‖n - m‖ := lt_of_lt_of_le hsep (min_le_left _ _)
  have h2 : θ < ‖n + m‖ := lt_of_lt_of_le hsep (min_le_right _ _)
  have hn2 := norm_sq_fin2' n
  have hm2 := norm_sq_fin2' m
  have hs := norm_sq_fin2' (n - m)
  have ha := norm_sq_fin2' (n + m)
  rw [hn] at hn2; rw [hm] at hm2
  simp only [PiLp.sub_apply, PiLp.add_apply] at hs ha
  -- the two squared norms sum to four
  have hsum : ‖n - m‖ ^ 2 + ‖n + m‖ ^ 2 = 4 := by rw [hs, ha]; nlinarith
  have hθ1 : θ ^ 2 ≤ ‖n - m‖ ^ 2 := by nlinarith [norm_nonneg (n - m)]
  have hθ2 : θ ^ 2 ≤ ‖n + m‖ ^ 2 := by nlinarith [norm_nonneg (n + m)]
  -- one of the two squared norms is at least two
  rcases le_total 2 (‖n - m‖ ^ 2) with h | h
  · nlinarith [sq_nonneg θ]
  · have h' : 2 ≤ ‖n + m‖ ^ 2 := by linarith
    nlinarith [sq_nonneg θ]

/-- Two transverse normal constraints pin a planar vector. -/
theorem norm_le_of_two_normals {n m w : EuclideanSpace ℝ (Fin 2)}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) {θ a b : ℝ} (hθ : 0 < θ)
    (hsep : θ < min ‖n - m‖ ‖n + m‖)
    (ha : |inner ℝ n w| ≤ a) (hb : |inner ℝ m w| ≤ b) :
    ‖w‖ ≤ 4 * (a + b) / θ := by
  have hlow := cross2_sq_lower hn hm hθ.le hsep
  have hcross : θ / 2 ≤ |cross2 n m| := by
    by_contra h
    push Not at h
    have h0 := abs_nonneg (cross2 n m)
    have : |cross2 n m| ^ 2 < (θ / 2) ^ 2 := by nlinarith
    rw [sq_abs] at this
    nlinarith
  have hcpos : 0 < |cross2 n m| := lt_of_lt_of_le (by positivity) hcross
  have hn0 := abs_coord_le_norm_fin2 n 0
  have hn1 := abs_coord_le_norm_fin2 n 1
  have hm0 := abs_coord_le_norm_fin2 m 0
  have hm1 := abs_coord_le_norm_fin2 m 1
  rw [hn] at hn0 hn1; rw [hm] at hm0 hm1
  have ha0 : 0 ≤ a := (abs_nonneg _).trans ha
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hb
  -- each coordinate is at most (a + b) / |cross|
  have hc0 : |cross2 n m| * |w 0| ≤ a + b := by
    rw [← abs_mul, cross2_mul_coord0]
    calc |inner ℝ n w * m 1 - inner ℝ m w * n 1|
        ≤ |inner ℝ n w| * |m 1| + |inner ℝ m w| * |n 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = a + b := by ring
  have hc1 : |cross2 n m| * |w 1| ≤ a + b := by
    rw [← abs_mul, cross2_mul_coord1]
    calc |inner ℝ m w * n 0 - inner ℝ n w * m 0|
        ≤ |inner ℝ m w| * |n 0| + |inner ℝ n w| * |m 0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ b * 1 + a * 1 := by gcongr
      _ = a + b := by ring
  have hw := norm_le_abs_add_abs_fin2 w
  have key : |cross2 n m| * ‖w‖ ≤ 2 * (a + b) := by nlinarith [abs_nonneg (w 0), abs_nonneg (w 1)]
  rw [le_div_iff₀ hθ]
  nlinarith [norm_nonneg w]

end

end Submission.Obl.k4_raw_localized_native_systems.Pairing
