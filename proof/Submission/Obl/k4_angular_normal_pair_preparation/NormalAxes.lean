-- Adapted from this LOT tree, o104, session x0472, commit 48795996,
-- Submission/Obl/k4_terminal_time_extension/ChartAxes.lean (principal axes) and
-- Submission/Obl/k4_terminal_time_extension/FrameBounds.lean (`velocity_inter_subset_ball`).
-- The definitions `col0`, `col1`, `longCol`, `r₁`, `r₂`, `nrm`, `wedge` are the frozen ones
-- of `Definitions.lean` (x0770); the lemmas are restated for them.
import Submission.Obl.k4_angular_normal_pair_preparation.Definitions
import Submission.Lib.K4VelocityStrips.StripIntersections

/-!
# Principal axes of an old chart and separated normals

For an invertible `2 × 2` chart matrix `Q`, `longCol Q` is its longer column, `r₁ Q` its
length, `nrm Q` the unit vector perpendicular to it and `r₂ Q = |det Q| / r₁ Q`.  Every
image `Q g` has normal component at most `‖g‖ r₂ Q`.  Two velocity ellipses
`{w | ‖Q⁻¹ (w - u)‖ ≤ W}` whose normals are separated (`g ≤ |wedge|`) therefore meet
inside a closed ball of radius `8 W max(r₂ Q, r₂ Q') / g`.
-/

namespace Submission.Obl.k4_angular_normal_pair_preparation

open Matrix Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

/-- Unfolding lemmas for the frozen trajectory, observation and depth definitions. -/
theorem x_def (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    x l t = ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] := rfl

theorem y_def (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : y l t = WithLp.toLp 2 ![(x l t) 1, (x l t) 2] := rfl

theorem v_def (l : ℕ × (Fin 6 → ℝ)) : v l = WithLp.toLp 2 ![l.2 3, l.2 4] := rfl

theorem obs_def (B a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    obs B a p = (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋) := rfl

theorem δ_def (N r : ℝ) : δ N r = (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ)) := rfl

/-- Coordinates of the inner product in the plane. -/
theorem inner_two (a b : EuclideanSpace ℝ (Fin 2)) : inner ℝ (a) (b) = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The other column. -/
noncomputable def shortCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col1 Q else col0 Q

/-- The perpendicular of a plane vector. -/
noncomputable def perp (a : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-a 1, a 0]

theorem nrm_eq_perp (Q : Matrix (Fin 2) (Fin 2) ℝ) : nrm Q = (r₁ Q)⁻¹ • perp (longCol Q) := rfl

theorem wedge_eq_stripWedge (n m : EuclideanSpace ℝ (Fin 2)) : wedge n m = stripWedge n m := rfl

theorem perp_apply0 (a : EuclideanSpace ℝ (Fin 2)) : perp a 0 = -a 1 := rfl
theorem perp_apply1 (a : EuclideanSpace ℝ (Fin 2)) : perp a 1 = a 0 := rfl

-- From o104/x0472, SpineFrames.lean (`norm_sq_two`).
theorem norm_sq_eq_two (a : EuclideanSpace ℝ (Fin 2)) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

theorem norm_perp (a : EuclideanSpace ℝ (Fin 2)) : ‖perp a‖ = ‖a‖ := by
  have h1 := norm_sq_eq_two (perp a)
  have h2 := norm_sq_eq_two a
  rw [perp_apply0, perp_apply1] at h1
  have : ‖perp a‖ ^ 2 = ‖a‖ ^ 2 := by rw [h1, h2]; ring
  nlinarith [norm_nonneg (perp a), norm_nonneg a, sq_nonneg (‖perp a‖ - ‖a‖),
    sq_nonneg (‖perp a‖ + ‖a‖)]

theorem inner_perp_self (a : EuclideanSpace ℝ (Fin 2)) : inner ℝ (a) (perp a) = 0 := by
  rw [inner_two, perp_apply0, perp_apply1]
  ring

theorem col_norm_le (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖col0 Q‖ ≤ r₁ Q ∧ ‖col1 Q‖ ≤ r₁ Q ∧ ‖shortCol Q‖ ≤ r₁ Q := by
  unfold r₁ longCol shortCol
  split_ifs with h
  · exact ⟨le_rfl, h, h⟩
  · push Not at h
    exact ⟨h.le, le_rfl, h.le⟩

theorem r₁_nonneg (Q : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ r₁ Q := norm_nonneg _

theorem det_eq_cols (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q.det = col0 Q 0 * col1 Q 1 - col0 Q 1 * col1 Q 0 := by
  rw [Matrix.det_fin_two]
  simp [col0, col1]
  ring

theorem r₁_pos {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : 0 < r₁ Q := by
  rcases (r₁_nonneg Q).lt_or_eq with h | h
  · exact h
  exfalso
  have h0 : ‖col0 Q‖ = 0 := le_antisymm (h ▸ (col_norm_le Q).1) (norm_nonneg _)
  have h00 : col0 Q = 0 := norm_eq_zero.mp h0
  apply hQ
  rw [det_eq_cols, h00]
  simp

theorem norm_nrm {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : ‖nrm Q‖ = 1 := by
  have h := r₁_pos hQ
  rw [nrm_eq_perp, norm_smul, norm_perp, Real.norm_eq_abs, abs_inv, abs_of_pos h]
  exact inv_mul_cancel₀ h.ne'

/-- The absolute determinant is the long scale times the normal component of the other
column. -/
theorem inner_shortCol_nrm {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    |inner ℝ (shortCol Q) (nrm Q)| = r₂ Q := by
  have h := r₁_pos hQ
  rw [nrm_eq_perp]
  unfold r₂
  rw [inner_smul_right, abs_mul, abs_inv, abs_of_pos h, inv_mul_eq_div]
  congr 1
  unfold shortCol longCol
  split_ifs with hc
  · rw [inner_two, perp_apply0, perp_apply1, det_eq_cols]
    congr 1
    ring
  · rw [inner_two, perp_apply0, perp_apply1, det_eq_cols, abs_sub_comm]
    congr 1
    ring

theorem inner_longCol_nrm (Q : Matrix (Fin 2) (Fin 2) ℝ) : inner ℝ (longCol Q) (nrm Q) = 0 := by
  rw [nrm_eq_perp, inner_smul_right, inner_perp_self, mul_zero]

theorem r₂_nonneg (Q : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ r₂ Q :=
  div_nonneg (abs_nonneg _) (r₁_nonneg _)

/-- The image of a vector under the chart matrix, by columns. -/
theorem toEuclideanLin_two (Q : Matrix (Fin 2) (Fin 2) ℝ) (g : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin Q g = g 0 • col0 Q + g 1 • col1 Q := by
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, col0, col1] <;> ring_nf

theorem abs_coord_le_norm (g : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |g i| ≤ ‖g‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le g i

/-- The image under the chart matrix in terms of the long and short columns. -/
theorem toEuclideanLin_long_short (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (g : EuclideanSpace ℝ (Fin 2)) :
    ∃ a b : ℝ, |a| ≤ ‖g‖ ∧ |b| ≤ ‖g‖ ∧
      Matrix.toEuclideanLin Q g = a • longCol Q + b • shortCol Q := by
  rw [toEuclideanLin_two]
  unfold longCol shortCol
  split_ifs
  · exact ⟨g 0, g 1, abs_coord_le_norm g 0, abs_coord_le_norm g 1, rfl⟩
  · exact ⟨g 1, g 0, abs_coord_le_norm g 1, abs_coord_le_norm g 0, add_comm _ _⟩

/-- Chart images have normal component at most `‖g‖ r₂`. -/
theorem abs_inner_nrm_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (g : EuclideanSpace ℝ (Fin 2)) :
    |inner ℝ (Matrix.toEuclideanLin Q g) (nrm Q)| ≤ ‖g‖ * r₂ Q := by
  obtain ⟨a, b, ha, hb, h⟩ := toEuclideanLin_long_short Q g
  rw [h, inner_add_left, inner_smul_left, inner_smul_left, inner_longCol_nrm]
  simp only [conj_trivial, mul_zero, zero_add]
  rw [abs_mul, inner_shortCol_nrm hQ]
  exact mul_le_mul_of_nonneg_right hb (r₂_nonneg Q)

/-- The long scale is at most the entry sum. -/
theorem r₁_le_entrySum (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    r₁ Q ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q i j| := by
  have hsum : ∀ a b : ℝ, Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    intro a b
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  have hc0 : ‖col0 Q‖ ≤ |Q 0 0| + |Q 1 0| := by
    rw [← Real.sqrt_sq (norm_nonneg (col0 Q)), norm_sq_eq_two]
    exact hsum _ _
  have hc1 : ‖col1 Q‖ ≤ |Q 0 1| + |Q 1 1| := by
    rw [← Real.sqrt_sq (norm_nonneg (col1 Q)), norm_sq_eq_two]
    exact hsum _ _
  simp only [Fin.sum_univ_two]
  unfold r₁ longCol
  split_ifs
  · linarith [abs_nonneg (Q 0 1), abs_nonneg (Q 1 1)]
  · linarith [abs_nonneg (Q 0 0), abs_nonneg (Q 1 0)]

/-- **Separated normals.**  The velocity sets `u + Q(ball(W))` of two charts whose unit
normals satisfy `g ≤ |wedge|` meet inside one closed ball of radius `8 r / g`, where
`r = W · max(r₂ Q, r₂ Q')`. -/
theorem velocity_inter_subset_ball {Q Q' : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hQ' : Q'.det ≠ 0) {u u' : EuclideanSpace ℝ (Fin 2)} {W g : ℝ} (hg : 0 < g)
    (hsep : g ≤ |wedge (nrm Q) (nrm Q')|) :
    ∃ w₀ : EuclideanSpace ℝ (Fin 2),
      {w | ‖Matrix.toEuclideanLin Q⁻¹ (w - u)‖ ≤ W} ∩
        {w | ‖Matrix.toEuclideanLin Q'⁻¹ (w - u')‖ ≤ W} ⊆
      Metric.closedBall w₀ (8 * (W * max (r₂ Q) (r₂ Q')) / g) := by
  have hinv : ∀ (P : Matrix (Fin 2) (Fin 2) ℝ), P.det ≠ 0 → ∀ z,
      Matrix.toEuclideanLin P (Matrix.toEuclideanLin P⁻¹ z) = z := by
    intro P hP z
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    rw [Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)]
    simp
  set r := W * max (r₂ Q) (r₂ Q') with hr
  have hstrip : ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (uP : EuclideanSpace ℝ (Fin 2)), P.det ≠ 0 →
      r₂ P ≤ max (r₂ Q) (r₂ Q') → ∀ w, ‖Matrix.toEuclideanLin P⁻¹ (w - uP)‖ ≤ W →
      w ∈ affineStrip (nrm P) (inner ℝ uP (nrm P)) r := by
    intro P uP hP hrP w hw
    have h := abs_inner_nrm_le hP (Matrix.toEuclideanLin P⁻¹ (w - uP))
    rw [hinv P hP] at h
    change |inner ℝ w (nrm P) - inner ℝ uP (nrm P)| ≤ r
    rw [← inner_sub_left]
    refine h.trans ?_
    rw [hr]
    have hW : 0 ≤ W := (norm_nonneg _).trans hw
    exact mul_le_mul hw hrP (r₂_nonneg _) hW
  by_cases hne : ({w | ‖Matrix.toEuclideanLin Q⁻¹ (w - u)‖ ≤ W} ∩
      {w | ‖Matrix.toEuclideanLin Q'⁻¹ (w - u')‖ ≤ W}).Nonempty
  · obtain ⟨w₀, hw₀, hw₀'⟩ := hne
    refine ⟨w₀, fun w ⟨hw, hw'⟩ => ?_⟩
    rw [Metric.mem_closedBall]
    have hd := strip_intersection_diameter (norm_nrm hQ) (norm_nrm hQ') hg hsep
      (hstrip Q u hQ (le_max_left _ _) w hw) (hstrip Q' u' hQ' (le_max_right _ _) w hw')
      (hstrip Q u hQ (le_max_left _ _) w₀ hw₀) (hstrip Q' u' hQ' (le_max_right _ _) w₀ hw₀')
    exact hd
  · refine ⟨0, fun w hw => absurd ⟨w, hw⟩ hne⟩

end Submission.Obl.k4_angular_normal_pair_preparation
