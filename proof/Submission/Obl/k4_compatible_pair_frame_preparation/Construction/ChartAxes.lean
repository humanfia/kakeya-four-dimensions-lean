-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/ChartAxes.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/ChartAxes.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.SpineFrames

/-!
# Principal axes of an old spatial chart

For an invertible `2 × 2` chart matrix `Q` let `longCol Q` be its longer column,
`r₁ Q` its length, `nrm Q` the unit vector perpendicular to it and `r₂ Q = |det Q| / r₁ Q`.
Every image `Q g` lies in the rectangle of half-sides `2‖g‖ r₁` along the long column and
`‖g‖ r₂` along the normal.  These are the old physical scales of the supplied paper's
Lemma 3.5 (the longer side and the normal width of an old chart), obtained without a
singular value decomposition.

A trajectory confined in an old chart on its old block stays in the extrapolated chart on
any longer block containing it, with the slack multiplied by `1 + 2 q₁/q₀`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix
open scoped RealInnerProductSpace

/-- Coordinates of the inner product in the plane. -/
theorem inner_two (a b : EuclideanSpace ℝ (Fin 2)) : inner ℝ (a) (b) = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The first column of a `2 × 2` matrix. -/
noncomputable def col0 (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Q 0 0, Q 1 0]

/-- The second column of a `2 × 2` matrix. -/
noncomputable def col1 (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Q 0 1, Q 1 1]

/-- The longer column (the first one on ties). -/
noncomputable def longCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col0 Q else col1 Q

/-- The other column. -/
noncomputable def shortCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col1 Q else col0 Q

/-- The long scale. -/
noncomputable def r₁ (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ‖longCol Q‖

/-- The narrow scale. -/
noncomputable def r₂ (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |Q.det| / r₁ Q

/-- The perpendicular of a plane vector. -/
noncomputable def perp (a : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-a 1, a 0]

/-- The unit normal of the long column. -/
noncomputable def nrm (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (r₁ Q)⁻¹ • perp (longCol Q)

theorem perp_apply0 (a : EuclideanSpace ℝ (Fin 2)) : perp a 0 = -a 1 := rfl
theorem perp_apply1 (a : EuclideanSpace ℝ (Fin 2)) : perp a 1 = a 0 := rfl

theorem norm_sq_eq_two (a : EuclideanSpace ℝ (Fin 2)) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 :=
  norm_sq_two a

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
  rw [nrm, norm_smul, norm_perp, Real.norm_eq_abs, abs_inv, abs_of_pos h]
  exact inv_mul_cancel₀ h.ne'

/-- The absolute determinant is the long scale times the normal component of the other
column. -/
theorem inner_shortCol_nrm {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    |inner ℝ (shortCol Q) (nrm Q)| = r₂ Q := by
  have h := r₁_pos hQ
  unfold r₂ nrm
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
  unfold nrm
  rw [inner_smul_right, inner_perp_self, mul_zero]

theorem r₂_nonneg (Q : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ r₂ Q :=
  div_nonneg (abs_nonneg _) (r₁_nonneg _)

theorem r₂_le_r₁ {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : r₂ Q ≤ r₁ Q := by
  rw [← inner_shortCol_nrm hQ]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_nrm hQ, mul_one]
  exact (col_norm_le Q).2.2

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

/-- Chart images have length at most `2‖g‖ r₁`. -/
theorem norm_toEuclideanLin_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (g : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanLin Q g‖ ≤ 2 * ‖g‖ * r₁ Q := by
  obtain ⟨a, b, ha, hb, h⟩ := toEuclideanLin_long_short Q g
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : ‖longCol Q‖ = r₁ Q := rfl
  have h2 := (col_norm_le Q).2.2
  rw [h1]
  have := r₁_nonneg Q
  nlinarith [abs_nonneg a, abs_nonneg b, norm_nonneg (shortCol Q), norm_nonneg g]

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

/-- An affine function bounded at the two ends of a short interval is bounded on any
longer interval containing it, with the length ratio. -/
theorem affine_extension_bound {g₀ g' : EuclideanSpace ℝ (Fin 2)} {t₁ q₀ κ₀ t : ℝ}
    (hq₀ : 0 < q₀) (h₁ : ‖g₀ + t₁ • g'‖ ≤ κ₀) (h₂ : ‖g₀ + (t₁ + q₀) • g'‖ ≤ κ₀) :
    ‖g₀ + t • g'‖ ≤ κ₀ * (1 + 2 * |t - t₁| / q₀) ∧ ‖g'‖ ≤ 2 * κ₀ / q₀ := by
  have hd : (g₀ + (t₁ + q₀) • g') - (g₀ + t₁ • g') = q₀ • g' := by module
  have hg' : ‖g'‖ ≤ 2 * κ₀ / q₀ := by
    have hn : ‖q₀ • g'‖ ≤ 2 * κ₀ := by
      rw [← hd]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq₀] at hn
    rw [le_div_iff₀ hq₀]
    linarith
  refine ⟨?_, hg'⟩
  have he : g₀ + t • g' = (g₀ + t₁ • g') + (t - t₁) • g' := by module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have : |t - t₁| * ‖g'‖ ≤ |t - t₁| * (2 * κ₀ / q₀) :=
    mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
  have h3 : |t - t₁| * (2 * κ₀ / q₀) = κ₀ * (2 * |t - t₁| / q₀) := by ring
  nlinarith

/-- The frame offset written affinely in time. -/
theorem frameOffset_affine (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    frameOffset c u Q l t = frameOffset c u Q l 0 + t • Matrix.toEuclideanLin Q⁻¹ (v l - u) := by
  have h := frameOffset_sub c u Q l t 0
  rw [sub_zero] at h
  rw [← h]
  abel

/-- **Extrapolated confinement.**  A trajectory confined in an old chart at the two ends
of its old block `[t₁, t₁ + q₀]` deviates from the old moving center by a chart image of
size at most `κ₀ (1 + 2|t - t₁|/q₀)` at every time, and its velocity deviates by a chart
image of size at most `2κ₀/q₀`. -/
theorem chart_extrapolation {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) {l : ℕ × (Fin 6 → ℝ)} {t₁ q₀ κ₀ : ℝ} (hq₀ : 0 < q₀)
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ ≤ κ₀)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (t₁ + q₀) - c - (t₁ + q₀) • u)‖ ≤ κ₀) (t : ℝ) :
    (∃ g : EuclideanSpace ℝ (Fin 2), ‖g‖ ≤ κ₀ * (1 + 2 * |t - t₁| / q₀) ∧
      y l t - c - t • u = Matrix.toEuclideanLin Q g) ∧
    (∃ g : EuclideanSpace ℝ (Fin 2), ‖g‖ ≤ 2 * κ₀ / q₀ ∧
      v l - u = Matrix.toEuclideanLin Q g) := by
  have hinv : ∀ z, Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ z) = z := by
    intro z
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    rw [Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)]
    simp
  have hA := frameOffset_affine c u Q l
  have h₁' : ‖frameOffset c u Q l 0 + t₁ • Matrix.toEuclideanLin Q⁻¹ (v l - u)‖ ≤ κ₀ := by
    rw [← hA]; exact h₁
  have h₂' : ‖frameOffset c u Q l 0 + (t₁ + q₀) • Matrix.toEuclideanLin Q⁻¹ (v l - u)‖ ≤ κ₀ := by
    rw [← hA]; exact h₂
  obtain ⟨hb, hv⟩ := affine_extension_bound (t := t) hq₀ h₁' h₂'
  refine ⟨⟨frameOffset c u Q l t, ?_, ?_⟩, ⟨Matrix.toEuclideanLin Q⁻¹ (v l - u), hv, ?_⟩⟩
  · rw [hA]; exact hb
  · rw [frameOffset, hinv]
  · rw [hinv]

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
