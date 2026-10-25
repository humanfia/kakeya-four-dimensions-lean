-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/FrameBounds.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/FrameBounds.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.FrameCompat

/-!
# Bounds for the common frames

* `frameQ_bounds`: the frame matrix of a code is invertible, its determinant is the
  product of its widths, its entries and inverse entries are bounded by the widths.
* `homogenized_scales`: for old charts in one dyadic scale class `R₁ ≤ r₁ ≤ 2R₁`,
  `r₂ ≤ 2R₂`, the choice `S₁ = 2^s R₁`, `S₂ = 2^s max(R₂, g R₁)`, `K = 78 κ₀` satisfies the
  scale hypotheses of `frame_confinement` and `chartCode_mem_codeNbhd`.
* `velEllipse_inter_subset_ball`: the velocity sets of two charts whose normals are
  separated (`g < |wedge|`) meet in a ball of radius `8 r / g`, `r` the larger normal
  velocity width.  This is the exceptional case handed to the normal-exception bound.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix Submission.Lib.K4FinitePlankAtlases Submission.Lib.K4VelocityStrips

/-- The frame matrix of a code with nonzero grid corner. -/
theorem frameQ_bounds {g S₁ S₂ A : ℝ} {κ : FrameCode} (hk : 0 < ‖codeVec g κ.kn‖)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hA : 0 < A) :
    |(frameQ g S₁ S₂ A κ).det| = (A * S₁) * (A * S₂) ∧
    (frameQ g S₁ S₂ A κ).det ≠ 0 ∧
    (∑ i : Fin 2, ∑ j : Fin 2, |frameQ g S₁ S₂ A κ i j|) ≤ 2 * (A * S₁ + A * S₂) ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|frameQ g S₁ S₂ A κ i j| + |(frameQ g S₁ S₂ A κ)⁻¹ i j|)) ≤
      2 * (A * S₁ + A * S₂ + (A * S₁)⁻¹ + (A * S₂)⁻¹) := by
  obtain ⟨he, hn, hen⟩ := axes_orthonormal hk
  have ha : 0 < A * S₁ := mul_pos hA hS₁
  have hb : 0 < A * S₂ := mul_pos hA hS₂
  have hdet := plankFrame_abs_det ha hb he hn hen
  refine ⟨hdet, ?_, plankFrame_entries ha hb he hn, plankFrame_entry_budget ha hb he hn hen⟩
  intro h0
  unfold frameQ at h0
  rw [h0, abs_zero] at hdet
  have : 0 < (A * S₁) * (A * S₂) := mul_pos ha hb
  linarith

/-- The norm of a combination of orthonormal axes. -/
theorem norm_comb_axes_le {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (a b : ℝ) : ‖a • e + b • n‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, he, hn, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]

/-- A plane vector is the combination of its coordinates in orthonormal axes. -/
theorem eq_comb_axes {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hen : inner ℝ e n = 0) (w : EuclideanSpace ℝ (Fin 2)) :
    w = (inner ℝ w e) • e + (inner ℝ w n) • n := by
  have hsq0 : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_two, he]; norm_num
  have hsq1 : n 0 ^ 2 + n 1 ^ 2 = 1 := by rw [← norm_sq_two, hn]; norm_num
  have hor : e 0 * n 0 + e 1 * n 1 = 0 := by rw [inner_two] at hen; exact hen
  have key : (e 0 * n 1 - e 1 * n 0) ^ 2 =
      (e 0 ^ 2 + e 1 ^ 2) * (n 0 ^ 2 + n 1 ^ 2) - (e 0 * n 0 + e 1 * n 1) ^ 2 := by ring
  rw [hsq0, hsq1, hor] at key
  have hdet : e 0 * n 1 - e 1 * n 0 ≠ 0 := by
    intro h0
    rw [h0] at key
    norm_num at key
  set z := w - ((inner ℝ w e) • e + (inner ℝ w n) • n) with hz
  have hze : inner ℝ z e = 0 := by
    rw [hz, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      real_inner_self_eq_norm_sq, he, real_inner_comm e n, hen]
    simp
  have hzn : inner ℝ z n = 0 := by
    rw [hz, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      real_inner_self_eq_norm_sq, hn, hen]
    simp
  rw [inner_two] at hze hzn
  have hz0 : z 0 = 0 := by
    have h : z 0 * (e 0 * n 1 - e 1 * n 0) = 0 := by
      have : z 0 * (e 0 * n 1 - e 1 * n 0) =
          n 1 * (z 0 * e 0 + z 1 * e 1) - e 1 * (z 0 * n 0 + z 1 * n 1) := by ring
      rw [this, hze, hzn]; ring
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hdet
  have hz1 : z 1 = 0 := by
    have h : z 1 * (e 0 * n 1 - e 1 * n 0) = 0 := by
      have : z 1 * (e 0 * n 1 - e 1 * n 0) =
          e 0 * (z 0 * n 0 + z 1 * n 1) - n 0 * (z 0 * e 0 + z 1 * e 1) := by ring
      rw [this, hze, hzn]; ring
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hdet
  have hzero : z = 0 := by
    ext i
    fin_cases i
    · simpa using hz0
    · simpa using hz1
  have := sub_eq_zero.mp (hz ▸ hzero)
  exact this

/-- The frame velocity and midpoint center of a chart's code are close to the chart's. -/
theorem frame_data_close {g S₁ S₂ q₁ tm : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hq₁ : 0 < q₁)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    ‖u - frameU g S₁ S₂ q₁ (chartCode g S₁ S₂ q₁ tm c u Q)‖ ≤ S₁ / q₁ + S₂ / q₁ ∧
    ‖(c + tm • u) - frameP g S₁ S₂ (chartCode g S₁ S₂ q₁ tm c u Q)‖ ≤ S₁ + S₂ := by
  have hν := norm_nrm hQ
  obtain ⟨he, hn, hen⟩ := axes_orthonormal (codeVec_ne_zero hg hg8 hν)
  set k := roundCode g (nrm Q)
  set e := axisT g k
  set n := axisN g k
  have hP := inner_comb_axes he hn hen
  have hcomb := eq_comb_axes he hn hen
  constructor
  · rw [hcomb (u - _)]
    refine (norm_comb_axes_le he hn _ _).trans ?_
    have h1 : |inner ℝ (u - frameU g S₁ S₂ q₁ (chartCode g S₁ S₂ q₁ tm c u Q)) e| ≤ S₁ / q₁ := by
      rw [inner_sub_left]
      unfold frameU
      rw [show (chartCode g S₁ S₂ q₁ tm c u Q).kn = k from rfl, (hP _ _).1]
      exact floor_spacing_err (div_pos hS₁ hq₁)
    have h2 : |inner ℝ (u - frameU g S₁ S₂ q₁ (chartCode g S₁ S₂ q₁ tm c u Q)) n| ≤ S₂ / q₁ := by
      rw [inner_sub_left]
      unfold frameU
      rw [show (chartCode g S₁ S₂ q₁ tm c u Q).kn = k from rfl, (hP _ _).2]
      exact floor_spacing_err (div_pos hS₂ hq₁)
    linarith
  · rw [hcomb (_ - _)]
    refine (norm_comb_axes_le he hn _ _).trans ?_
    have h1 : |inner ℝ ((c + tm • u) - frameP g S₁ S₂ (chartCode g S₁ S₂ q₁ tm c u Q)) e| ≤ S₁ := by
      rw [inner_sub_left]
      unfold frameP
      rw [show (chartCode g S₁ S₂ q₁ tm c u Q).kn = k from rfl, (hP _ _).1]
      exact floor_spacing_err hS₁
    have h2 : |inner ℝ ((c + tm • u) - frameP g S₁ S₂ (chartCode g S₁ S₂ q₁ tm c u Q)) n| ≤ S₂ := by
      rw [inner_sub_left]
      unfold frameP
      rw [show (chartCode g S₁ S₂ q₁ tm c u Q).kn = k from rfl, (hP _ _).2]
      exact floor_spacing_err hS₂
    linarith

/-- The frame center and velocity have norm bounded through the chart's own. -/
theorem frame_center_velocity_le {g S₁ S₂ q₁ tm : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hq₁ : 0 < q₁)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    ‖frameC g S₁ S₂ q₁ tm (chartCode g S₁ S₂ q₁ tm c u Q)‖ +
        ‖frameU g S₁ S₂ q₁ (chartCode g S₁ S₂ q₁ tm c u Q)‖ ≤
      ‖c‖ + (2 * |tm| + 1) * ‖u‖ + (S₁ + S₂) + (2 * |tm| + 1) * ((S₁ + S₂) / q₁) := by
  obtain ⟨hU, hPc⟩ := frame_data_close (tm := tm) (c := c) hg hg8 hS₁ hS₂ hq₁ hQ
  set κc := chartCode g S₁ S₂ q₁ tm c u Q
  have hUn : ‖frameU g S₁ S₂ q₁ κc‖ ≤ ‖u‖ + (S₁ + S₂) / q₁ := by
    have : frameU g S₁ S₂ q₁ κc = u - (u - frameU g S₁ S₂ q₁ κc) := by abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [add_div]; linarith
  have hPn : ‖frameP g S₁ S₂ κc‖ ≤ ‖c‖ + |tm| * ‖u‖ + (S₁ + S₂) := by
    have : frameP g S₁ S₂ κc = (c + tm • u) - ((c + tm • u) - frameP g S₁ S₂ κc) := by abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖c + tm • u‖ ≤ ‖c‖ + |tm| * ‖u‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
    linarith
  have hCn : ‖frameC g S₁ S₂ q₁ tm κc‖ ≤ ‖frameP g S₁ S₂ κc‖ + |tm| * ‖frameU g S₁ S₂ q₁ κc‖ := by
    unfold frameC
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  have htm := abs_nonneg tm
  have hq : 0 ≤ (S₁ + S₂) / q₁ := by positivity
  have hu := norm_nonneg u
  nlinarith

/-- **Homogenized scales.**  Old charts in one dyadic scale class satisfy the scale
hypotheses of the frame lemmas with `S₁ = 2^s R₁`, `S₂ = 2^s max(R₂, g R₁)`, `K = 78 κ₀`,
where the coarse block is `2^s` old blocks long. -/
theorem homogenized_scales {g R₁ R₂ q₀ κ₀ : ℝ} {s : ℕ} (hg : 0 ≤ g) (hq₀ : 0 < q₀)
    (hκ₀ : 0 ≤ κ₀) {Q : Matrix (Fin 2) (Fin 2) ℝ} (hr₁ : r₁ Q ≤ 2 * R₁) (hr₂ : r₂ Q ≤ 2 * R₂) :
    2 * (κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀)) * r₁ Q ≤ (78 * κ₀) * (2 ^ s * R₁) ∧
    κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀) * r₂ Q +
        6 * g * (2 * (κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀)) * r₁ Q) ≤
      (78 * κ₀) * (2 ^ s * max R₂ (g * R₁)) := by
  have hs : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hρ : κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀) ≤ 3 * 2 ^ s * κ₀ := by
    have e : 2 * (2 ^ s * q₀) / q₀ = 2 * 2 ^ s := by field_simp
    rw [e]
    nlinarith
  have hρ0 : 0 ≤ κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀) := by positivity
  have hr₁0 := r₁_nonneg Q
  have hr₂0 := r₂_nonneg Q
  have hR₁ : 0 ≤ R₁ := by linarith
  have hR₂ : 0 ≤ R₂ := by linarith
  have hm1 : R₂ ≤ max R₂ (g * R₁) := le_max_left _ _
  have hm2 : g * R₁ ≤ max R₂ (g * R₁) := le_max_right _ _
  constructor
  · calc 2 * (κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀)) * r₁ Q ≤ 2 * (3 * 2 ^ s * κ₀) * (2 * R₁) := by
          gcongr
      _ ≤ (78 * κ₀) * (2 ^ s * R₁) := by nlinarith [mul_nonneg hκ₀ hR₁]
  · have a1 : κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀) * r₂ Q ≤ 3 * 2 ^ s * κ₀ * (2 * R₂) := by gcongr
    have a2 : 6 * g * (2 * (κ₀ * (1 + 2 * (2 ^ s * q₀) / q₀)) * r₁ Q) ≤
        6 * g * (2 * (3 * 2 ^ s * κ₀) * (2 * R₁)) := by gcongr
    have b1 : 3 * 2 ^ s * κ₀ * (2 * R₂) ≤ 6 * (κ₀ * (2 ^ s * max R₂ (g * R₁))) := by
      have : 2 ^ s * κ₀ * R₂ ≤ 2 ^ s * κ₀ * max R₂ (g * R₁) := by gcongr
      nlinarith
    have b2 : 6 * g * (2 * (3 * 2 ^ s * κ₀) * (2 * R₁)) ≤ 72 * (κ₀ * (2 ^ s * max R₂ (g * R₁))) := by
      have : 2 ^ s * κ₀ * (g * R₁) ≤ 2 ^ s * κ₀ * max R₂ (g * R₁) := by gcongr
      nlinarith
    nlinarith

/-- **Separated normals.**  The velocity sets `u + Q(ball(W))` of two charts whose unit
normals satisfy `g ≤ |wedge|` meet inside one closed ball of radius `8 r / g`, where
`r = W · max(r₂ Q, r₂ Q')`. -/
theorem velocity_inter_subset_ball {Q Q' : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hQ' : Q'.det ≠ 0) {u u' : EuclideanSpace ℝ (Fin 2)} {W g : ℝ} (hg : 0 < g)
    (hsep : g ≤ |stripWedge (nrm Q) (nrm Q')|) :
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

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
