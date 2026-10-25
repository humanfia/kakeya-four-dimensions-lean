-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/CommonFrames.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/CommonFrames.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.ChartAxes
import Submission.Lib.K4FinitePlankAtlases.PlankFrame

/-!
# Common moving frames on a coarse block

Following the supplied paper's Lemma 3.5 ("A common spatial frame"), each old chart is
assigned a code: its unit normal rounded at mesh `g`, and, in the orthonormal axes of the
rounded normal, its center at the new block midpoint rounded at spacings `S₁, S₂` and its
center velocity rounded at spacings `S₁/q₁, S₂/q₁`.  A code determines a frame
(`frameC, frameU, frameQ`) on the new block, independently of the old chart.

`frame_confinement`: every trajectory confined in the old chart on its old block is
confined in the frame of the chart's code on the whole new block, once the scales `S₁,S₂`
dominate the extrapolated long and normal extents (with the normal rounding error).
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix Submission.Lib.K4FinitePlankAtlases

/-! ### Rounded normals -/

/-- The integer code of a plane vector at mesh `g`. -/
noncomputable def roundCode (g : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℤ × ℤ :=
  (⌊w 0 / g⌋, ⌊w 1 / g⌋)

/-- The grid corner of a code. -/
noncomputable def codeVec (g : ℝ) (k : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![g * k.1, g * k.2]

/-- The unit normal axis of a code. -/
noncomputable def axisN (g : ℝ) (k : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  ‖codeVec g k‖⁻¹ • codeVec g k

/-- The tangent axis of a code. -/
noncomputable def axisT (g : ℝ) (k : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  perp (axisN g k)

theorem floor_mul_err {a g : ℝ} (hg : 0 < g) : |a - g * ⌊a / g⌋| ≤ g := by
  have h1 := Int.floor_le (a / g)
  have h2 := Int.lt_floor_add_one (a / g)
  have e1 : g * ⌊a / g⌋ ≤ a := by
    have := mul_le_mul_of_nonneg_left h1 hg.le
    rwa [mul_div_cancel₀ _ hg.ne'] at this
  have e2 : a < g * ⌊a / g⌋ + g := by
    have := mul_lt_mul_of_pos_left h2 hg
    rw [mul_div_cancel₀ _ hg.ne', mul_add, mul_one] at this
    exact this
  rw [abs_le]
  constructor <;> linarith

theorem codeVec_sub_le {g : ℝ} (hg : 0 < g) (w : EuclideanSpace ℝ (Fin 2)) :
    ‖codeVec g (roundCode g w) - w‖ ≤ 2 * g := by
  have h0 := floor_mul_err (a := w 0) hg
  have h1 := floor_mul_err (a := w 1) hg
  have hsq := norm_sq_eq_two (codeVec g (roundCode g w) - w)
  have hc0 : (codeVec g (roundCode g w) - w) 0 = g * ⌊w 0 / g⌋ - w 0 := by
    simp [codeVec, roundCode]
  have hc1 : (codeVec g (roundCode g w) - w) 1 = g * ⌊w 1 / g⌋ - w 1 := by
    simp [codeVec, roundCode]
  rw [hc0, hc1] at hsq
  rw [abs_sub_comm] at h0 h1
  have a0 : (g * ⌊w 0 / g⌋ - w 0) ^ 2 ≤ g ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have a1 : (g * ⌊w 1 / g⌋ - w 1) ^ 2 ≤ g ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [norm_nonneg (codeVec g (roundCode g w) - w)]

/-- Normalizing a vector close to a unit vector at most doubles the error. -/
theorem normalize_err {w ν : EuclideanSpace ℝ (Fin 2)} {ε : ℝ} (hν : ‖ν‖ = 1)
    (hw : ‖w - ν‖ ≤ ε) (hε : ε < 1) : ‖‖w‖⁻¹ • w - ν‖ ≤ 2 * ε := by
  have hn : |‖w‖ - 1| ≤ ε := by
    rw [← hν]
    exact (abs_norm_sub_norm_le w ν).trans hw
  have hwpos : 0 < ‖w‖ := by
    rw [abs_le] at hn
    linarith [hn.1]
  have hsplit : ‖w‖⁻¹ • w - ν = (‖w‖⁻¹ • w - w) + (w - ν) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖‖w‖⁻¹ • w - w‖ = |1 - ‖w‖| := by
    have : ‖w‖⁻¹ • w - w = (‖w‖⁻¹ - 1) • w := by rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs]
    rw [show (‖w‖⁻¹ - 1) = (1 - ‖w‖) / ‖w‖ by field_simp]
    rw [abs_div, abs_of_pos hwpos, div_mul_cancel₀ _ hwpos.ne']
  rw [h1, abs_sub_comm]
  linarith

theorem axisN_err {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) {ν : EuclideanSpace ℝ (Fin 2)}
    (hν : ‖ν‖ = 1) : ‖axisN g (roundCode g ν) - ν‖ ≤ 4 * g := by
  have h := normalize_err hν (codeVec_sub_le hg ν) (by linarith)
  unfold axisN
  linarith

theorem codeVec_ne_zero {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) {ν : EuclideanSpace ℝ (Fin 2)}
    (hν : ‖ν‖ = 1) : 0 < ‖codeVec g (roundCode g ν)‖ := by
  have h := codeVec_sub_le hg ν
  have h2 := abs_norm_sub_norm_le (codeVec g (roundCode g ν)) ν
  rw [hν, abs_le] at h2
  linarith [h2.1]

/-- The axes of a code with a nonzero grid corner are orthonormal. -/
theorem axes_orthonormal {g : ℝ} {k : ℤ × ℤ} (hk : 0 < ‖codeVec g k‖) :
    ‖axisT g k‖ = 1 ∧ ‖axisN g k‖ = 1 ∧ inner ℝ (axisT g k) (axisN g k) = 0 := by
  have hN : ‖axisN g k‖ = 1 := by
    unfold axisN
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk, inv_mul_cancel₀ hk.ne']
  refine ⟨?_, hN, ?_⟩
  · unfold axisT; rw [norm_perp, hN]
  · unfold axisT
    rw [real_inner_comm]
    exact inner_perp_self _

/-! ### Codes and frames -/

/-- The code of an old chart: rounded normal, rounded midpoint center and rounded center
velocity, in the axes of the rounded normal. -/
structure FrameCode where
  kn : ℤ × ℤ
  kp : ℤ × ℤ
  kv : ℤ × ℤ
deriving DecidableEq

/-- The code of the old chart `(c, u, Q)` on a coarse block with midpoint `tm`. -/
noncomputable def chartCode (g S₁ S₂ q₁ tm : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : FrameCode :=
  let k := roundCode g (nrm Q)
  let e := axisT g k
  let n := axisN g k
  let p := c + tm • u
  { kn := k
    kp := (⌊inner ℝ p e / S₁⌋, ⌊inner ℝ p n / S₂⌋)
    kv := (⌊inner ℝ u e / (S₁ / q₁)⌋, ⌊inner ℝ u n / (S₂ / q₁)⌋) }

/-- The frame velocity of a code. -/
noncomputable def frameU (g S₁ S₂ q₁ : ℝ) (κ : FrameCode) : EuclideanSpace ℝ (Fin 2) :=
  ((κ.kv.1 : ℝ) * (S₁ / q₁)) • axisT g κ.kn + ((κ.kv.2 : ℝ) * (S₂ / q₁)) • axisN g κ.kn

/-- The frame center at the block midpoint. -/
noncomputable def frameP (g S₁ S₂ : ℝ) (κ : FrameCode) : EuclideanSpace ℝ (Fin 2) :=
  ((κ.kp.1 : ℝ) * S₁) • axisT g κ.kn + ((κ.kp.2 : ℝ) * S₂) • axisN g κ.kn

/-- The frame center at time zero. -/
noncomputable def frameC (g S₁ S₂ q₁ tm : ℝ) (κ : FrameCode) : EuclideanSpace ℝ (Fin 2) :=
  frameP g S₁ S₂ κ - tm • frameU g S₁ S₂ q₁ κ

/-- The frame matrix: the orthonormal axes of the code scaled by `A S₁, A S₂`. -/
noncomputable def frameQ (g S₁ S₂ A : ℝ) (κ : FrameCode) : Matrix (Fin 2) (Fin 2) ℝ :=
  plankFrame (A * S₁) (A * S₂) (axisT g κ.kn) (axisN g κ.kn)

/-- Coordinates of a combination of orthonormal axes. -/
theorem inner_comb_axes {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hen : inner ℝ e n = 0) (a b : ℝ) :
    inner ℝ (a • e + b • n) e = a ∧ inner ℝ (a • e + b • n) n = b := by
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hne : inner ℝ n e = 0 := by rw [real_inner_comm]; exact hen
  constructor
  · rw [inner_add_left, inner_smul_left, inner_smul_left, hee, hne]; simp
  · rw [inner_add_left, inner_smul_left, inner_smul_left, hen, hnn]; simp

/-- Rounding a real number down to a multiple of a positive spacing. -/
theorem floor_spacing_err {a S : ℝ} (hS : 0 < S) : |a - ⌊a / S⌋ * S| ≤ S := by
  have := floor_mul_err (a := a) hS
  rwa [mul_comm] at this

/-- The along- and normal coordinates of a chart image in the axes `(e, n)`. -/
theorem image_coords {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (g : EuclideanSpace ℝ (Fin 2)) :
    |inner ℝ (Matrix.toEuclideanLin Q g) e| ≤ 2 * ‖g‖ * r₁ Q ∧
    |inner ℝ (Matrix.toEuclideanLin Q g) n| ≤ ‖g‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖g‖ * r₁ Q) := by
  have hw := norm_toEuclideanLin_le Q g
  constructor
  · refine (abs_real_inner_le_norm _ _).trans ?_
    rw [he, mul_one]; exact hw
  · have hsplit : inner ℝ (Matrix.toEuclideanLin Q g) n =
        inner ℝ (Matrix.toEuclideanLin Q g) (nrm Q) +
          inner ℝ (Matrix.toEuclideanLin Q g) (n - nrm Q) := by
      rw [inner_sub_right]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (abs_inner_nrm_le hQ g) ?_)
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)

set_option maxHeartbeats 800000 in
/-- **Confinement in the common frame.**  Let a trajectory be confined in the old chart
`(c, u, Q)` (slack `κ₀`) at the two ends of the old block `[t₁, t₁ + q₀]`, let the new
block midpoint `tm` lie within `q₁` of `t₁` and `t` within `q₁ / 2` of `tm`.  If the scales
dominate the extrapolated extents,
`2 ρ r₁ ≤ K S₁` and `ρ r₂ + 4g · 2ρ r₁ ≤ K S₂` with `ρ = κ₀ (1 + 2 q₁ / q₀)`, and also the
velocity extents `2κ₀/q₀ · 2r₁ ≤ K S₁/q₁` and `2κ₀/q₀ (r₂ + 8g r₁) ≤ K S₂/q₁`, then the
trajectory is confined in the frame of the chart's code with slack `2`, for the frame
widths `(2K + 2) S₁, (2K + 2) S₂`. -/
theorem frame_confinement {g S₁ S₂ q₀ q₁ tm κ₀ K t₁ t : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hK : 0 ≤ K)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {l : ℕ × (Fin 6 → ℝ)}
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ ≤ κ₀)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (t₁ + q₀) - c - (t₁ + q₀) • u)‖ ≤ κ₀)
    (htm : |t - tm| ≤ q₁ / 2) (htm₁ : |tm - t₁| ≤ q₁)
    (hA₁ : 2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q ≤ K * S₁)
    (hA₂ : κ₀ * (1 + 2 * q₁ / q₀) * r₂ Q + 4 * g * (2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q) ≤
      K * S₂) :
    ‖Matrix.toEuclideanLin (frameQ g S₁ S₂ (2 * K + 2) (chartCode g S₁ S₂ q₁ tm c u Q))⁻¹
      (y l t - frameC g S₁ S₂ q₁ tm (chartCode g S₁ S₂ q₁ tm c u Q) -
        t • frameU g S₁ S₂ q₁ (chartCode g S₁ S₂ q₁ tm c u Q))‖ ≤ 2 := by
  have hν : ‖nrm Q‖ = 1 := norm_nrm hQ
  obtain ⟨he, hn, hen⟩ := axes_orthonormal (codeVec_ne_zero hg hg8 hν)
  have hnerr : ‖axisN g (roundCode g (nrm Q)) - nrm Q‖ ≤ 4 * g := axisN_err hg hg8 hν
  set k := roundCode g (nrm Q) with hk
  set e := axisT g k with he_def
  set n := axisN g k with hn_def
  set κc := chartCode g S₁ S₂ q₁ tm c u Q with hκc
  have hkn : κc.kn = k := rfl
  -- decomposition of the frame offset
  set p := c + tm • u with hp
  have hdecomp : y l t - frameC g S₁ S₂ q₁ tm κc - t • frameU g S₁ S₂ q₁ κc =
      (y l tm - c - tm • u) + (p - frameP g S₁ S₂ κc) +
        (t - tm) • (v l - frameU g S₁ S₂ q₁ κc) := by
    rw [y_eq_add_smul l t, y_eq_add_smul l tm]
    unfold frameC
    rw [hp]
    module
  -- the three pieces in the axes (e, n)
  obtain ⟨⟨gm, hgm, hgmeq⟩, ⟨gv, hgv, hgveq⟩⟩ := chart_extrapolation hQ hq₀ h₁ h₂ tm
  have hρ : ‖gm‖ ≤ κ₀ * (1 + 2 * q₁ / q₀) := by
    refine hgm.trans ?_
    have hκ₀ : 0 ≤ κ₀ := (norm_nonneg _).trans h₁
    gcongr
  have hc1 := image_coords hQ he hn gm
  rw [← hgmeq] at hc1
  -- coordinates of the frame data
  have hP := inner_comb_axes he hn hen ((κc.kp.1 : ℝ) * S₁) ((κc.kp.2 : ℝ) * S₂)
  have hU := inner_comb_axes he hn hen ((κc.kv.1 : ℝ) * (S₁ / q₁)) ((κc.kv.2 : ℝ) * (S₂ / q₁))
  have hPe : inner ℝ (frameP g S₁ S₂ κc) e = (κc.kp.1 : ℝ) * S₁ := by
    unfold frameP; rw [hkn]; exact hP.1
  have hPn : inner ℝ (frameP g S₁ S₂ κc) n = (κc.kp.2 : ℝ) * S₂ := by
    unfold frameP; rw [hkn]; exact hP.2
  have hUe : inner ℝ (frameU g S₁ S₂ q₁ κc) e = (κc.kv.1 : ℝ) * (S₁ / q₁) := by
    unfold frameU; rw [hkn]; exact hU.1
  have hUn : inner ℝ (frameU g S₁ S₂ q₁ κc) n = (κc.kv.2 : ℝ) * (S₂ / q₁) := by
    unfold frameU; rw [hkn]; exact hU.2
  have hkp1 : κc.kp.1 = ⌊inner ℝ p e / S₁⌋ := rfl
  have hkp2 : κc.kp.2 = ⌊inner ℝ p n / S₂⌋ := rfl
  have hkv1 : κc.kv.1 = ⌊inner ℝ u e / (S₁ / q₁)⌋ := rfl
  have hkv2 : κc.kv.2 = ⌊inner ℝ u n / (S₂ / q₁)⌋ := rfl
  have hr1 : |inner ℝ (p - frameP g S₁ S₂ κc) e| ≤ S₁ := by
    rw [inner_sub_left, hPe, hkp1]; exact floor_spacing_err hS₁
  have hr2 : |inner ℝ (p - frameP g S₁ S₂ κc) n| ≤ S₂ := by
    rw [inner_sub_left, hPn, hkp2]; exact floor_spacing_err hS₂
  have hS₁q : 0 < S₁ / q₁ := div_pos hS₁ hq₁
  have hS₂q : 0 < S₂ / q₁ := div_pos hS₂ hq₁
  have hv1 : |inner ℝ (u - frameU g S₁ S₂ q₁ κc) e| ≤ S₁ / q₁ := by
    rw [inner_sub_left, hUe, hkv1]; exact floor_spacing_err hS₁q
  have hv2 : |inner ℝ (u - frameU g S₁ S₂ q₁ κc) n| ≤ S₂ / q₁ := by
    rw [inner_sub_left, hUn, hkv2]; exact floor_spacing_err hS₂q
  -- the velocity of the trajectory relative to the old center velocity
  have hcv := image_coords hQ he hn gv
  rw [← hgveq] at hcv
  have hvsplit : v l - frameU g S₁ S₂ q₁ κc = (v l - u) + (u - frameU g S₁ S₂ q₁ κc) := by abel
  -- assemble the two coordinates
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin 2)) (B₁ B₂ B₃ : ℝ),
      |inner ℝ (y l tm - c - tm • u) w| ≤ B₁ → |inner ℝ (p - frameP g S₁ S₂ κc) w| ≤ B₂ →
      |inner ℝ (v l - frameU g S₁ S₂ q₁ κc) w| ≤ B₃ →
      |inner ℝ (y l t - frameC g S₁ S₂ q₁ tm κc - t • frameU g S₁ S₂ q₁ κc) w| ≤
        B₁ + B₂ + q₁ / 2 * B₃ := by
    intro w B₁ B₂ B₃ hB₁ hB₂ hB₃
    rw [hdecomp, inner_add_left, inner_add_left, inner_smul_left]
    simp only [conj_trivial]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add hB₁ hB₂)) ?_
    rw [abs_mul]
    exact mul_le_mul htm hB₃ (abs_nonneg _) (by positivity)
  have hve : |inner ℝ (v l - frameU g S₁ S₂ q₁ κc) e| ≤ 2 * ‖gv‖ * r₁ Q + S₁ / q₁ := by
    rw [hvsplit, inner_add_left]
    exact (abs_add_le _ _).trans (add_le_add hcv.1 hv1)
  have hvn : |inner ℝ (v l - frameU g S₁ S₂ q₁ κc) n| ≤
      ‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q) + S₂ / q₁ := by
    rw [hvsplit, inner_add_left]
    exact (abs_add_le _ _).trans (add_le_add hcv.2 hv2)
  have hr₁ := r₁_nonneg Q
  have hr₂ := r₂_nonneg Q
  have hgv0 := norm_nonneg gv
  have hgm0 := norm_nonneg gm
  have hκ₀ : 0 ≤ κ₀ := (norm_nonneg _).trans h₁
  set ρ := κ₀ * (1 + 2 * q₁ / q₀) with hρ_def
  have hρ0 : 0 ≤ ρ := by positivity
  -- velocity extents: ‖gv‖ ≤ 2κ₀/q₀ and q₁ / 2 * (2κ₀/q₀) ≤ ρ
  have hvel : q₁ / 2 * ‖gv‖ ≤ ρ := by
    have h1 : q₁ / 2 * ‖gv‖ ≤ q₁ / 2 * (2 * κ₀ / q₀) := by gcongr
    have e2 : q₁ / 2 * (2 * κ₀ / q₀) = κ₀ * (q₁ / q₀) := by ring
    have h3 : κ₀ * (q₁ / q₀) ≤ ρ := by
      rw [hρ_def]
      apply mul_le_mul_of_nonneg_left _ hκ₀
      have : 0 ≤ q₁ / q₀ := by positivity
      have e3 : 2 * q₁ / q₀ = 2 * (q₁ / q₀) := by ring
      rw [e3]; linarith
    linarith
  have hE := hcoord e _ _ _ hc1.1 hr1 hve
  have hN := hcoord n _ _ _ hc1.2 hr2 hvn
  have hn4 : ‖n - nrm Q‖ ≤ 4 * g := hnerr
  have hn0 := norm_nonneg (n - nrm Q)
  apply plankFrame_fit (by positivity) (by positivity) he hn hen
  · refine hE.trans ?_
    have h1 : 2 * ‖gm‖ * r₁ Q ≤ K * S₁ := by
      refine le_trans ?_ hA₁
      gcongr
    have h2 : q₁ / 2 * (2 * ‖gv‖ * r₁ Q) ≤ K * S₁ := by
      refine le_trans ?_ hA₁
      have e : q₁ / 2 * (2 * ‖gv‖ * r₁ Q) = 2 * (q₁ / 2 * ‖gv‖) * r₁ Q := by ring
      rw [e]
      gcongr
    have h3 : q₁ / 2 * (S₁ / q₁) = S₁ / 2 := by field_simp
    have e : q₁ / 2 * (2 * ‖gv‖ * r₁ Q + S₁ / q₁) =
        q₁ / 2 * (2 * ‖gv‖ * r₁ Q) + q₁ / 2 * (S₁ / q₁) := by ring
    rw [e, h3]
    linarith
  · refine hN.trans ?_
    have h1 : ‖gm‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gm‖ * r₁ Q) ≤ K * S₂ := by
      refine le_trans ?_ hA₂
      have a1 : ‖gm‖ * r₂ Q ≤ ρ * r₂ Q := by gcongr
      have a2 : ‖n - nrm Q‖ * (2 * ‖gm‖ * r₁ Q) ≤ 4 * g * (2 * ρ * r₁ Q) := by gcongr
      linarith
    have h2 : q₁ / 2 * (‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q)) ≤ K * S₂ := by
      refine le_trans ?_ hA₂
      have e : q₁ / 2 * (‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q)) =
          (q₁ / 2 * ‖gv‖) * r₂ Q + ‖n - nrm Q‖ * (2 * (q₁ / 2 * ‖gv‖) * r₁ Q) := by ring
      rw [e]
      have a1 : (q₁ / 2 * ‖gv‖) * r₂ Q ≤ ρ * r₂ Q := by gcongr
      have a2 : ‖n - nrm Q‖ * (2 * (q₁ / 2 * ‖gv‖) * r₁ Q) ≤ 4 * g * (2 * ρ * r₁ Q) := by
        gcongr
      linarith
    have h3 : q₁ / 2 * (S₂ / q₁) = S₂ / 2 := by field_simp
    have e : q₁ / 2 * (‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q) + S₂ / q₁) =
        q₁ / 2 * (‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q)) + q₁ / 2 * (S₂ / q₁) := by ring
    rw [e, h3]
    linarith

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
