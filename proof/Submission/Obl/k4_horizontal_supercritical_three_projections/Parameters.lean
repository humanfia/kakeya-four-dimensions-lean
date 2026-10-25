import Mathlib

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

/-- Fixed depths with all the strict margins used by the three scalar projections. -/
structure ProjectionDepths (d κ U e₀ buffer : ℝ) where
  s₀ : ℝ
  s : ℝ
  u : ℝ
  v : ℝ
  s₀_pos : 0 < s₀
  below_U : buffer * s₀ < U
  below_e₀ : buffer * s₀ < e₀
  s₀_lt_s : s₀ < s
  u_pos : 0 < u
  v_pos : 0 < v
  v_lt_u : v < u
  v_small : v < (1 - d) * u / 4
  depth_below_U : s + u < U
  depth_near : s + u < 3 * s₀ / 2
  depth_supercritical : s + u < 2 * κ * s₀
  wide_transverse : (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀)
  wide_time : (10 / (1 - d) + 3) * u < κ * s

/-- The exponents are chosen before requesting any subpower loss. -/
theorem exists_projectionDepths {d κ U e₀ buffer : ℝ}
    (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hκ₀ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hU : 0 < U) (he₀ : 0 < e₀) (hκ : 1 < 2 * κ) (hb : 100 < buffer) :
    Nonempty (ProjectionDepths d κ U e₀ buffer) := by
  let s₀ := min U e₀ / (2 * buffer)
  let C := 10 / (1 - d) + 3
  let δ := min (s₀ / 8) ((2 * κ - 1) * s₀ / 4)
  let u := κ * δ / (8 * C)
  let v := (1 - d) * u / 8
  have hb₀ : 0 < buffer := by linarith
  have hden : 0 < 1 - d := by linarith
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have hC : 3 < C := by
    have := div_pos (show (0 : ℝ) < 10 by norm_num) hden
    dsimp [C]
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ s₀ / 8 := min_le_left _ _
  have hδ₂ : δ ≤ (2 * κ - 1) * s₀ / 4 := min_le_right _ _
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hCu : C * u = κ * δ / 8 := by dsimp [u]; field_simp
  have huδ : u ≤ δ / 8 := by
    apply (div_le_iff₀ (show 0 < 8 * C by positivity)).mpr
    have : κ * δ ≤ δ * C := by nlinarith
    nlinarith
  have hbs₀ : buffer * s₀ = min U e₀ / 2 := by dsimp [s₀]; field_simp
  have hU₀ : buffer * s₀ < U := by
    rw [hbs₀]
    linarith [min_le_left U e₀]
  have he₀₀ : buffer * s₀ < e₀ := by
    rw [hbs₀]
    linarith [min_le_right U e₀]
  refine ⟨{
    s₀ := s₀
    s := s₀ + δ
    u := u
    v := v
    s₀_pos := hs₀
    below_U := hU₀
    below_e₀ := he₀₀
    s₀_lt_s := by linarith
    u_pos := hu
    v_pos := hv
    v_lt_u := ?_
    v_small := ?_
    depth_below_U := ?_
    depth_near := ?_
    depth_supercritical := ?_
    wide_transverse := ?_
    wide_time := ?_ }⟩
  · dsimp [v]
    nlinarith [mul_nonneg hd₀ hu.le]
  · dsimp [v]
    nlinarith [mul_pos hden hu]
  · have : (s₀ + δ) + u < 3 * s₀ / 2 := by linarith
    have : 3 * s₀ / 2 < buffer * s₀ := by nlinarith
    linarith
  · linarith
  · nlinarith
  · change C * u < 2 * κ * ((s₀ + δ) - s₀)
    rw [hCu]
    nlinarith [mul_pos hκ₀ hδ]
  · change C * u < κ * (s₀ + δ)
    rw [hCu]
    nlinarith [mul_pos hκ₀ hs₀, mul_pos hκ₀ hδ]

end Submission.Obl.k4_horizontal_supercritical_three_projections
