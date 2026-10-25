import Mathlib

/- Adapted from this LOT tree, o218 session x0857, branch split/s091,
   Depths.lean and BufferedDepths.lean. The directional margin is strengthened
   from /4 to /16, and both coarse depth buffers are chosen together. -/

namespace Submission.Obl.k4_horizontal_endpoint_three_projections

theorem exists_projection_mesh {U e₀ buffer : ℝ}
    (hU : 0 < U) (he₀ : 0 < e₀) (hbuffer : 0 < buffer) :
    ∃ M : ℝ, 0 < M ∧ M < e₀ ∧ buffer * M < U ∧ buffer * M < e₀ := by
  let M := min (U / (2 * (buffer + 1))) (e₀ / (2 * (buffer + 1)))
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : 0 < 2 * (buffer + 1) := by positivity
  have hMU := (le_div_iff₀ hb).mp (show M ≤ U / (2 * (buffer + 1)) from min_le_left _ _)
  have hMe := (le_div_iff₀ hb).mp (show M ≤ e₀ / (2 * (buffer + 1)) from min_le_right _ _)
  exact ⟨M, hM, by nlinarith, by nlinarith, by nlinarith⟩

theorem exists_split_depths {d κ sMax U M buffer : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hκ2 : 2 * κ < 1)
    (hsMax : 0 < sMax) (hU : 2 * sMax < U) (hM : 0 < M)
    (hbuffer : 0 < buffer) :
    ∃ s₀ s u v : ℝ,
      0 < s₀ ∧ 3 * s₀ / 2 < sMax ∧ buffer * s₀ < M ∧ 100 * s₀ < M ∧
      s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - d) * u / 4 ∧
      s + u < U ∧ s + u < 3 * s₀ / 2 ∧
      (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀) ∧
      (10 / (1 - d) + 3) * u < κ * s ∧
      (∀ h : Fin 3, s₀ < (![s, s + u, s + v] : Fin 3 → ℝ) h ∧
        (![s, s + u, s + v] : Fin 3 → ℝ) h - s₀ ≤
          s₀ * min κ (1 - 2 * κ) / 16) := by
  have hd' : 0 < 1 - d := by linarith
  have hκ' : 0 < 1 - 2 * κ := by linarith
  let s₀ := min (sMax / 4) (M / (2 * (buffer + 100)))
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have hs₀Max : s₀ ≤ sMax / 4 := min_le_left _ _
  have hs₀M : s₀ * (2 * (buffer + 100)) ≤ M :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let gain := s₀ * min κ (1 - 2 * κ) / 16
  have hgain : 0 < gain := by dsimp [gain]; positivity
  let B := min (s₀ / 2) gain
  have hB : 0 < B := by dsimp [B]; positivity
  have hBs : B ≤ s₀ / 2 := min_le_left _ _
  have hBg : B ≤ gain := min_le_right _ _
  let δ := B / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let C := 10 / (1 - d) + 3
  have hC : 0 < C := by dsimp [C]; positivity
  let u := min (δ / 4) (κ * δ / (4 * C))
  have hu : 0 < u := by dsimp [u]; positivity
  have huδ : u ≤ δ / 4 := min_le_left _ _
  have huC : u ≤ κ * δ / (4 * C) := min_le_right _ _
  have hCu : C * u ≤ κ * δ / 4 := by
    have := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp huC
    nlinarith
  let v := (1 - d) * u / 8
  have hv : 0 < v := by dsimp [v]; positivity
  have hvu : v < u := by dsimp [v]; nlinarith
  have hδu : δ + u < B := by dsimp [δ] at *; linarith
  refine ⟨s₀, s₀ + δ, u, v, hs₀, ?_, ?_, ?_, ?_, hu, hv, hvu,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · nlinarith [mul_pos hs₀ hbuffer]
  · nlinarith [mul_pos hs₀ hbuffer]
  · linarith
  · dsimp [v]; nlinarith
  · linarith
  · linarith
  · change C * u < 2 * κ * (s₀ + δ - s₀)
    nlinarith [mul_pos hκ hδ]
  · change C * u < κ * (s₀ + δ)
    nlinarith [mul_pos hκ hδ, mul_pos hκ hs₀]
  · intro h
    fin_cases h
    · change s₀ < s₀ + δ ∧ s₀ + δ - s₀ ≤ gain
      constructor <;> linarith
    · change s₀ < s₀ + δ + u ∧ s₀ + δ + u - s₀ ≤ gain
      constructor <;> linarith
    · change s₀ < s₀ + δ + v ∧ s₀ + δ + v - s₀ ≤ gain
      constructor <;> linarith

end Submission.Obl.k4_horizontal_endpoint_three_projections
