import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Filter

/-- The exact near-chart radius costs at most twelve original velocity
widths times the native geometric slack. -/
theorem agreement_near_radius_bound {K q χ δz : ℝ}
    (hK : 1 ≤ K) (_hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ 1) (hz0 : 0 ≤ δz) (hz : δz ≤ χ) :
    2 * χ + (q * χ + q * δz) * (3 * K + χ) + (K + 1) * (q * δz) ≤ 12 * K * χ := by
  have hqχ : q * χ ≤ χ := mul_le_of_le_one_left hχ0 hq
  have hqz : q * δz ≤ χ := (mul_le_of_le_one_left hz0 hq).trans hz
  calc
    _ ≤ 2 * χ + (2 * χ) * (3 * K + 1) + (K + 1) * χ := by
      gcongr
      linarith
    _ = (5 + 7 * K) * χ := by ring
    _ ≤ (12 * K) * χ := by gcongr; linarith
    _ = _ := by ring

/-- The buffered chart width makes the displacement of source reference
points smaller than the squared offset scale. -/
theorem agreement_reference_drift_bound {N K q V M u σ : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N ^ σ)
    (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hq : N ^ (-V) / K ≤ q) (hconst : 3 ≤ N ^ σ)
    (hmargin : 2 * σ + V + 2 * u ≤ M) :
    N ^ (-M) / q + N ^ (-M) * (2 * K + N ^ (-M)) / 2 ≤ N ^ (-2 * u) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hK₀ : 0 < K := by linarith
  have hq0 : 0 < q := (div_pos (Real.rpow_pos_of_pos hN₀ _) hK₀).trans_le hq
  have hχ : N ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hqlo : N ^ (-V - σ) ≤ q := by
    calc
      _ = N ^ (-V) / N ^ σ := by rw [← Real.rpow_sub hN₀]
      _ ≤ N ^ (-V) / K := div_le_div_of_nonneg_left (Real.rpow_nonneg hN₀.le _) hK₀ hKN
      _ ≤ q := hq
  have hratio : N ^ (-M) / q ≤ N ^ (V + σ - M) := by
    calc
      _ ≤ N ^ (-M) / N ^ (-V - σ) := by gcongr
      _ = _ := by rw [← Real.rpow_sub hN₀]; congr 1; ring
  have hmult : N ^ (-M) * (2 * K + N ^ (-M)) / 2 ≤
      (3 / 2 : ℝ) * N ^ (V + σ - M) := by
    calc
      _ ≤ N ^ (-M) * (3 * K) / 2 := by gcongr; linarith
      _ ≤ (3 / 2 : ℝ) * (N ^ σ * N ^ (-M)) := by nlinarith [Real.rpow_nonneg hN₀.le (-M)]
      _ = (3 / 2 : ℝ) * N ^ (σ - M) := by rw [← Real.rpow_add hN₀]; congr 2
      _ ≤ _ := by gcongr; linarith
  calc
    _ ≤ 3 * N ^ (V + σ - M) := by nlinarith [Real.rpow_nonneg hN₀.le (V + σ - M)]
    _ ≤ N ^ σ * N ^ (V + σ - M) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hN₀.le _)
    _ = N ^ (2 * σ + V - M) := by rw [← Real.rpow_add hN₀]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The fine-state error leaves half the allowed coefficient discrepancy
for the derivative comparison. -/
theorem agreement_gap_bound {N H u τ δz δt ρ : ℝ}
    (_hN : 1 ≤ N) (hH : 0 ≤ H)
    (hz : δz ≤ N ^ (-2 * u)) (ht : δt ≤ N ^ (-2 * u)) (hρ : ρ ≤ N ^ (-2 * u))
    (hbudget : 10 * H * N ^ (-2 * u) ≤ N ^ (-τ)) :
    N ^ (-τ) / 2 + 2 * H * (δz + δt / 2 + ρ) ≤ N ^ (-τ) := by
  have hfine : 2 * H * (δz + δt / 2 + ρ) ≤ 5 * H * N ^ (-2 * u) := by
    calc
      _ ≤ 2 * H * (N ^ (-2 * u) + N ^ (-2 * u) / 2 + N ^ (-2 * u)) := by gcongr
      _ = _ := by ring
  linarith

/-- The selected positive derivative threshold never exceeds half of the
comparison gap. -/
theorem agreement_threshold_bounds {N d u : ℝ}
    (hN : 1 ≤ N) (hd : d ≤ 1) (hu : 0 ≤ u) :
    let e := N ^ (-((1 - d) * u / 2)) / 2
    0 < (e / 2) * N ^ (-((1 - d) * u) / 8) ∧
      (e / 2) * N ^ (-((1 - d) * u) / 8) ≤ e / 2 := by
  dsimp only
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  constructor
  · positivity
  · apply mul_le_of_le_one_right (by positivity)
    exact Real.rpow_le_one_of_one_le_of_nonpos hN
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hd) hu])

/-- The literal coefficient-comparison width is paid by the coarse offset
accuracy; every fine coordinate mesh is at most its square. -/
theorem agreement_width_bound {N K H u δt δz δU δX ρ : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hH : 1 ≤ H) (hu : 0 ≤ u)
    (ht0 : 0 ≤ δt) (hz0 : 0 ≤ δz) (hU0 : 0 ≤ δU) (_hX0 : 0 ≤ δX) (hρ0 : 0 ≤ ρ)
    (ht : δt ≤ N ^ (-2 * u)) (hz : δz ≤ N ^ (-2 * u))
    (hU : δU ≤ N ^ (-2 * u)) (hX : δX ≤ N ^ (-2 * u)) (hρ : ρ ≤ N ^ (-2 * u)) :
    (2 * H + 2) * N ^ (-u) + δX + H *
      ((1 + 2 * 2 + (K + ρ) + K) * (2 * (δt / 2) + δz) +
        (1 + 2 + 2 * (K + ρ) + K) * (2 * ρ + δz) +
        (1 + 2 + (K + ρ) + 2 * K) * δU) ≤
      100 * H * K ^ 2 * N ^ (-u) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hK₀ : 0 ≤ K := by linarith
  have hH₀ : 0 ≤ H := by linarith
  have htiny : 0 ≤ N ^ (-2 * u) := Real.rpow_nonneg hN₀.le _
  have htiny₁ : N ^ (-2 * u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have htiny_r : N ^ (-2 * u) ≤ N ^ (-u) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hρ₁ : ρ ≤ 1 := hρ.trans htiny₁
  have hA : 1 + 2 * 2 + (K + ρ) + K ≤ 8 * K := by linarith
  have hB : 1 + 2 + 2 * (K + ρ) + K ≤ 8 * K := by linarith
  have hC : 1 + 2 + (K + ρ) + 2 * K ≤ 7 * K := by linarith
  have hw :
      (1 + 2 * 2 + (K + ρ) + K) * (2 * (δt / 2) + δz) +
        (1 + 2 + 2 * (K + ρ) + K) * (2 * ρ + δz) +
        (1 + 2 + (K + ρ) + 2 * K) * δU ≤ 47 * K * N ^ (-2 * u) := by
    calc
      _ ≤ (8 * K) * (2 * N ^ (-2 * u)) +
          (8 * K) * (3 * N ^ (-2 * u)) + (7 * K) * N ^ (-2 * u) := by
        gcongr
        · linarith
        · linarith
      _ = _ := by ring
  have hKsq : K ≤ K ^ 2 := by nlinarith
  calc
    _ ≤ (2 * H + 2) * N ^ (-u) + N ^ (-2 * u) + H * (47 * K * N ^ (-2 * u)) := by
      gcongr
    _ ≤ (2 * H + 2) * N ^ (-u) + N ^ (-u) + H * (47 * K * N ^ (-u)) := by
      gcongr
    _ = (2 * H + 3 + 47 * H * K) * N ^ (-u) := by ring
    _ ≤ (100 * H * K ^ 2) * N ^ (-u) := by
      gcongr
      have hHK : H ≤ H * K := le_mul_of_one_le_right hH₀ hK
      have hHKsq : H * K ≤ H * K ^ 2 := mul_le_mul_of_nonneg_left hKsq hH₀
      nlinarith
    _ = _ := by ring

/-- The matching threshold balances the derivative and offset alternatives.
The number of offsets uses the original dimension `d`. -/
theorem agreement_matching_factor_bound {N K H d u δU : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hH : 1 ≤ H) (hd : d ≤ 1) (hu : 0 ≤ u)
    (hU0 : 0 ≤ δU) (hU : δU ≤ N ^ (-2 * u)) :
    let τ := (1 - d) * u / 2
    let e := N ^ (-τ) / 2
    let θm := (e / 2) * N ^ (-((1 - d) * u) / 8)
    θm * (4 * (K + δU) + 2) / e +
      4 * (H * N ^ (d * u)) *
        (100 * H * K ^ 2 * N ^ (-u) + δU * (24 * H * K)) / θm ≤
      2000 * H ^ 2 * K ^ 2 * N ^ (-((1 - d) * u) / 8) := by
  dsimp only
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hK₀ : 0 ≤ K := by linarith
  have hH₀ : 0 ≤ H := by linarith
  have hU₁ : δU ≤ 1 := hU.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith))
  have hU_r : δU ≤ N ^ (-u) := hU.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have he : 0 < N ^ (-((1 - d) * u / 2)) / 2 := by positivity
  have hθ : 0 < (N ^ (-((1 - d) * u / 2)) / 2 / 2) *
      N ^ (-((1 - d) * u) / 8) := by positivity
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  have hfirst :
      ((N ^ (-((1 - d) * u / 2)) / 2 / 2) * N ^ (-((1 - d) * u) / 8)) *
        (4 * (K + δU) + 2) / (N ^ (-((1 - d) * u / 2)) / 2) ≤
      5 * K * N ^ (-((1 - d) * u) / 8) := by
    calc
      _ = ((4 * (K + δU) + 2) / 2) * N ^ (-((1 - d) * u) / 8) := by
        field_simp
      _ ≤ (5 * K) * N ^ (-((1 - d) * u) / 8) := by gcongr; linarith
      _ = _ := by ring
  have hwidth : 100 * H * K ^ 2 * N ^ (-u) + δU * (24 * H * K) ≤
      124 * H * K ^ 2 * N ^ (-u) := by
    calc
      _ ≤ 100 * H * K ^ 2 * N ^ (-u) + N ^ (-u) * (24 * H * K ^ 2) := by gcongr
      _ = _ := by ring
  have hratio : N ^ (d * u) * N ^ (-u) /
      ((N ^ (-((1 - d) * u / 2)) / 2 / 2) * N ^ (-((1 - d) * u) / 8)) =
      4 * N ^ (-3 * ((1 - d) * u) / 8) := by
    calc
      _ = 4 * (N ^ (d * u) * N ^ (-u) /
          (N ^ (-((1 - d) * u / 2)) * N ^ (-((1 - d) * u) / 8))) := by
        field_simp
        ring
      _ = 4 * N ^ (d * u + -u - (-((1 - d) * u / 2) + -((1 - d) * u) / 8)) := by
        rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀, ← Real.rpow_sub hN₀]
      _ = _ := by congr 2; ring
  have hsecond :
      4 * (H * N ^ (d * u)) *
        (100 * H * K ^ 2 * N ^ (-u) + δU * (24 * H * K)) /
          ((N ^ (-((1 - d) * u / 2)) / 2 / 2) * N ^ (-((1 - d) * u) / 8)) ≤
      1984 * H ^ 2 * K ^ 2 * N ^ (-((1 - d) * u) / 8) := by
    calc
      _ ≤ 4 * (H * N ^ (d * u)) * (124 * H * K ^ 2 * N ^ (-u)) /
          ((N ^ (-((1 - d) * u / 2)) / 2 / 2) * N ^ (-((1 - d) * u) / 8)) := by gcongr
      _ = (496 * H ^ 2 * K ^ 2) * (N ^ (d * u) * N ^ (-u) /
          ((N ^ (-((1 - d) * u / 2)) / 2 / 2) * N ^ (-((1 - d) * u) / 8))) := by ring
      _ = (1984 * H ^ 2 * K ^ 2) * N ^ (-3 * ((1 - d) * u) / 8) := by rw [hratio]; ring
      _ ≤ (1984 * H ^ 2 * K ^ 2) * N ^ (-((1 - d) * u) / 8) := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.mpr hd) hu]
      _ = _ := by ring
  have hfirst' : 5 * K * N ^ (-((1 - d) * u) / 8) ≤
      5 * H ^ 2 * K ^ 2 * N ^ (-((1 - d) * u) / 8) := by gcongr; nlinarith
  linarith [mul_nonneg (by positivity : 0 ≤ H ^ 2 * K ^ 2)
    (Real.rpow_nonneg hN₀.le (-((1 - d) * u) / 8))]

/-- Subpower constants leave a fixed power saving in the actual matching
factor used by coefficient agreement. -/
theorem eventually_agreement_matching_factor {d u σ : ℝ}
    (hd : d ≤ 1) (hu : 0 ≤ u) (_hσ : 0 ≤ σ) (hgap : 64 * σ < (1 - d) * u) :
    ∀ᶠ N : ℝ in atTop, ∀ K H δU : ℝ,
      1 ≤ K → K ≤ N ^ σ → 1 ≤ H → H ≤ N ^ σ →
      0 ≤ δU → δU ≤ N ^ (-2 * u) →
      let τ := (1 - d) * u / 2
      let e := N ^ (-τ) / 2
      let θm := (e / 2) * N ^ (-((1 - d) * u) / 8)
      θm * (4 * (K + δU) + 2) / e +
        4 * (H * N ^ (d * u)) *
          (100 * H * K ^ 2 * N ^ (-u) + δU * (24 * H * K)) / θm ≤
        N ^ (-((1 - d) * u) / 16) := by
  have hmargin : 4 * σ - ((1 - d) * u) / 8 < -((1 - d) * u) / 16 := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 2000 hmargin]
      with N hN hbudget
  intro K H δU hK hKN hH hHN hU0 hU
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  refine (agreement_matching_factor_bound hN hK hH hd hu hU0 hU).trans ?_
  calc
    _ ≤ 2000 * (N ^ σ) ^ 2 * (N ^ σ) ^ 2 * N ^ (-((1 - d) * u) / 8) := by gcongr
    _ = 2000 * N ^ (4 * σ - ((1 - d) * u) / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le]
      rw [mul_assoc (2000 : ℝ), ← Real.rpow_add hN₀,
        mul_assoc (2000 : ℝ), ← Real.rpow_add hN₀]
      congr 2
      ring
    _ ≤ _ := hbudget

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
