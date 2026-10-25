import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Filter

noncomputable section

/-- The literal raw-cap and geometric numerical premises of native agreement and
the common-field cell cap, at their fixed physical resolutions. -/
structure NativeRawBudgetsAt (N K H q g s u M B σ : ℝ) : Prop where
  chart_q : N ^ (-M) ≤ q
  chart_one : N ^ (-M) ≤ 1
  field_g : N ^ (-B) ≤ g
  chart_precision : N ^ (-M) ≤ N ^ (-2 * u)
  field_precision : N ^ (-B) ≤ N ^ (-2 * u)
  source_width : K * N ^ (-M) ≤ q * g * N ^ (-2 * u)
  rho2 : N ^ (-M) / q + N ^ (-M) * (2 * K + N ^ (-M)) / 2 ≤ N ^ (-2 * u)
  rhoN : 2 * N ^ (-M) + (q * N ^ (-M) + q * N ^ (-B)) * (3 * K + N ^ (-M)) +
    (K + 1) * (q * N ^ (-B)) ≤ 12 * K * N ^ (-M)
  agree_time : N ^ (-(10 * B)) ≤ q * N ^ (-M) / 2
  agree_chart : 5 * K ^ 2 * N ^ (-(10 * B)) ≤ N ^ (-M)
  agree_width : 5 * K ^ 2 * N ^ (-(10 * B)) ≤ q * g * N ^ (-2 * u) / 2
  agree_base : (3 + 3 * K) * N ^ (-(10 * B)) ≤ q * g
  agree_lip : 3 * (H * N ^ (2 * s)) * N ^ (-(10 * B)) +
    N ^ (-s) * H * (3 * K + 7) * (3 * K + 3) * N ^ (-(10 * B)) / (q * g) ≤ N ^ (-(s + u))
  field_fit : 2 * K * N ^ (-s) ≤ N ^ (-(s - 2 * σ))
  field_mesh : (K + K ^ 2 + 1) * N ^ (-(10 * B)) ≤ q * N ^ (-B) / 2
  field_lip : 3 * (H * N ^ (2 * s)) * N ^ (-(10 * B)) ≤ N ^ (-(s - 2 * σ))

/-- A single subpower growth threshold pays every fixed raw-mesh constant.
The weaker coarse lower bounds used here follow from every original rate `κ≤1`. -/
theorem native_raw_budgets_of_power {N K H q g s u M B σ : ℝ}
    (hN : 1 ≤ N) (hs : 0 ≤ s) (hu : 0 ≤ u) (hM : 0 < M)
    (hsu : s + u < M / 10) (hB : 10 * M ≤ B)
    (hσ : 0 ≤ σ) (hσM : 100 * σ ≤ M)
    (hK : 1 ≤ K) (hH : 1 ≤ H) (hKN : K ≤ N ^ σ) (hHN : H ≤ N ^ σ)
    (hlarge : 200 ≤ N ^ σ) (hqlo : N ^ (-s) / K ≤ q) (hq₁ : q ≤ 1)
    (hglo : N ^ (-s) ≤ g) : NativeRawBudgetsAt N K H q g s u M B σ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hA : 1 ≤ N ^ σ := Real.one_le_rpow hN hσ
  have hQp : 0 < N ^ (-s - σ) := Real.rpow_pos_of_pos hNp _
  have hQ : N ^ (-s - σ) ≤ q := by
    calc
      _ = N ^ (-s) / N ^ σ := by rw [← Real.rpow_sub hNp]
      _ ≤ N ^ (-s) / K := div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hKp hKN
      _ ≤ q := hqlo
  have hqp : 0 < q := hQp.trans_le hQ
  have hgp : 0 < g := (Real.rpow_pos_of_pos hNp _).trans_le hglo
  have hQG : N ^ (-2 * s - σ) ≤ q * g := by
    calc
      _ = N ^ (-s - σ) * N ^ (-s) := by rw [← Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := mul_le_mul hQ hglo (Real.rpow_nonneg hNp.le _) hqp.le
  have hpow (j : ℕ) : (N ^ σ) ^ j = N ^ ((j : ℝ) * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hp2 : (N ^ σ) ^ 2 = N ^ (2 * σ) := by simpa only [Nat.cast_ofNat] using hpow 2
  have hp3 : (N ^ σ) ^ 3 = N ^ (3 * σ) := by simpa only [Nat.cast_ofNat] using hpow 3
  have hp4 : (N ^ σ) ^ 4 = N ^ (4 * σ) := by simpa only [Nat.cast_ofNat] using hpow 4
  have htwoK : 2 * K ≤ N ^ (2 * σ) := by
    rw [← hp2]
    nlinarith only [hKN, hlarge, sq_nonneg (N ^ σ - 2)]
  have hthreeH : 3 * H ≤ N ^ (2 * σ) := by
    rw [← hp2]
    nlinarith only [hHN, hlarge, sq_nonneg (N ^ σ - 3)]
  have htenK : 10 * K ^ 2 ≤ N ^ (3 * σ) := by
    calc
      _ ≤ N ^ σ * (N ^ σ) ^ 2 := by gcongr; linarith
      _ = _ := by rw [← pow_succ']; exact hp3
  have hpolyK : 2 * (K + K ^ 2 + 1) ≤ N ^ (3 * σ) := by
    calc
      _ ≤ 6 * (N ^ σ) ^ 2 := by
        have hsq : K ^ 2 ≤ (N ^ σ) ^ 2 := by gcongr
        nlinarith only [hKN, hsq, hA, sq_nonneg (N ^ σ - 1)]
      _ ≤ N ^ σ * (N ^ σ) ^ 2 := by gcongr; linarith
      _ = _ := by rw [← pow_succ']; exact hp3
  have hbaseK : 3 + 3 * K ≤ N ^ (2 * σ) := by
    rw [← hp2]
    nlinarith only [hKN, hlarge, sq_nonneg (N ^ σ - 6)]
  have hcoeff : H * (3 * K + 7) * (3 * K + 3) ≤ N ^ (4 * σ) := by
    calc
      _ ≤ N ^ σ * (10 * N ^ σ) * (6 * N ^ σ) := by gcongr <;> linarith
      _ = 60 * (N ^ σ) ^ 3 := by ring
      _ ≤ N ^ σ * (N ^ σ) ^ 3 := by gcongr; linarith
      _ = _ := by rw [← pow_succ']; exact hp4
  have hrawL : 3 * (H * N ^ (2 * s)) * N ^ (-(10 * B)) ≤ N ^ (2 * σ + 2 * s - 10 * B) := by
    calc
      _ ≤ N ^ (2 * σ) * N ^ (2 * s) * N ^ (-(10 * B)) := by
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hthreeH (Real.rpow_nonneg hNp.le _))
          (Real.rpow_nonneg hNp.le _) using 1 <;> ring
      _ = _ := by rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; congr 1
  have hrawQ : N ^ (-s) * H * (3 * K + 7) * (3 * K + 3) * N ^ (-(10 * B)) / (q * g) ≤
      N ^ (5 * σ + s - 10 * B) := by
    calc
      _ ≤ (N ^ (-s) * N ^ (4 * σ) * N ^ (-(10 * B))) / N ^ (-2 * s - σ) := by
        apply div_le_div₀ (by positivity) _ (Real.rpow_pos_of_pos hNp _) hQG
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hNp.le _))
          (Real.rpow_nonneg hNp.le _) using 1 <;> ring
      _ = _ := by
        rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_sub hNp]
        congr 1
        ring
  have hχ : N ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hδχ : N ^ (-B) ≤ N ^ (-M) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hrhoA : N ^ (-M) / q ≤ N ^ (s + σ - M) := by
    calc
      _ ≤ N ^ (-M) / N ^ (-s - σ) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hQp hQ
      _ = _ := by rw [← Real.rpow_sub hNp]; congr 1; ring
  have hrhoB : N ^ (-M) * (2 * K + N ^ (-M)) / 2 ≤ N ^ (2 * σ - M) := by
    have hco : (2 * K + N ^ (-M)) / 2 ≤ N ^ (2 * σ) := by
      nlinarith only [htwoK, hχ, Real.one_le_rpow hN (show 0 ≤ 2 * σ by positivity)]
    calc
      _ = N ^ (-M) * ((2 * K + N ^ (-M)) / 2) := by ring
      _ ≤ N ^ (-M) * N ^ (2 * σ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  refine ⟨?_, hχ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith : -M ≤ -s - σ)).trans hQ
  · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith : -B ≤ -s)).trans hglo
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · calc
      _ ≤ N ^ σ * N ^ (-M) := by gcongr
      _ = N ^ (σ - M) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ N ^ (-2 * s - σ - 2 * u) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N ^ (-2 * s - σ) * N ^ (-2 * u) := by rw [← Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := by gcongr
  · have hmax : N ^ (s + σ - M) + N ^ (2 * σ - M) ≤ N ^ (s + 3 * σ - M) := by
      calc
        _ ≤ 2 * N ^ (s + 2 * σ - M) := by
          have h1 := Real.rpow_le_rpow_of_exponent_le hN (show s + σ - M ≤ s + 2 * σ - M by linarith)
          have h2 := Real.rpow_le_rpow_of_exponent_le hN (show 2 * σ - M ≤ s + 2 * σ - M by linarith)
          linarith
        _ ≤ N ^ σ * N ^ (s + 2 * σ - M) := by gcongr; linarith
        _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
    exact (add_le_add hrhoA hrhoB).trans (hmax.trans
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)))
  · calc
      _ ≤ 2 * N ^ (-M) + (1 * N ^ (-M) + 1 * N ^ (-M)) * (3 * K + 1) +
          (K + 1) * (1 * N ^ (-M)) := by gcongr
      _ ≤ 12 * K * N ^ (-M) := by nlinarith only [mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hNp.le (-M))]
  · have hh : 2 * N ^ (-(10 * B)) ≤ q * N ^ (-M) := by
      calc
        _ ≤ N ^ σ * N ^ (-(10 * B)) := by gcongr; linarith
        _ = N ^ (σ - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1
        _ ≤ N ^ (-s - σ - M) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = N ^ (-s - σ) * N ^ (-M) := by rw [← Real.rpow_add hNp]; congr 1
        _ ≤ _ := by gcongr
    linarith
  · calc
      _ ≤ N ^ (3 * σ) * N ^ (-(10 * B)) := by gcongr; nlinarith only [htenK, sq_nonneg K]
      _ = N ^ (3 * σ - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · have hh : 10 * K ^ 2 * N ^ (-(10 * B)) ≤ q * g * N ^ (-2 * u) := by
      calc
        _ ≤ N ^ (3 * σ) * N ^ (-(10 * B)) := by gcongr
        _ = N ^ (3 * σ - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1
        _ ≤ N ^ (-2 * s - σ - 2 * u) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = N ^ (-2 * s - σ) * N ^ (-2 * u) := by rw [← Real.rpow_add hNp]; congr 1; ring
        _ ≤ _ := by gcongr
    linarith
  · calc
      _ ≤ N ^ (2 * σ) * N ^ (-(10 * B)) := by gcongr
      _ = N ^ (2 * σ - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ N ^ (-2 * s - σ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ ≤ _ := hQG
  · calc
      _ ≤ N ^ (2 * σ + 2 * s - 10 * B) + N ^ (5 * σ + s - 10 * B) := add_le_add hrawL hrawQ
      _ ≤ 2 * N ^ (5 * σ + 2 * s - 10 * B) := by
        have h1 := Real.rpow_le_rpow_of_exponent_le hN
          (show 2 * σ + 2 * s - 10 * B ≤ 5 * σ + 2 * s - 10 * B by linarith)
        have h2 := Real.rpow_le_rpow_of_exponent_le hN
          (show 5 * σ + s - 10 * B ≤ 5 * σ + 2 * s - 10 * B by linarith)
        linarith
      _ ≤ N ^ σ * N ^ (5 * σ + 2 * s - 10 * B) := by gcongr; linarith
      _ = N ^ (6 * σ + 2 * s - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · calc
      _ ≤ N ^ (2 * σ) * N ^ (-s) := by gcongr
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  · have hh : 2 * ((K + K ^ 2 + 1) * N ^ (-(10 * B))) ≤ q * N ^ (-B) := by
      calc
        _ ≤ N ^ (3 * σ) * N ^ (-(10 * B)) := by nlinarith only [mul_le_mul_of_nonneg_right hpolyK (Real.rpow_nonneg hNp.le (-(10 * B)))]
        _ = N ^ (3 * σ - 10 * B) := by rw [← Real.rpow_add hNp]; congr 1
        _ ≤ N ^ (-s - σ - B) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = N ^ (-s - σ) * N ^ (-B) := by rw [← Real.rpow_add hNp]; congr 1
        _ ≤ _ := by gcongr
    linarith
  · exact hrawL.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

/-- Every fixed positive subpower loss eventually supplies all raw-cap budgets,
uniformly in the original dyadic length and every original horizontal rate. -/
theorem eventually_native_raw_budgets {s u M B σ : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hM : 0 < M)
    (hsu : s + u < M / 10) (hB : 10 * M ≤ B) (hσ : 0 < σ) (hσM : 100 * σ ≤ M) :
    ∀ᶠ N : ℝ in atTop, ∀ K H q κ : ℝ, 1 ≤ K → 1 ≤ H → K ≤ N ^ σ → H ≤ N ^ σ →
      κ ≤ 1 → N ^ (-κ * s) / K ≤ q → q ≤ 1 →
      NativeRawBudgetsAt N K H q (N ^ (-κ * s)) s u M B σ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hσ).eventually_ge_atTop 200] with N hN hlarge
  intro K H q κ hK hH hKN hHN hκ hqlo hq₁
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hp : N ^ (-s) ≤ N ^ (-κ * s) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  exact native_raw_budgets_of_power hN hs hu hM hsu hB hσ.le hσM hK hH hKN hHN hlarge
    ((div_le_div_of_nonneg_right hp hKp.le).trans hqlo) hq₁ hp

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
