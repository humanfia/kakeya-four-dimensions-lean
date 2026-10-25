import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeFinal
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The exact source/time factor in coefficient agreement, in real units. -/
def agreementSourceCost (n K H q g χ δU A V : ℝ) : ℝ :=
  n * ((6000 * K * (q * χ / 2) * χ * (q * g * δU / 2 + K * χ) * A) *
    ((H * V) * (2 * H * (2 * (K * q + 2 * χ) / χ + 1)))) / δU

/-- The original finite time cells cost only an inverse chart width. -/
theorem agreement_time_card_bound {χ : ℝ} (hχ : 0 < χ) (hχ₁ : χ ≤ 1) :
    ((Finset.Icc (0 : ℤ) ⌊1 / χ⌋).card : ℝ) ≤ 3 / χ := by
  have hcard : ((Finset.Icc (0 : ℤ) ⌊1 / χ⌋).card : ℝ) ≤ 1 / χ + 2 := by
    simpa using Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
      (show (0 : ℝ) ≤ 1 / χ by positivity)
  have hdiv : 1 ≤ 1 / χ := (le_div_iff₀ hχ).mpr (by simpa using hχ₁)
  exact hcard.trans (by
    calc
      _ ≤ 3 * (1 / χ) := by linarith
      _ = _ := by ring)

/-- The hidden-window enlargement cancels the original offset count at precision `u`. -/
theorem agreement_hidden_window_bound {N H a d u sp : ℝ}
    (hN : 0 < N) (hH : 1 ≤ H) (ha : 0 < a) (hd : d ≤ 1)
    (hwin : a * (2 * H + 1) * N ^ (-u) = N ^ (-sp)) :
    (N ^ (-sp)) ^ d * N ^ (d * u) ≤ 3 * H * a ^ d := by
  have hH₀ : 0 < 2 * H + 1 := by linarith
  have hcancel : (N ^ (-u)) ^ d * N ^ (d * u) = 1 := by
    rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    convert Real.rpow_zero N using 2 <;> ring
  have hpow : (2 * H + 1) ^ d ≤ 3 * H := by
    calc
      _ ≤ (2 * H + 1) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hd
      _ ≤ _ := by rw [Real.rpow_one]; linarith
  rw [← hwin, Real.mul_rpow (mul_pos ha hH₀).le (Real.rpow_nonneg hN.le _),
    Real.mul_rpow ha.le hH₀.le]
  calc
    _ = a ^ d * (2 * H + 1) ^ d * ((N ^ (-u)) ^ d * N ^ (d * u)) := by ring
    _ = a ^ d * (2 * H + 1) ^ d := by rw [hcancel, mul_one]
    _ ≤ a ^ d * (3 * H) := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg ha.le _)
    _ = _ := by ring

/-- Normalize the literal source/time expression before any law is selected or
renormalized. Chart width and transverse precision cancel exactly. -/
theorem agreement_source_cost_bound {n K H q g χ δU A V ad : ℝ}
    (hn : 0 ≤ n) (hK : 1 ≤ K) (hH : 1 ≤ H) (hq : 0 < q) (hg : 0 ≤ g)
    (hχ : 0 < χ) (hχq : χ ≤ q) (hδU : 0 < δU)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (had : 0 ≤ ad)
    (hcard : n ≤ 3 / χ) (hwidth : K * χ ≤ q * g * δU)
    (hwindow : A * V ≤ 3 * H * ad) :
    agreementSourceCost n K H q g χ δU A V ≤ 600000 * K ^ 2 * H ^ 3 * q ^ 3 * g * ad := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hχKq : χ ≤ K * q := hχq.trans (le_mul_of_one_le_left hq.le hK)
  have hsrc : 2 * H * (2 * (K * q + 2 * χ) / χ + 1) ≤ 14 * H * K * q / χ := by
    apply (le_div_iff₀ hχ).mpr
    have heq : (2 * H * (2 * (K * q + 2 * χ) / χ + 1)) * χ =
        2 * H * (2 * K * q + 5 * χ) := by field_simp; ring
    rw [heq]
    calc
      _ ≤ 2 * H * (7 * K * q) := by gcongr; linarith
      _ = _ := by ring
  have hw : q * g * δU / 2 + K * χ ≤ (3 / 2 : ℝ) * q * g * δU := by linarith
  unfold agreementSourceCost
  calc
    _ ≤ (3 / χ) * ((6000 * K * (q * χ / 2) * χ * ((3 / 2 : ℝ) * q * g * δU) * A) *
        ((H * V) * (14 * H * K * q / χ))) / δU := by gcongr
    _ = (189000 * K ^ 2 * H ^ 2 * q ^ 3 * g) * (A * V) := by field_simp; ring
    _ ≤ (189000 * K ^ 2 * H ^ 2 * q ^ 3 * g) * (3 * H * ad) := by gcongr
    _ = 567000 * K ^ 2 * H ^ 3 * q ^ 3 * g * ad := by ring
    _ ≤ _ := by gcongr <;> norm_num

/-- The near-chart palette factor is subpower when the time mesh is the chart width. -/
theorem agreement_near_factor_bound {K H χ ρ : ℝ}
    (hK : 1 ≤ K) (hH : 0 ≤ H) (hχ : 0 < χ) (hρ : ρ ≤ 12 * K * χ) :
    2 * H * (2 * ρ / χ + 1) ≤ 50 * H * K := by
  have hh : ρ / χ ≤ 12 * K := (div_le_iff₀ hχ).mpr hρ
  calc
    _ ≤ 2 * H * (24 * K + 1) := by
      gcongr
      calc
        _ = 2 * (ρ / χ) := by ring
        _ ≤ 2 * (12 * K) := by gcongr
        _ = _ := by ring
    _ ≤ 2 * H * (25 * K) := by gcongr; linarith
    _ = _ := by ring

/-- The real source cost agrees exactly with the original extended-real expression. -/
theorem agreement_source_cost_ennreal {n : ℕ} {K H q g χ δU A V : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (hg : 0 ≤ g)
    (hχ : 0 < χ) (hδU : 0 < δU) (hA : 0 ≤ A) (hV : 0 ≤ V) :
    (n : ℝ≥0∞) * ((ENNReal.ofReal (6000 * K * (q * χ / 2) * χ *
      (q * g * δU / 2 + K * χ) * A) *
      (ENNReal.ofReal (H * V) * ENNReal.ofReal (2 * H * (2 * (K * q + 2 * χ) / χ + 1)))) /
      ENNReal.ofReal δU) = ENNReal.ofReal (agreementSourceCost n K H q g χ δU A V) := by
  symm
  simp (disch := positivity) only [agreementSourceCost, ENNReal.ofReal_div_of_pos hδU,
    ENNReal.ofReal_mul, ENNReal.ofReal_natCast, mul_div_assoc]

namespace ComparedBlock

open Submission.Obl.k4_critical_conditional_row_preparation

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}
    (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- The complete literal coefficient-agreement loss is charged to the unchanged
original `q ν(A_i)`. No posterior normalization or incidence floor is used. -/
theorem agreeLoss_le_original_reference
    (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hd : cfg.d ≤ 1)
    (hχ : 0 < χ) (hχ₁ : χ ≤ 1) (hχq : χ ≤ CB.frame.q)
    (hδt : P.δt = χ) (hδU : 0 < P.δU)
    (hwidth : cfg.K k * χ ≤ CB.frame.q * CB.frame.g * P.δU)
    {r sp vp θm w LipU ρN : ℝ}
    (hρ : ρN ≤ 12 * cfg.K k * χ)
    (hwin : CB.frame.a * (2 * H + 1) * cfg.N k ^ (-u) = cfg.N k ^ (-sp))
    (C₁ : ℝ≥0∞) :
    CB.agreeLoss P C₁ r sp vp θm w LipU ρN ≤
      C₁ * ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
        4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) *
      ENNReal.ofReal (100000000 * (cfg.K k) ^ 4 * H ^ 4) *
      (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) := by
  have hH : 1 ≤ H := CB.H_one
  have hK₀ : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hg : 0 < CB.frame.g := Real.rpow_pos_of_pos hN _
  have ha : 0 < CB.frame.a := Real.rpow_pos_of_pos hN _
  let n := (Finset.Icc (0 : ℤ) ⌊1 / χ⌋).card
  let A := (cfg.N k ^ (-sp)) ^ cfg.d
  let V := cfg.N k ^ (cfg.d * u)
  let ad := CB.frame.a ^ cfg.d
  have hA : 0 ≤ A := (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _).le
  have hV : 0 ≤ V := (Real.rpow_pos_of_pos hN _).le
  have had : 0 ≤ ad := (Real.rpow_pos_of_pos ha _).le
  have hsource := agreement_source_cost_bound (Nat.cast_nonneg n) hK hH hq hg.le hχ hχq hδU
    hA hV had (agreement_time_card_bound hχ hχ₁) hwidth
    (agreement_hidden_window_bound hN hH ha hd hwin)
  have hsourceEq := agreement_source_cost_ennreal (n := n) hK₀ hH₀ hq hg.le hχ hδU hA hV
  have hnear := ENNReal.ofReal_le_ofReal (agreement_near_factor_bound hK hH₀ hχ hρ)
  have hproduct : ENNReal.ofReal (50 * H * cfg.K k) *
      ENNReal.ofReal (600000 * (cfg.K k) ^ 2 * H ^ 3 * CB.frame.q ^ 3 * CB.frame.g * ad) =
      ENNReal.ofReal (30000000 * (cfg.K k) ^ 3 * H ^ 4 * CB.frame.q ^ 3 * CB.frame.g * ad) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 50 * H * cfg.K k)]
    congr 1
    ring
  have href : ENNReal.ofReal (30000000 * (cfg.K k) ^ 3 * H ^ 4 * CB.frame.q ^ 3 * CB.frame.g * ad) ≤
      ENNReal.ofReal (100000000 * (cfg.K k) ^ 4 * H ^ 4) *
        (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) := by
    have heq : 30000000 * (cfg.K k) ^ 3 * H ^ 4 * CB.frame.q ^ 3 * CB.frame.g * ad =
        (30000000 * (cfg.K k) ^ 4 * H ^ 4) *
          (CB.frame.q * (ad * CB.frame.q ^ 2 * CB.frame.g / cfg.K k)) := by
      field_simp
    rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hq.le]
    have hlo : ENNReal.ofReal (ad * CB.frame.q ^ 2 * CB.frame.g / cfg.K k) ≤
        cfg.ν k (cfg.A k s CB.i) := hB.nu_lo CB.i
    gcongr
    norm_num
  have hprodle : ENNReal.ofReal (2 * H * (2 * ρN / χ + 1)) *
      ENNReal.ofReal (agreementSourceCost n (cfg.K k) H CB.frame.q CB.frame.g χ P.δU A V) ≤
      ENNReal.ofReal (30000000 * (cfg.K k) ^ 3 * H ^ 4 * CB.frame.q ^ 3 * CB.frame.g * ad) :=
    (mul_le_mul' hnear (ENNReal.ofReal_le_ofReal hsource)).trans_eq hproduct
  have hfinal := mul_le_mul'
    (le_refl (C₁ * ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
      4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm))) (hprodle.trans href)
  unfold agreeLoss
  rw [hδt, hsourceEq]
  simpa only [mul_assoc] using hfinal

/-- The same bound in the real units of `agreement_final`'s mass-loss conclusion. -/
theorem agreeLoss_toReal_le_original_reference [IsFiniteMeasure (cfg.ν k)]
    (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hd : cfg.d ≤ 1)
    (hχ : 0 < χ) (hχ₁ : χ ≤ 1) (hχq : χ ≤ CB.frame.q)
    (hδt : P.δt = χ) (hδU : 0 < P.δU)
    (hwidth : cfg.K k * χ ≤ CB.frame.q * CB.frame.g * P.δU)
    {r sp vp θm w LipU ρN : ℝ}
    (hρ : ρN ≤ 12 * cfg.K k * χ)
    (hwin : CB.frame.a * (2 * H + 1) * cfg.N k ^ (-u) = cfg.N k ^ (-sp))
    (C₁ : ℝ≥0∞) (hC₁ : C₁ ≠ ⊤)
    (hlen : 0 ≤ θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
      4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) :
    (CB.agreeLoss P C₁ r sp vp θm w LipU ρN).toReal ≤
      C₁.toReal * (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
        4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) *
      (100000000 * (cfg.K k) ^ 4 * H ^ 4) *
      (CB.frame.q * (cfg.ν k (cfg.A k s CB.i)).toReal) := by
  have hbound := CB.agreeLoss_le_original_reference P hB hN hK hd hχ hχ₁ hχq hδt hδU hwidth
    (r := r) (vp := vp) (θm := θm) (w := w) (LipU := LipU) hρ hwin C₁
  have hfinite : C₁ * ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
      4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) *
      ENNReal.ofReal (100000000 * (cfg.K k) ^ 4 * H ^ 4) *
      (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
  have hq : 0 ≤ CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hcoeff : 0 ≤ 100000000 * (cfg.K k) ^ 4 * H ^ 4 := by positivity
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlen,
    ENNReal.toReal_ofReal hcoeff, ENNReal.toReal_ofReal hq] using ENNReal.toReal_mono hfinite hbound

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
