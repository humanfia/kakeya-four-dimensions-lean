-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WindowLoss.lean (bf60247).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowDecay
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

/-- A fixed constant and a sufficiently small fine-scale loss fit inside
any prescribed loss at a scale bounded above by a fixed positive power. -/
theorem small_loss_transfer {c ζ A D : ℝ} (hc : 0 < c) (hζ : 0 < ζ)
    (hA : 0 ≤ A) (hD : 0 < D) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r δ x : ℝ,
      0 < r → r ≤ r₀ → 0 < δ → δ ≤ D * r ^ c → x ≤ c * ζ / 2 →
        A * r ^ (-x) ≤ δ ^ (-ζ) := by
  have hDZ : 0 < D ^ (-ζ) := Real.rpow_pos_of_pos hD _
  obtain ⟨r₁, hr₁, hsmall⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := c * ζ / 2) (B := D ^ (-ζ) / (A + 1)) (by positivity) (by positivity)
  refine ⟨min r₁ 1, lt_min hr₁ zero_lt_one, min_le_right _ _, ?_⟩
  intro r δ x hr hrr hδ hδr hx
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  have hsm := hsmall r hr (hrr.trans (min_le_left _ _))
  have hcoeff : A * r ^ (c * ζ / 2) ≤ D ^ (-ζ) := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < A + 1)).mp hsm
    have hp := Real.rpow_nonneg hr.le (c * ζ / 2)
    nlinarith
  have hbase : A * r ^ (-x) ≤ D ^ (-ζ) * r ^ (-c * ζ) := by
    calc
      A * r ^ (-x) ≤ A * r ^ (-(c * ζ / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hA
      _ = (A * r ^ (c * ζ / 2)) * r ^ (-c * ζ) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 1
        ring
      _ ≤ D ^ (-ζ) * r ^ (-c * ζ) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hr.le _)
  have heq : D ^ (-ζ) * r ^ (-c * ζ) = (D * r ^ c) ^ (-ζ) := by
    rw [Real.mul_rpow hD.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [heq] at hbase
  exact hbase.trans (Real.rpow_le_rpow_of_nonpos hδ hδr (by linarith))

/-- Rewrite the coefficient from `palette_square_decay` as one fine-scale
power. The discretization cost is exactly `2s/n`. -/
theorem palette_coefficient_le_power {r s d u K C L : ℝ} {n : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hn : 0 < n) (hs : 0 ≤ s) (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 0 ≤ L) (hKC : K ≤ C * r ^ (-u)) :
    L ^ (2 * s) + K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s) ≤
      (1 + C) * L ^ (2 * s) * r ^ (-(u + 4 * d + 2 * s / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 ≤ palBase r n := (palBase_pos hr).le
  have hid : (palBase r n * L) ^ (2 * s) = r ^ (-(2 * s / n)) * L ^ (2 * s) := by
    rw [Real.mul_rpow hB hL]
    unfold palBase
    rw [← Real.rpow_mul hr.le]
    congr 2
    ring
  have hexp : 0 ≤ u + 4 * d + 2 * s / n := by positivity
  have hpow : 1 ≤ r ^ (-(u + 4 * d + 2 * s / n)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_nonpos.mpr hexp)
  calc
    _ ≤ L ^ (2 * s) * r ^ (-(u + 4 * d + 2 * s / n)) +
        (C * r ^ (-u)) * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s) := by
      gcongr
      exact le_mul_of_one_le_right (Real.rpow_nonneg hL _) hpow
    _ = _ := by
      rw [hid]
      have hp : r ^ (-u) * r ^ (-4 * d) * r ^ (-(2 * s / n)) =
          r ^ (-(u + 4 * d + 2 * s / n)) := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]
        congr 1
        ring
      calc _ = L ^ (2 * s) * r ^ (-(u + 4 * d + 2 * s / n)) +
          C * L ^ (2 * s) * (r ^ (-u) * r ^ (-4 * d) * r ^ (-(2 * s / n))) := by ring
        _ = _ := by rw [hp]; ring

/-- Quantified form of the palette-to-Frostman conversion: the profile and
count errors are chosen before the palette length and the fine scale. -/
theorem palette_square_frostman {s q c ζ C L D : ℝ}
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hqs : q ≤ 2 * s) (hc : 0 < c) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hD : 0 < D) :
    ∃ ε : ℝ, ∃ n₀ : ℕ, ∃ r₀ : ℝ, 0 < ε ∧ 0 < n₀ ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ n h a : ℕ, n₀ ≤ n → h ≤ a → ∀ r δ d u K N : ℝ,
        0 < r → r < 1 → r ≤ r₀ → 0 < δ → δ ≤ D * r ^ c →
        0 ≤ d → d ≤ ε → 0 ≤ u → u ≤ ε → 0 ≤ K → K ≤ C * r ^ (-u) → 0 ≤ N →
        palScale r n a ≤ L * palScale r n h * δ →
        ∀ (F : ℕ → ℝ) (A : ℝ → ℝ),
          (∀ i, h ≤ i → i ≤ a → |F i - s * i| ≤ d * n) →
          (∀ ρ, δ ≤ ρ → A ρ ≤ N) →
          (∀ ρ, δ ≤ ρ → ρ ≤ 1 / L → ∀ i, h ≤ i → i ≤ a →
            L * palScale r n h * ρ ≤ palScale r n i →
            A ρ ≤ K * (palBase r n ^ (F h - F i)) ^ (2 : ℕ) * N) →
          ∀ ρ, δ ≤ ρ → A ρ ≤ δ ^ (-ζ) * ρ ^ q * N := by
  have hCZ : 0 < c * ζ := mul_pos hc hζ
  let ε := c * ζ / 32
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (16 * s / (c * ζ) + 1)
  have hn₀pos : 0 < n₀ := by
    have hh : 0 ≤ 16 * s / (c * ζ) := by positivity
    have hh' : (0 : ℝ) < n₀ := by linarith
    exact_mod_cast hh'
  obtain ⟨r₀, hr₀, hr₀1, htransfer⟩ := small_loss_transfer hc hζ
    (A := (1 + C) * L ^ (2 * s)) (D := D) (by positivity) hD
  refine ⟨ε, n₀, r₀, hε, hn₀pos, hr₀, hr₀1, ?_⟩
  intro n h a hn hha r δ d u K N hr hr1 hrr hδ hδr hd hdε hu huε hK hKC hN hsmall F A hF hcount hpal
  have hnpos : 0 < n := hn₀pos.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlen : 2 * s / n ≤ c * ζ / 8 := by
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : 16 * s / (c * ζ) ≤ (n : ℝ) := by linarith
    have hh := (div_le_iff₀ hCZ).mp hlt
    rw [div_le_iff₀ hnR]
    nlinarith
  have hbudget : u + 4 * d + 2 * s / n ≤ c * ζ / 2 := by
    dsimp [ε] at hdε huε
    linarith
  have hcoeff := palette_coefficient_le_power hr hr1.le hnpos hs hd hu hK hC
    (by linarith : 0 ≤ L) hKC
  have hfit := htransfer r δ (u + 4 * d + 2 * s / n) hr hrr hδ hδr hbudget
  have hdecay := palette_square_decay hr hr1 hnpos hha hK hL hN hq hqs hδ hsmall hF hcount hpal
  intro ρ hρ
  have hρ0 := hδ.trans_le hρ
  calc
    A ρ ≤ (L ^ (2 * s) + K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s)) * ρ ^ q * N :=
      hdecay ρ hρ
    _ ≤ δ ^ (-ζ) * ρ ^ q * N := by
      apply mul_le_mul_of_nonneg_right _ hN
      exact mul_le_mul_of_nonneg_right (hcoeff.trans hfit) (Real.rpow_nonneg hρ0.le _)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
