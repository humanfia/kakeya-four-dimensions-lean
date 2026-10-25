-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DensityPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

/-- At one common radius, comparable ball density costs an arbitrarily small
power of mass. The ambient set may be larger than the retained shadings. -/
theorem regular_ball_density_power {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ η R : ℝ, η ≤ 1 → 0 < R → R ≤ 1 →
    ∀ (n : ℕ) (U : Set Space) (Y : Fin n → Set Space),
    MeasurableSet U → U ⊆ ball 0 1 → (∀ i, Y i ⊆ U) →
    ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) →
    ∃ (lam : ℝ) (Z : Set Space), MeasurableSet Z ∧ Z ⊆ U ∧
      δ ^ 4 / 2 ≤ lam ∧ lam ≤ 4 ∧
      (∀ p ∈ Z,
        ENNReal.ofReal (lam * R ^ 3) ≤ volume (U ∩ ball p R) ∧
        volume (U ∩ ball p R) ≤ ENNReal.ofReal (2 * lam * R ^ 3)) ∧
      ENNReal.ofReal (δ ^ ε) * ∑ i, volume (Y i) ≤ ∑ i, volume (Y i ∩ Z) := by
  obtain ⟨d, hd, hlog⟩ := dyadic_size_power_bound (M := 8) (k := 4) (by norm_num) (by norm_num) hε
  refine ⟨min (1 / 8192) d, lt_min (by norm_num) hd, (min_le_left _ _).trans (by norm_num), ?_⟩
  intro δ hδ hδd η R hη hR hR1 n U Y hUm hUball hYU hmass
  have hδsmall : δ ≤ 1 / 8192 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδd' : δ ≤ d := hδd.trans (min_le_right _ _)
  have ht : 0 < δ ^ (4 : ℕ) := by positivity
  have ht8 : δ ^ (4 : ℕ) ≤ 8 := (pow_le_one₀ hδ.le hδ1).trans (by norm_num)
  have hfin : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ne_top_of_le_ne_top (measure_ball_lt_top.ne) (measure_mono ((hYU i).trans hUball))
  have hηpow : δ ≤ δ ^ η := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη
  have hreal : 4096 * (1 : ℕ) * n * δ ^ (4 : ℕ) ≤ (1 / 2 : ℝ) * (δ ^ η * n * δ ^ 2) := by
    have hh : 4096 * δ ^ (4 : ℕ) ≤ (1 / 2 : ℝ) * (δ ^ η * δ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hδsmall (show 0 ≤ δ ^ 3 by positivity),
        mul_le_mul_of_nonneg_right hηpow (sq_nonneg δ)]
    have hn := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n)
    convert hn using 1 <;> push_cast <;> ring
  have hbudget : ENNReal.ofReal (4096 * (1 : ℕ) * n * δ ^ (4 : ℕ)) ≤
      (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (δ ^ η * n * δ ^ 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num [ENNReal.ofReal_div_of_pos]
      _ ≤ _ := mul_le_mul' le_rfl hmass
  obtain ⟨lam, Z, hZm, hZU, hlam, hden, hretain⟩ := regular_ball_density_shading
    (k := 1) (fun _ => R) (fun _ => hR) (fun _ => hR1) ht ht8 U hUm hUball Y hYU hfin hbudget
  refine ⟨lam 0, Z, hZm, hZU, (hlam 0).1, (hlam 0).2, fun p hp => hden p hp 0, ?_⟩
  let K : ℝ := (Scale.dyExp 8 (δ ^ (4 : ℕ)) : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : 2 * K ≤ δ ^ (-ε) := by
    simpa only [K, Real.rpow_ofNat] using hlog δ hδ hδ1 hδd'
  have hretain' : (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤
      ENNReal.ofReal K * ∑ i, volume (Y i ∩ Z) := by
    simpa only [pow_one, K, Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hretain
  have hmul := mul_le_mul' (le_refl (2 : ℝ≥0∞)) hretain'
  have hfull : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (2 * K) * ∑ i, volume (Y i ∩ Z) := by
    simpa only [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hmul
  have hcoeff : δ ^ ε * (2 * K) ≤ 1 := by
    calc
      _ ≤ δ ^ ε * δ ^ (-ε) := mul_le_mul_of_nonneg_left hKr (Real.rpow_nonneg hδ.le _)
      _ = 1 := by rw [← Real.rpow_add hδ]; simp
  calc
    _ ≤ ENNReal.ofReal (δ ^ ε) * (ENNReal.ofReal (2 * K) * ∑ i, volume (Y i ∩ Z)) :=
      mul_le_mul' le_rfl hfull
    _ = ENNReal.ofReal (δ ^ ε * (2 * K)) * ∑ i, volume (Y i ∩ Z) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    _ ≤ 1 * ∑ i, volume (Y i ∩ Z) := mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal hcoeff) le_rfl
    _ = _ := one_mul _

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
