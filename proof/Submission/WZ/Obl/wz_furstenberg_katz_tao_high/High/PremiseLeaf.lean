-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.PremiseLeaf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyProfile

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The strong energy premise at every pair of palette scales. Its
constants are chosen before the palette size and the fine scale. -/
theorem premiseLeaf {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : PremiseLeaf s := by
  intro e he
  let ζ := e / 10
  let ν := ζ / 10
  let ℓ := min 1 (ζ / 100)
  let ε' := min 1 (min (ζ / 100) (ℓ * (1 - s) / 2))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hℓ1 : ℓ ≤ 1 := min_le_left _ _
  have hℓζ : ℓ ≤ ζ / 100 := min_le_right _ _
  have hε' : 0 < ε' := by
    dsimp only [ε']
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'ζ : ε' ≤ ζ / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hε'κ : ε' ≤ ℓ * (1 - s) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (8 / ζ) 1)
  refine ⟨ε', hε', N₀, ?_⟩
  intro n hn₀
  have hnR : (N₀ : ℝ) ≤ n := by exact_mod_cast hn₀
  have hn1 : (1 : ℝ) < n := (lt_of_le_of_lt (le_max_right _ _) hN₀).trans_le hnR
  have hn : 0 < n := by exact_mod_cast (lt_trans zero_lt_one hn1)
  have hsize : 8 / ζ ≤ (n : ℝ) :=
    (le_max_left _ _).trans (hN₀.le.trans hnR)
  have hgap : 2 ≤ ζ * n / 4 := by
    have hh := (div_le_iff₀ hζ).mp hsize
    nlinarith
  let C : ℝ := 10000000000000000 * ((n : ℝ) + 1)
  have hCbig : (10000000000000000 : ℝ) ≤ C := by
    dsimp [C]
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨rE, hrE, hrE4, hsecond⟩ := highConfig_tube_second_moment ν hν
  obtain ⟨rB, hrB, _, hbase⟩ := exists_palBase_cutoff (by norm_num : (1 : ℝ) < 128) hn
  obtain ⟨rC, hrC, _, hconstant⟩ :=
    WangZahlLot.Obl.wz_nonconcentrated_dot_products.exists_power_bound C
      (show 0 < ζ / 4 by positivity)
  obtain ⟨rF, hrF, hfarcut⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (show 0 < ℓ * (1 - s) / 2 by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨min rE (min rB (min rC rF)), by positivity, ?_⟩
  intro r ε₀ ε κ P D S J₀ cls J₁ tb hr hsmall hε₀ hε₀small hε hεsmall hκ hκsmall H p₀ hp₀ h a hh hha han
  have hrE' : r ≤ rE := hsmall.trans (min_le_left _ _)
  have hrB' : r ≤ rB := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC' : r ≤ rC := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrF' : r ≤ rF := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr4 : r ≤ 1 / 4 := hrE'.trans hrE4
  have hr1 : r < 1 := by linarith only [hr4]
  have hb128 : 128 ≤ palBase r n := hbase r hr hrB'
  have hB : 1 < palBase r n := palBase_gt_one hr hr1 hn
  have hB0 : 0 < palBase r n := palBase_pos hr
  have hB2 : 1 ≤ (palBase r n) ^ (2 : ℕ) := one_le_pow₀ hB.le
  have hCpow : C ≤ palBase r n ^ (ζ * n / 4) := by
    have hc := hconstant r hr hrC'
    rw [rpow_eq_palBase hr hn] at hc
    convert hc using 1 <;> congr 1 <;> ring
  have hBpow : (palBase r n) ^ (2 : ℕ) ≤ palBase r n ^ (ζ * n / 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hB.le (by exact_mod_cast hgap)
  have hbudget : C * (palBase r n) ^ (2 : ℕ) * r ^ (-(ζ / 2)) ≤
      palBase r n ^ (ζ * n) := by
    calc
      _ ≤ (palBase r n ^ (ζ * n / 4)) * (palBase r n ^ (ζ * n / 4)) * r ^ (-(ζ / 2)) := by
        gcongr
      _ = palBase r n ^ (ζ * n) := by
        rw [rpow_eq_palBase hr hn, ← Real.rpow_add hB0, ← Real.rpow_add hB0]
        congr 1
        ring
  have hcoef (c k : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) (hk : k ≤ ζ / 2) :
      c * (palBase r n) ^ (2 : ℕ) * r ^ (-k) ≤ palBase r n ^ (ζ * n) := by
    apply le_trans _ hbudget
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hcC (sq_nonneg _)
    · exact Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith)
    · exact Real.rpow_nonneg hr.le _
    · exact mul_nonneg hC0 (sq_nonneg _)
  have hplain (c k : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) (hk : k ≤ ζ / 2) :
      c * r ^ (-k) ≤ palBase r n ^ (ζ * n) := by
    apply le_trans _ (hcoef c k hc hcC hk)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    calc c = c * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hB2 hc
  have hεζ : ε ≤ ζ / 100 := hεsmall.trans hε'ζ
  have hε₀ζ : ε₀ ≤ ζ / 100 := hε₀small.trans hε'ζ
  have hκℓ : κ ≤ ℓ * (1 - s) / 2 := hκsmall.trans hε'κ
  have hℓs : ℓ * s ≤ ζ / 100 :=
    (mul_le_mul_of_nonneg_left hs1.le hℓ.le).trans (by simpa using hℓζ)
  have hfar : r ^ (-κ + ℓ * (1 - s)) ≤ 1 / 2 := by
    apply le_trans _ (hfarcut r hr hrF')
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith)
  have hRsmall : palScale r n a ≤ 1 / 8 := by
    have hscale := palScale_le_inv_base hr hr1 hn (hh.trans_le hha)
    have hinv : (palBase r n)⁻¹ ≤ (128 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hb128
    linarith [hscale.trans hinv]
  have hEp := hsecond r s ε₀ ε κ n P D S J₀ cls J₁ tb hrE'
    (hεsmall.trans hε'1) hb128 H h a hh hha han
  have hWcoef : 8586240 * r ^ (-4 * ε) ≤ palBase r n ^ (ζ * n) := by
    convert hplain 8586240 (4 * ε) (by norm_num) (by linarith only [hCbig]) (by linarith only [hεζ, hζ]) using 1 <;> congr 1 <;> ring
  have hEcoef : 3 * r ^ (-(4 * ε + ν)) ≤ palBase r n ^ (ζ * n) :=
    hplain 3 (4 * ε + ν) (by norm_num) (by linarith only [hCbig]) (by dsimp [ν]; linarith only [hεζ, hζ])
  have hJcoef : (67080 : ℝ) ^ (2 : ℕ) * 5200 * r ^ (-(12 * ε + ε₀ + ℓ * s)) ≤
      palBase r n ^ (ζ * n) :=
    hplain (67080 ^ (2 : ℕ) * 5200) (12 * ε + ε₀ + ℓ * s)
      (by positivity) (by norm_num; linarith only [hCbig]) (by linarith only [hεζ, hε₀ζ, hℓs, hζ])
  have hIcoef : 72 * r ^ (-2 * ε) ≤ palBase r n ^ (ζ * n) := by
    convert hplain 72 (2 * ε) (by norm_num) (by linarith only [hCbig]) (by linarith only [hεζ, hζ]) using 1 <;> congr 1 <;> ring
  have hUcoef : 4829760000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-4 * ε) ≤
      palBase r n ^ (ζ * n) := by
    convert hcoef 4829760000000 (4 * ε) (by norm_num) (by linarith only [hCbig]) (by linarith only [hεζ, hζ]) using 1 <;> congr 1 <;> ring
  have hcard : ((Finset.Icc h a).card : ℝ) ≤ (n : ℝ) + 1 := by
    have hh : (Finset.Icc h a).card ≤ n + 1 := by rw [Nat.card_Icc]; omega
    exact_mod_cast hh
  have hnC : (n : ℝ) + 1 ≤ C := by dsimp [C]; nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  have hpalette : ((Finset.Icc h a).card : ℝ) ≤ palBase r n ^ (ζ * n) := by
    have hb := hplain ((n : ℝ) + 1) 0 (by positivity) hnC (by positivity)
    simp only [neg_zero, Real.rpow_zero, mul_one] at hb
    exact hcard.trans hb
  have h8 : 8 ≤ palBase r n ^ (ζ * n) := by
    have hb := hplain 8 0 (by norm_num) (by linarith only [hCbig]) (by positivity)
    simpa only [neg_zero, Real.rpow_zero, mul_one] using hb
  obtain ⟨y, hhy, hya, hvalue⟩ := H.energy_witness_of_coefficients hr1 hn hs0 hs1.le hε.le
    hha han hRsmall hℓ1 hfar (by positivity : 0 ≤ ζ * n) hp₀ hEp
    hWcoef hEcoef hJcoef hIcoef hUcoef hpalette h8
  refine ⟨y, hhy, hya, ?_⟩
  calc
    _ ≤ bushProfile r n S p₀ a + ptProfile r n S h - bushProfile r n S p₀ h + 10 * (ζ * n) := hvalue
    _ = _ := by dsimp [ζ]; ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
