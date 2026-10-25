-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseANumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/CaseANumerics.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowJCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TopLevel

/-!
# Numerics of case A at a window

* `palBase_rpow_eq`: `palBase r n ^ x = r ^ (-(x / n))`.
* `arcAvg_bounds`: with near-uniform bushes `|F t - s t| ≤ d n`, the average number of normals of
  the reference pin per occupied `palScale j`-arc is `(palScale j / r)^s` up to `r^(±(ε + d))`
  (and a factor `2^s` above).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem palBase_rpow_eq {r : ℝ} (hr : 0 < r) (n : ℕ) (x : ℝ) :
    palBase r n ^ x = r ^ (-(1 / (n : ℝ)) * x) := by
  unfold palBase
  rw [← Real.rpow_mul hr.le]

theorem palScale_eq_rpow {r : ℝ} (hr : 0 < r) (n i : ℕ) :
    palScale r n i = r ^ ((i : ℝ) / n) := by
  unfold palScale
  rw [palBase_rpow_eq hr]
  congr 1
  ring

/-- **The arc averages of the reference pin.** -/
theorem arcAvg_bounds {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) (hr1 : r < 1) (hn : 0 < n)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {d : ℝ}
    (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) {j : ℕ} (hj : j ≤ n) :
    (palScale r n j / r) ^ s * r ^ (ε + d) ≤ arcAvg (palScale r n j) S p₀ ∧
      arcAvg (palScale r n j) S p₀ ≤ 2 ^ s * (palScale r n j / r) ^ s * r ^ (-(ε + d)) := by
  have hr : 0 < r := hC.fail.r_pos
  have hne := bushOf_nonempty hC.failS hp₀
  have hB := palBase_gt_one hr hr1 hn
  have hBpos : 0 < palBase r n := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the number of arcs is `B ^ F j`
  have hcount : (((bushOf S p₀).image (arcOf (palScale r n j))).card : ℝ) =
      palBase r n ^ (bushProfile r n S p₀ j) := by
    rw [image_arcOf_eq_cellOf]
    unfold bushProfile cellProfile
    rw [Real.rpow_logb hBpos (by linarith : palBase r n ≠ 1)
      (by exact_mod_cast cellCount_pos hne _)]
    rfl
  have hF := abs_le.mp (hunif j hj)
  set ρj := palScale r n j with hρj
  have hρj0 : 0 < ρj := by rw [hρj, palScale_eq_rpow hr]; positivity
  have hρjr : ρj = r ^ ((j : ℝ) / n) := palScale_eq_rpow hr n j
  -- `B ^ (s j ± d n) = ρj ^ (-s) r ^ (∓ d)`
  have hpow : ∀ u : ℝ, palBase r n ^ (s * j + u * n) = ρj ^ (-s) * r ^ (-u) := by
    intro u
    rw [palBase_rpow_eq hr, hρjr, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    field_simp
    ring
  have hup : palBase r n ^ (bushProfile r n S p₀ j) ≤ ρj ^ (-s) * r ^ (-d) := by
    rw [← hpow d]
    exact Real.rpow_le_rpow_of_exponent_le hB.le (by linarith [hF.2])
  have hlo : ρj ^ (-s) * r ^ (-(-d)) ≤ palBase r n ^ (bushProfile r n S p₀ j) := by
    rw [← hpow (-d)]
    exact Real.rpow_le_rpow_of_exponent_le hB.le (by nlinarith [hF.1])
  rw [neg_neg] at hlo
  -- the size of the bush
  have hbush_lo : r ^ (ε - s) ≤ ((bushOf S p₀).card : ℝ) := hC.failS.D_card p₀ hp₀
  obtain ⟨e₀, he₀⟩ := hne
  have he₀1 : ‖e₀‖ = 1 := by
    have := (hC.failS.D_mem (p₀, e₀) (mem_bushOf.mp he₀)).2
    exact this
  have hbush_hi : ((bushOf S p₀).card : ℝ) ≤ r ^ (-ε) * (2 / r) ^ s := by
    have h := hC.failS.D_kt p₀ hp₀ e₀ he₀1 2 (by linarith)
    have hall : (bushOf S p₀).filter (fun e => dist e e₀ ≤ 2) = bushOf S p₀ := by
      apply Finset.filter_true_of_mem
      intro e he
      have he1 : ‖e‖ = 1 := (hC.failS.D_mem (p₀, e) (mem_bushOf.mp he)).2
      calc dist e e₀ ≤ ‖e‖ + ‖e₀‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ = 2 := by rw [he1, he₀1]; norm_num
    rw [hall] at h
    exact h
  have hcount0 : 0 < palBase r n ^ (bushProfile r n S p₀ j) := Real.rpow_pos_of_pos hBpos _
  have hρs : (ρj / r) ^ s = ρj ^ s * r ^ (-s) := by
    rw [Real.div_rpow hρj0.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  have hρneg : ρj ^ (-s) = (ρj ^ s)⁻¹ := Real.rpow_neg hρj0.le s
  unfold arcAvg
  rw [hcount]
  constructor
  · -- lower bound
    rw [le_div_iff₀ hcount0]
    calc (ρj / r) ^ s * r ^ (ε + d) * palBase r n ^ (bushProfile r n S p₀ j)
        ≤ (ρj / r) ^ s * r ^ (ε + d) * (ρj ^ (-s) * r ^ (-d)) := by
          apply mul_le_mul_of_nonneg_left hup; positivity
      _ = r ^ (ε - s) := by
          rw [hρs, hρneg]
          have h1 : ρj ^ s ≠ 0 := (Real.rpow_pos_of_pos hρj0 s).ne'
          field_simp
          repeat rw [← Real.rpow_add hr]
          congr 1; ring
      _ ≤ _ := hbush_lo
  · -- upper bound
    rw [div_le_iff₀ hcount0]
    calc ((bushOf S p₀).card : ℝ) ≤ r ^ (-ε) * (2 / r) ^ s := hbush_hi
      _ = 2 ^ s * (ρj / r) ^ s * r ^ (-(ε + d)) * (ρj ^ (-s) * r ^ d) := by
          rw [hρs, hρneg, Real.div_rpow (by norm_num) hr.le]
          have h1 : ρj ^ s ≠ 0 := (Real.rpow_pos_of_pos hρj0 s).ne'
          have h2 : r ^ s ≠ 0 := (Real.rpow_pos_of_pos hr s).ne'
          field_simp
          rw [Real.rpow_neg hr.le s]
          field_simp
          repeat rw [← Real.rpow_add hr]
          congr 1; ring
      _ ≤ 2 ^ s * (ρj / r) ^ s * r ^ (-(ε + d)) * palBase r n ^ (bushProfile r n S p₀ j) := by
          apply mul_le_mul_of_nonneg_left hlo; positivity

/-- **Algebra of the quadratic bound.** From `Jc (a/Kc)² (Rm/t)² ≤ Z` with `t = 98 K H` and
`a ≥ u v`: `64 Jc ≤ K₀ M²` for `M = H / (Kc q u)` and `K₀ = 64 Z Kc⁴ (98 K)² q² / (v² Rm²)`. -/
theorem quad_algebra {Jc Z a H Kc K Rm u v q : ℝ} (hZ : 0 ≤ Z) (hKc : 0 < Kc) (hK : 0 < K)
    (hH : 0 < H) (hRm : 0 < Rm) (hu : 0 < u) (hv : 0 < v) (hq : 0 < q)
    (hcount : Jc * ((a / Kc) ^ 2 * (Rm / (2 * (49 * (K * H)))) ^ 2) ≤ Z) (ha : u * v ≤ a) :
    64 * Jc ≤ (64 * Z * Kc ^ 4 * (2 * (49 * K)) ^ 2 * q ^ 2 / (v ^ 2 * Rm ^ 2)) *
      (H / (Kc * (q * u))) ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hu hv) ha
  set t := 2 * (49 * (K * H)) with ht
  have ht0 : 0 < t := by positivity
  have h1 : Jc * (a ^ 2 * Rm ^ 2) ≤ Z * (Kc ^ 2 * t ^ 2) := by
    have e : (a / Kc) ^ 2 * (Rm / t) ^ 2 = a ^ 2 * Rm ^ 2 / (Kc ^ 2 * t ^ 2) := by
      field_simp
    rw [e, mul_div_assoc', div_le_iff₀ (by positivity)] at hcount
    exact hcount
  have h2 : (u * v) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
  have hR : (64 * Z * Kc ^ 4 * (2 * (49 * K)) ^ 2 * q ^ 2 / (v ^ 2 * Rm ^ 2)) *
      (H / (Kc * (q * u))) ^ 2 = 64 * (Z * (Kc ^ 2 * t ^ 2)) / ((u * v) ^ 2 * Rm ^ 2) := by
    rw [ht]; field_simp
  rw [hR, le_div_iff₀ (by positivity)]
  rcases le_or_gt Jc 0 with hJ | hJ
  · have : 64 * Jc * ((u * v) ^ 2 * Rm ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have : 0 ≤ 64 * (Z * (Kc ^ 2 * t ^ 2)) := by positivity
    linarith
  · have h3 : Jc * ((u * v) ^ 2 * Rm ^ 2) ≤ Jc * (a ^ 2 * Rm ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) hJ.le
    nlinarith

/-- **Algebra of the code bound.** In the setting of `quad_algebra`, with `H / u ≤ Hu`:
`8 Jc / M ≤ 8 Z Kc³ (98 K)² q Hu / (v² Rm²)`. -/
theorem code_algebra {Jc Z a H Kc K Rm u v q Hu : ℝ} (hZ : 0 ≤ Z) (hKc : 0 < Kc) (hK : 0 < K)
    (hH : 0 < H) (hRm : 0 < Rm) (hu : 0 < u) (hv : 0 < v) (hq : 0 < q)
    (hcount : Jc * ((a / Kc) ^ 2 * (Rm / (2 * (49 * (K * H)))) ^ 2) ≤ Z) (ha : u * v ≤ a)
    (hHu : H / u ≤ Hu) :
    8 * Jc / (H / (Kc * (q * u))) ≤
      8 * Z * Kc ^ 3 * (2 * (49 * K)) ^ 2 * q * Hu / (v ^ 2 * Rm ^ 2) := by
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hu hv) ha
  set t := 2 * (49 * (K * H)) with ht
  have ht0 : 0 < t := by positivity
  have h1 : Jc * (a ^ 2 * Rm ^ 2) ≤ Z * (Kc ^ 2 * t ^ 2) := by
    have e : (a / Kc) ^ 2 * (Rm / t) ^ 2 = a ^ 2 * Rm ^ 2 / (Kc ^ 2 * t ^ 2) := by
      field_simp
    rw [e, mul_div_assoc', div_le_iff₀ (by positivity)] at hcount
    exact hcount
  have h2 : (u * v) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
  have hJ' : Jc * ((u * v) ^ 2 * Rm ^ 2) ≤ Z * (Kc ^ 2 * t ^ 2) := by
    rcases le_or_gt Jc 0 with hJ | hJ
    · have : Jc * ((u * v) ^ 2 * Rm ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hJ (by positivity)
      have : 0 ≤ Z * (Kc ^ 2 * t ^ 2) := by positivity
      linarith
    · have h3 : Jc * ((u * v) ^ 2 * Rm ^ 2) ≤ Jc * (a ^ 2 * Rm ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) hJ.le
      linarith
  have hHu0 : H / u ≤ Hu := hHu
  have hL : 8 * Jc / (H / (Kc * (q * u))) = 8 * Jc * (Kc * q * u) / H := by
    field_simp
  rw [hL, div_le_div_iff₀ hH (by positivity)]
  -- `Jc ≤ Z Kc² t² / ((u v)² Rm²)` and `H ≤ Hu u`
  have hHle : H ≤ Hu * u := by rwa [div_le_iff₀ hu] at hHu0
  have hJle : Jc ≤ Z * (Kc ^ 2 * t ^ 2) / ((u * v) ^ 2 * Rm ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hJ'
  rw [ht] at hJle
  have hfin : 8 * Jc * (Kc * q * u) * (v ^ 2 * Rm ^ 2) ≤
      8 * (Z * (Kc ^ 2 * (2 * (49 * (K * H))) ^ 2) / ((u * v) ^ 2 * Rm ^ 2)) * (Kc * q * u) *
        (v ^ 2 * Rm ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hsimp : 8 * (Z * (Kc ^ 2 * (2 * (49 * (K * H))) ^ 2) / ((u * v) ^ 2 * Rm ^ 2)) *
      (Kc * q * u) * (v ^ 2 * Rm ^ 2) = 8 * Z * Kc ^ 3 * (2 * (49 * K)) ^ 2 * q * H * (H / u) := by
    field_simp
  rw [hsimp] at hfin
  have hHu' : H * (H / u) ≤ H * Hu := mul_le_mul_of_nonneg_left hHu0 hH.le
  nlinarith [mul_le_mul_of_nonneg_left hHu' (by positivity : (0:ℝ) ≤ 8 * Z * Kc ^ 3 * (2 * (49 * K)) ^ 2 * q)]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
