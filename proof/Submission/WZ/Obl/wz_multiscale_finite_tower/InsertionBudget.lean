-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.InsertionBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexedInsertion
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyPreparation

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

structure InsertionBudget (d ζ C c g g' gap' : ℝ) (B q : ℕ) : Prop where
  small : d ≤ 1 / 100000
  coefficient : (10 ^ 15 : ℝ) * d ^ ζ ≤ 1
  regularize : (q : ℝ) ^ (B + 2) * d ^ ζ ≤ 1
  balance : 56 * (q : ℝ) * d ^ ζ ≤ 1
  tube_count : 56 * d ≤ 1
  span_constant : C ^ 2 * d ≤ 1
  mesh : 1024 * C * d ^ g' ≤ d ^ ((1 - c) * g)
  upper : 65536 * C * d ^ (c * g') ≤ d ^ gap'
  card_power : d ^ (-4 : ℝ) < (d ^ (-ζ)) ^ q

theorem exists_insertion_budget (B : ℕ) {ζ C c g g' gap' D : ℝ}
    (hζ : 0 < ζ) (hC : 1 ≤ C) (hmesh : (1 - c) * g < g')
    (hgap : gap' < c * g') (hD : 0 < D) :
    ∃ q : ℕ, 0 < q ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ → InsertionBudget d ζ C c g g' gap' B q := by
  obtain ⟨q, hq'⟩ := exists_nat_gt (5 / ζ)
  have hq : 0 < q := by
    have hh : (0 : ℝ) < q := (by positivity : (0 : ℝ) < 5 / ζ).trans hq'
    exact_mod_cast hh
  have hqζ : 5 < ζ * q := by
    have hh := (div_lt_iff₀ hζ).mp hq'
    nlinarith
  let a : ℝ := min ζ (min (g' - (1 - c) * g) (min (c * g' - gap') 1))
  have ha : 0 < a := lt_min hζ (lt_min (sub_pos.mpr hmesh) (lt_min (sub_pos.mpr hgap) zero_lt_one))
  have haζ : a ≤ ζ := min_le_left _ _
  have hamesh : a ≤ g' - (1 - c) * g := (min_le_right _ _).trans (min_le_left _ _)
  have hagap : a ≤ c * g' - gap' :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let W : ℝ := max (10 ^ 15) (max ((q : ℝ) ^ (B + 2)) (max (56 * q) (max (C ^ 2) (65536 * C))))
  have hW : 0 < W := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hWcoef : (10 ^ 15 : ℝ) ≤ W := le_max_left _ _
  have hWreg : (q : ℝ) ^ (B + 2) ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have hWbal : 56 * (q : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hWspan : C ^ 2 ≤ W := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hWupper : 65536 * C ≤ W := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨d₀, hd₀, hd₀D, hcut⟩ := exists_scale_cutoff (1 / W) a (min D (1 / 100000))
    (by positivity) ha (lt_min hD (by norm_num))
  refine ⟨q, hq, d₀, hd₀, hd₀D.trans (min_le_left _ _), ?_⟩
  intro d hd hdd
  have hdsmall : d ≤ 1 / 100000 := hdd.trans (hd₀D.trans (min_le_right _ _))
  have hd1 : d < 1 := by linarith
  have hbase : W * d ^ a ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hcut d hd hdd) hW.le
    simpa only [one_div, mul_inv_cancel₀ hW.ne'] using hh
  have hb {K b : ℝ} (hK : 0 ≤ K) (hKW : K ≤ W) (hab : a ≤ b) : K * d ^ b ≤ 1 :=
    power_coefficient_bound hd hd1.le hK hKW hab hbase
  refine ⟨hdsmall, hb (by norm_num) hWcoef haζ, hb (by positivity) hWreg haζ,
    hb (by positivity) hWbal haζ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_one] using hb (by norm_num) ((by norm_num : (56 : ℝ) ≤ 10 ^ 15).trans hWcoef) ha1
  · simpa only [Real.rpow_one] using hb (sq_nonneg C) hWspan ha1
  · have hh := density_power_bound hd (by positivity : 0 < 1024 * C)
      (hb (by positivity) ((by nlinarith : 1024 * C ≤ 65536 * C).trans hWupper) hamesh)
    exact (mul_comm (1024 * C) (d ^ g') ▸ (le_div_iff₀ (by positivity : 0 < 1024 * C)).mp hh)
  · have hh := density_power_bound hd (by positivity : 0 < 65536 * C)
      (hb (by positivity) hWupper hagap)
    exact (mul_comm (65536 * C) (d ^ (c * g')) ▸ (le_div_iff₀ (by positivity : 0 < 65536 * C)).mp hh)
  · rw [← Real.rpow_mul_natCast hd.le]
    exact Real.rpow_lt_rpow_of_exponent_gt hd hd1 (by nlinarith)

lemma InsertionBudget.length {d ζ C c g g' gap' : ℝ} {B q J : ℕ}
    (H : InsertionBudget d ζ C c g g' gap' B q) (hd : 0 ≤ d) (hq : 0 < q) (hJ : J ≤ B) :
    (q : ℝ) ^ (J + 2) * d ^ ζ ≤ 1 :=
  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hq) (by omega))
    (Real.rpow_nonneg hd _)).trans H.regularize

lemma InsertionBudget.span {d ζ C c g g' gap' : ℝ} {B q : ℕ}
    (H : InsertionBudget d ζ C c g g' gap' B q) (hd : 0 < d) :
    d ^ (-2 : ℝ) < (d ^ (-ζ)) ^ q :=
  (Real.rpow_le_rpow_of_exponent_ge hd (by linarith [H.small] : d ≤ 1) (by norm_num : (-4 : ℝ) ≤ -2)).trans_lt H.card_power

lemma InsertionBudget.card {d θ ζ C c g g' gap' gap : ℝ} {B q J : ℕ}
    (H : InsertionBudget d ζ C c g g' gap' B q) (hd : 0 < d) (hθ : θ ≤ 1)
    (T : HierarchyCertificate d θ g gap J) :
    ((T.tree.layer J).card : ℝ) < (d ^ (-ζ)) ^ q :=
  (T.family.polynomial_card_bound hd (by linarith [H.small]) hθ H.tube_count).trans_lt H.card_power

end WangZahlLot.Obl.wz_multiscale_finite_tower
