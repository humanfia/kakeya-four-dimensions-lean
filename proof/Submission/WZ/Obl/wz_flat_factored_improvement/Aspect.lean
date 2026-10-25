-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Aspect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.CoverComposition
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatProductScalar

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

set_option maxHeartbeats 1200000 in
/-- The two body estimates give the full aspect-ratio improvement. All choices
of density tolerance and scale are uniform in the prism widths and the family. -/
theorem aspectRatio_of_body {σ u : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hu : 0 < u) (hE : TubeEstimate σ u) (hF : BodyEstimate σ u) : AspectRatioEstimate σ u := by
  intro ε hε
  obtain ⟨Af, ηf, df, hAf, hηf, hdf, _, Hf⟩ := flat_fine_estimate hσ hF (by positivity : 0 < ε / 4)
  obtain ⟨Ac, ηc, dc, hAc, hηc, hdc, _, Hc⟩ := flat_coarse_estimate hσhalf hF (by positivity : 0 < ε / 4)
  obtain ⟨Ae, hAe, ηe, hηe, HE⟩ := hE ε hε
  obtain ⟨dn, hdn, _, Hn⟩ := tube_number_power_bound
  let s := min (ε / 40) (min (ηf / 4) (ηc / 16))
  have hs : 0 < s := by dsimp [s]; positivity
  have hsε : s ≤ ε / 40 := min_le_left _ _
  have hsf : s ≤ ηf / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsc : s ≤ ηc / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hsf' : 2 * s ≤ ηf := by linarith
  have hsc' : 8 * s ≤ ηc := by linarith
  have herr : ε / 2 + 7 * s ≤ ε := by linarith
  obtain ⟨K, hKgt⟩ := exists_nat_gt (4 / s)
  have hK : 0 < K := by
    have hh : (0 : ℝ) < K := lt_trans (by positivity) hKgt
    exact_mod_cast hh
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hsK : 4 ≤ s * K := by
    have hh := (div_lt_iff₀ hs).mp hKgt
    nlinarith
  obtain ⟨dl, hdl, _, Hl⟩ := WangZahlLot.Obl.wz_regular_transverse_affine_cells.dyadic_depth_with_power_budget
    1 s ((10 : ℝ) ^ (15 : ℕ)) (by norm_num) hs (by positivity)
  let η := min 1 (min s ηe)
  have hη : 0 < η := by dsimp [η]; positivity
  let d := min df (min dc (min dn (min dl (min (1 / 3456) ((1 / (224 * K) : ℝ) ^ s⁻¹)))))
  have hd : 0 < d := by dsimp [d]; positivity
  let As := Af * Ac / 432 * (16 : ℝ) ^ (-1 + 3 / 2 * σ)
  let Al := Ae / (200 : ℝ) ^ u
  let A := min As Al
  have hAs : 0 < As := by dsimp [As]; positivity
  have hAl : 0 < Al := by dsimp [Al]; positivity
  have hA : 0 < A := lt_min hAs hAl
  refine ⟨A, hA, η, hη, d, hd, ?_⟩
  intro ν hν hνη δ hδ hδ100 hδd c l hc hl n x v Y hAdm hY a b hδa hab hb2 hCover
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hν1 : ν ≤ 1 := hνη.trans (min_le_left _ _)
  have hνs : ν ≤ s := hνη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνe : ν ≤ ηe := hνη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hc' : 0 < c := zero_lt_one.trans_le hc
  have hl' : 0 < l := zero_lt_one.trans_le hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hAdm.1
  by_cases haSmall : a ≤ 1 / 100
  · have hδf : δ ≤ df := hδd.trans (min_le_left _ _)
    have hδc : δ ≤ dc := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδn : δ ≤ dn := hδd.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hδl : δ ≤ dl := hδd.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hδcut : δ ≤ 1 / 3456 := hδd.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    have hδroot : δ ≤ (1 / (224 * K) : ℝ) ^ s⁻¹ := hδd.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    have hretBudget : 224 * K * δ ^ s ≤ 1 := by
      have hh := (Real.le_rpow_inv_iff_of_pos hδ.le (by positivity : 0 ≤ (1 / (224 * K) : ℝ)) hs).mp hδroot
      have hh' := (le_div_iff₀ (by positivity : (0 : ℝ) < 224 * K)).mp hh
      nlinarith
    have hcut : 432 * (δ ^ s) ^ K * a * b ≤ δ ^ ν * δ ^ 2 / 2 := by
      have hpower : (δ ^ s) ^ K ≤ δ ^ (4 : ℕ) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_ofNat]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hsK
      have hab4 : a * b ≤ 4 := by
        have hh := mul_le_mul (hab.trans hb2) hb2 hb.le (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
      have hδν : δ ≤ δ ^ ν := by
        have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hν1
        simpa only [Real.rpow_one] using hh
      calc
        _ ≤ 1728 * δ ^ (4 : ℕ) := by
          have hh := mul_le_mul hpower hab4 (mul_pos ha hb).le (by positivity : 0 ≤ δ ^ (4 : ℕ))
          nlinarith only [hh]
        _ ≤ δ ^ (3 : ℕ) / 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hδcut (by positivity : 0 ≤ δ ^ (3 : ℕ))]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hδν (sq_nonneg δ)]
    obtain ⟨Kc, hKc, hlog⟩ := Hl δ hδ hδl
    rw [Real.rpow_one] at hKc
    have hLf : 1 ≤ δ ^ (-3 * s) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hD : 1 ≤ δ ^ (-ν) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hFine : ∀ e, FineEstimateAt σ u (ε / 4) Af ηf δ a b (δ ^ (-3 * s)) e :=
      fun e => Hf δ a b (δ ^ (-3 * s)) hδ hδf hδa hab hb2 haSmall hLf e
    have hCoarse : CoarseEstimateAt σ u (ε / 4) Ac ηc δ a b (δ ^ (-ν)) l :=
      Hc δ a b (δ ^ (-ν)) l hδ hδc hδa hab hb2 hD hl
    have hnmax := Hn δ hδ hδn n x v (fun i => (hAdm.2.1 i).1)
      (fun i => (hAdm.2.1 i).2.1) hAdm.2.2.1
    obtain ⟨q, N, hq, hN, hsize, hNvol, hbound⟩ := finite_flat_cover_product hσ hAf hAc hδ hδ1
      hδa hab hb2 haSmall hν hν1 hs hνs hsf' hsc' hc hl hFine hCoarse
      hK hretBudget hcut Kc hKc hlog x v Y hnmax hAdm hY hCover
    have hscalar := flat_product_scalar (u := u) (ε := ε) hσ hσhalf hAf hAc hδ hδ1
      ha hb hc' hl' hn' (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hN) hD
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : -s ≤ -ν)) hsize hNvol herr
    calc
      _ ≤ ENNReal.ofReal ((b / a) ^ u * profile σ u ε As δ c l n) := by
        apply ENNReal.ofReal_le_ofReal
        unfold profile
        have hAA : A ≤ As := min_le_left _ _
        gcongr
      _ ≤ ENNReal.ofReal (flatCellDensity σ u (ε / 4) Af δ a b s N *
          (Ac * δ ^ (ε / 4) * b ^ u * (δ ^ (-ν)) ^ (-2 : ℝ) * l ^ (-σ) *
            (q : ℝ) ^ (1 - σ) * (a * b) ^ (1 - σ / 2))) := by
        exact ENNReal.ofReal_le_ofReal hscalar
      _ ≤ _ := hbound
  · have hInput : Admissible δ ηe c l n x v Y := by
      obtain ⟨hn, hfam, hsep, hmass, hconv, hslab⟩ := hAdm
      refine ⟨hn, hfam, hsep, ?_, hconv, hslab⟩
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
      have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνe
      gcongr
    have hbound := HE δ hδ hδ100 c l hc hl n x v Y hInput
    have hratio : b / a ≤ 200 := by
      rw [div_le_iff₀ ha]
      have hh := lt_of_not_ge haSmall
      linarith
    have h200 : 0 < (200 : ℝ) ^ u := by positivity
    have hcoef : (b / a) ^ u * A ≤ Ae := by
      calc
        _ ≤ (200 : ℝ) ^ u * Al := mul_le_mul
          (Real.rpow_le_rpow (div_pos hb ha).le hratio hu.le) (min_le_right _ _) hA.le h200.le
        _ = _ := by dsimp [Al]; field_simp
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
    calc
      _ = profile σ u ε ((b / a) ^ u * A) δ c l n := by unfold profile; ring
      _ ≤ _ := by unfold profile; gcongr

theorem aspectRatio_of_tube_estimate {σ u : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hu : 0 < u) (hE : TubeEstimate σ u) : AspectRatioEstimate σ u :=
  aspectRatio_of_body hσ.le hσhalf hu hE (body_estimate_of_tube_estimate hσ.le hσhalf hu hE)

end WangZahlLot.Obl.wz_flat_factored_improvement
