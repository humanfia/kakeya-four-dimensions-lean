-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowLinePower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WindowLinePower.lean (bf60247).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowLineFrostman
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowNumerics
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowLoss

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- The fixed geometric coefficient in the window estimate. -/
noncomputable def windowGeomConst : ℝ :=
  5200 * nearTubeConst ^ 3 * arcTubeConst ^ (2 : ℕ) * 98 ^ (2 : ℕ)

/-- The fixed coefficient after conversion of palette scales to radii. -/
noncomputable def windowPowerConst (s : ℝ) : ℝ :=
  (1 + windowGeomConst) * (320 : ℝ) ^ (2 * s)

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- The explicit window coefficient for an actual regularized configuration. -/
theorem HighConfig.winConst_le_power
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {ℓ ν w : ℝ} {KY : ℕ} (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hw : 0 < w) (hw26 : 26 * w ≤ 1)
    (hpin : pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY ≤
      r ^ (-2 * ε - ν)) :
    winConst r s ε (r ^ (-ε)) (r ^ ℓ) w
      (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card ≤
        windowGeomConst * r ^ (-(20 * ε + ε₀ + ℓ * s + ν)) := by
  classical
  have hr := hC.fail.r_pos
  have hCY : 0 ≤ r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ) :=
    div_nonneg (div_nonneg (Real.rpow_nonneg hr.le _) hr.le) (Nat.cast_nonneg _)
  have hsub : S.image cls ⊆ J₀ := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hC.cls_mem q (hC.sub hq)
  have hlines : ((S.image cls).card : ℝ) ≤ r ^ (-(2 * s) - ε₀) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hC.fail.few_lines J₀ hC.lines_sub hC.lines_sep).le
  unfold winConst windowGeomConst
  exact window_coefficient_le_power hr hr1 hs1 hε nearTubeConst_pos.le
    (by unfold arcTubeConst; positivity) (pinConst_nonneg' hw hw26 hCY)
    (Nat.cast_nonneg _) hpin hlines

/-- The full line-Frostman constant, including the measured-profile and
palette errors, is bounded by one explicit power of the fine scale. -/
theorem HighConfig.lineFrConst_le_power
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {ℓ ν d : ℝ} {KY : ℕ} (hr1 : r ≤ 1) (hr26 : 26 * r ≤ 1) (hn : 0 < n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε₀ : 0 ≤ ε₀)
    (hℓ : 0 ≤ ℓ) (hν : 0 ≤ ν) (hd : 0 ≤ d)
    (hpin : pinConst r (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY ≤
      r ^ (-2 * ε - ν)) :
    lineFrConst r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
      (S.image cls).card d (palBase r n) ≤
      windowPowerConst s * r ^ (-(20 * ε + ε₀ + ℓ * s + ν + 4 * d + 2 * s / n)) := by
  have hr := hC.fail.r_pos
  have hCY : 0 ≤ r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ) :=
    div_nonneg (div_nonneg (Real.rpow_nonneg hr.le _) hr.le) (Nat.cast_nonneg _)
  have hwin := hC.winConst_le_power (ℓ := ℓ) hr1 hs1 hε hr hr26 hpin
  have hwin0 : 0 ≤ winConst r s ε (r ^ (-ε)) (r ^ ℓ) r
      (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card :=
    winConst_nonneg hr (Real.rpow_nonneg hr.le _) (Real.rpow_pos_of_pos hr _) hr hr26 hCY
      (Nat.cast_nonneg _)
  have hgeom : 0 ≤ windowGeomConst := by
    unfold windowGeomConst
    have := nearTubeConst_pos
    positivity
  have hcoeff := palette_coefficient_le_power (L := 320) hr hr1 hn hs0 hd
    (by positivity : 0 ≤ 20 * ε + ε₀ + ℓ * s + ν) hwin0 hgeom (by norm_num) hwin
  have hlarge : (1 : ℝ) ≤ (320 : ℝ) ^ (2 * s) := Real.one_le_rpow (by norm_num) (by linarith)
  have hBpos := palBase_pos (n := n) hr
  have hterm : 0 ≤ winConst r s ε (r ^ (-ε)) (r ^ ℓ) r
      (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card *
      r ^ (-4 * d) * (palBase r n * 320) ^ (2 * s) := by positivity
  refine (max_le ?_ ?_).trans hcoeff
  · exact hlarge.trans (le_add_of_nonneg_right hterm)
  · rw [show (320 : ℝ) * palBase r n = palBase r n * 320 by ring]
    simpa only [neg_mul] using le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 320) (2 * s))

/-- The actual window lines satisfy the required all-radius Frostman bound
with the prescribed power loss. Only explicit scale inequalities and one
linear error budget remain for the final parameter choice. -/
theorem window_line_frostman_power {s c ζ ν q : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hζ : 0 < ζ) (hν : 0 < ν)
    (hq : 0 ≤ q) (hqs : q ≤ 2 * s) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 52 ∧
      ∀ r ε₀ ε κ ℓ d : ℝ, ∀ n a h : ℕ,
        ∀ (P : Finset E2) (D S J₀ : Finset (E2 × E2))
          (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
          (tb : ℕ → E2 × E2 → E2 × E2),
        HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb → r ≤ r₀ →
        0 ≤ ε → ε ≤ 1 → 0 ≤ ε₀ → 0 ≤ ℓ → 0 ≤ d → 0 < n → a ≤ n → h ≤ n →
        2 * palScale r n a ≤ palScale r n h → 10 * r ≤ palScale r n h →
        21440 * palBase r n * palScale r n h ≤ 1 / 2 →
        r ≤ r ^ ℓ → r ^ (-κ) * (r ^ ℓ) ^ (1 - s) ≤ 1 / 2 →
        243 * palScale r n a / (128 * palScale r n h) ≤ 2 * r ^ c →
        20 * ε + ε₀ + ℓ * s + ν + 4 * d + 2 * s / n ≤ c * ζ / 2 →
        ∀ p₀ ∈ S.image Prod.fst,
          (∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) →
          ∀ T ∈ S.image (fun q => tb h (tb a (cls q))),
          ∀ x y ρ : ℝ, 243 * palScale r n a / (128 * palScale r n h) ≤ ρ →
            (((windowLines S cls tb a h T).filter (fun j =>
              |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
                (4 * (16 * palScale r n h)) j).1 - x| ≤ ρ ∧
              |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
                (4 * (16 * palScale r n h)) j).2 - y| ≤ ρ)).card : ℝ) ≤
              (243 * palScale r n a / (128 * palScale r n h)) ^ (-ζ) *
                ρ ^ q * (windowLines S cls tb a h T).card := by
  classical
  obtain ⟨rP, hrP, hrP1, hpin⟩ := fail_pinConst_small_power hν
  have hC : 0 ≤ windowPowerConst s := by
    unfold windowPowerConst windowGeomConst
    have := nearTubeConst_pos
    positivity
  obtain ⟨rT, hrT, hrT1, htransfer⟩ := small_loss_transfer hc hζ hC (D := 2) (by norm_num)
  obtain ⟨rS, hrS, hsmall⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    hc (by norm_num : (0 : ℝ) < 1 / 2)
  let r₀ := min rP (min rT (min rS (1 / 52)))
  refine ⟨r₀, lt_min hrP (lt_min hrT (lt_min hrS (by norm_num))),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro r ε₀ ε κ ℓ d n a h P D S J₀ cls J₁ tb hC hrr hε hε1 hε₀ hℓ hd hn ha hh
    hδρ hrρ hρsmall hrc hfar hδr hbudget p₀ hp₀ hunif T hT x y ρ hρ
  have hr := hC.fail.r_pos
  have hrP' : r ≤ rP := hrr.trans (min_le_left _ _)
  have hrT' : r ≤ rT := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrS' : r ≤ rS := hrr.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hr52 : r ≤ 1 / 52 := hrr.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r < 1 := by linarith
  have hpal (i : ℕ) : 0 < palScale r n i := Real.rpow_pos_of_pos (palBase_pos hr) _
  let δ := 243 * palScale r n a / (128 * palScale r n h)
  have hδ : 0 < δ := div_pos (mul_pos (by norm_num) (hpal a))
    (mul_pos (by norm_num) (hpal h))
  have hδ1 : δ ≤ 1 := by
    have hh := hsmall r hr hrS'
    change δ ≤ 2 * r ^ c at hδr
    linarith
  have hK : 1 ≤ δ ^ (-ζ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_nonpos.mpr hζ.le)
  obtain ⟨KY, hKY, hPC⟩ := hpin r s ε₀ ε (S.image Prod.fst) S hC.failS hrP' hε1
  have hPCr := hPC r le_rfl (by linarith)
  have hcoeff := hC.lineFrConst_le_power (ℓ := ℓ) (ν := ν) (d := d)
    hr1.le (by linarith) hn hs0 hs1 hε hε₀ hℓ hν.le hd hPCr
  have hfit := htransfer r δ (20 * ε + ε₀ + ℓ * s + ν + 4 * d + 2 * s / n)
    hr hrT' hδ hδr hbudget
  have hthreshold : palScale r n a / (100 * palScale r n h) ≤
      243 * palScale r n a / (128 * palScale r n h) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (hpal h)) (mul_pos (by norm_num) (hpal h))]
    have hp := mul_pos (hpal a) (hpal h)
    nlinarith only [hp]
  have hfr := hC.window_line_frostman hs0 hs1 hn hr1 ha hh hδρ hrρ hρsmall
    hT hp₀ hrc hfar KY hKY hunif x y ρ (hthreshold.trans hρ)
  have hρ0 : 0 < ρ := hδ.trans_le hρ
  by_cases hρ1 : ρ ≤ 1
  · calc
      _ ≤ lineFrConst r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
          (S.image cls).card d (palBase r n) * ρ ^ (2 * s) *
            (windowLines S cls tb a h T).card := hfr
      _ ≤ δ ^ (-ζ) * ρ ^ q * (windowLines S cls tb a h T).card := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul (hcoeff.trans hfit)
          (Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 hqs)
          (Real.rpow_nonneg hρ0.le _) (Real.rpow_nonneg hδ.le _)
  · have hρpow : 1 ≤ ρ ^ q := Real.one_le_rpow (le_of_not_ge hρ1) hq
    have hcount : (((windowLines S cls tb a h T).filter (fun j =>
              |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
                (4 * (16 * palScale r n h)) j).1 - x| ≤ ρ ∧
              |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
                (4 * (16 * palScale r n h)) j).2 - y| ≤ ρ)).card : ℝ) ≤
          (windowLines S cls tb a h T).card := by exact_mod_cast Finset.card_filter_le _ _
    exact hcount.trans (le_mul_of_one_le_left (Nat.cast_nonneg _)
      (one_le_mul_of_one_le_of_one_le hK hρpow))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
