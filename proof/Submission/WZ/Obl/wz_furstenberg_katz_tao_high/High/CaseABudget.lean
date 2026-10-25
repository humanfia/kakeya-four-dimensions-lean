-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseABudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAPowers
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowLinePower

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

noncomputable def caseAQuadraticConst : ℝ :=
  64 * (5200 * nearTubeConst) * arcTubeConst ^ (4 : ℕ) * 98 ^ (2 : ℕ) * 36

noncomputable def caseACodeConst : ℝ :=
  96 * (5200 * nearTubeConst) * arcTubeConst ^ (3 : ℕ) * 98 ^ (2 : ℕ)

noncomputable def caseAPowerConst (s : ℝ) : ℝ :=
  27 + windowPowerConst s + caseAQuadraticConst + caseACodeConst * 2 ^ s + 31422600

theorem caseAPowerConst_bounds (s : ℝ) :
    27 ≤ caseAPowerConst s ∧ windowPowerConst s ≤ caseAPowerConst s ∧
      caseAQuadraticConst ≤ caseAPowerConst s ∧
      caseACodeConst * 2 ^ s ≤ caseAPowerConst s ∧ 31422600 ≤ caseAPowerConst s := by
  have hCn := nearTubeConst_pos
  have hAC : 0 < arcTubeConst := by unfold arcTubeConst; norm_num
  have hline : 0 ≤ windowPowerConst s := by unfold windowPowerConst windowGeomConst; positivity
  have hquad : 0 ≤ caseAQuadraticConst := by unfold caseAQuadraticConst; positivity
  have hcode : 0 ≤ caseACodeConst * 2 ^ s := by unfold caseACodeConst; positivity
  unfold caseAPowerConst
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The code exponent has the gap `(1-s)/2` needed by the expansion theorem. -/
theorem caseA_code_transfer {ρ R δ K s e : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hδ : 0 < δ) (hs : 0 ≤ s)
    (htol : δ ≤ 2 * (R / ρ)) (hK : K * 2 ^ s ≤ δ ^ (-e)) :
    K * (ρ / R) ^ s ≤ δ ^ (-(e + s)) := by
  rcases le_or_gt K 0 with hKn | hKp
  · exact (mul_nonpos_of_nonpos_of_nonneg hKn (Real.rpow_nonneg (by positivity) _)).trans
      (Real.rpow_nonneg hδ.le _)
  have hratio : ρ / R ≤ 2 / δ := by
    rw [div_le_div_iff₀ hR hδ]
    have hh := (le_div_iff₀ hρ).mp (show δ ≤ (2 * R) / ρ by simpa only [mul_div_assoc'] using htol)
    nlinarith only [hh]
  calc
    K * (ρ / R) ^ s ≤ K * (2 / δ) ^ s := by gcongr
    _ = (K * 2 ^ s) * δ ^ (-s) := by
      rw [Real.div_rpow (by norm_num) hδ.le, Real.rpow_neg hδ.le]
      ring
    _ ≤ δ ^ (-e) * δ ^ (-s) :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-(e + s)) := by rw [← Real.rpow_add hδ]; congr 1; ring

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- All three coefficient bounds at a window fit a single linear error
budget. The same dyadic range is used for the tube and the fine scale. -/
theorem HighConfig.caseA_constants_le_power
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {ℓ ν d w : ℝ} {KY : ℕ}
    (hr1 : r ≤ 1) (hr26 : 26 * r ≤ 1) (hn : 0 < n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε₀ : 0 ≤ ε₀) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hν : 0 ≤ ν) (hd : 0 ≤ d)
    (hw : 0 < w) (hw26 : 26 * w ≤ 1)
    (hpinr : pinConst r (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY ≤ r ^ (-2 * ε - ν))
    (hpinw : pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY ≤ r ^ (-2 * ε - ν)) :
    let U := 30 * ε + ε₀ + ℓ * s + ν + 4 * d + 2 * s / n + κ
    let Q := caseAPowerConst s * r ^ (-U)
    let Z := winZ r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card w
    max (max 27 (lineFrConst r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
      (S.image cls).card d (palBase r n))) (winK0J r s ε d Z) ≤ Q ∧
    twoEndedConst r κ ε ≤ Q ∧ winC2 r s ε d Z * 2 ^ s ≤ Q := by
  dsimp only
  let U := 30 * ε + ε₀ + ℓ * s + ν + 4 * d + 2 * s / n + κ
  let Z := winZ r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card w
  have hr := H.fail.r_pos
  have hCn := nearTubeConst_pos
  have hAC : 0 < arcTubeConst := by unfold arcTubeConst; norm_num
  have hB := caseAPowerConst_bounds s
  have hB0 : 0 ≤ caseAPowerConst s := by linarith only [hB.1]
  have hlen : 0 ≤ 2 * s / (n : ℝ) := by positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have lift {C u : ℝ} (hC : 0 ≤ C) (hCB : C ≤ caseAPowerConst s) (hu : u ≤ U) :
      C * r ^ (-u) ≤ caseAPowerConst s * r ^ (-U) := by
    exact mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith))
      (Real.rpow_nonneg hr.le _) hB0
  have hZ : Z ≤ (5200 * nearTubeConst) * r ^ (-(10 * ε + 2 * s + (ε₀ + ℓ * s + ν))) := by
    convert H.winZ_le_power (ℓ := ℓ) hr1 hs1 hε hw hw26 hpinw using 1 <;> ring
  have hquad := winK0J_le_power (d := d) hr hs1 (by positivity : 0 ≤ 5200 * nearTubeConst) hZ
  have hcode := winC2_le_power (d := d) hr hs1 (by positivity : 0 ≤ 5200 * nearTubeConst) hZ
  have hline := H.lineFrConst_le_power hr1 hr26 hn hs0 hs1 hε hε₀ hℓ hν hd hpinr
  have h27 : (27 : ℝ) ≤ caseAPowerConst s * r ^ (-U) := by
    simpa using lift (C := 27) (u := 0) (by norm_num) hB.1 hU
  have hline' := hline.trans (lift (by unfold windowPowerConst windowGeomConst; positivity)
    hB.2.1 (by dsimp [U]; linarith only [hε, hκ]))
  have hquad' := hquad.trans (lift (by positivity)
    hB.2.2.1 (by dsimp [U]; linarith only [hε, hd, hlen, hκ]))
  have htwo : twoEndedConst r κ ε = 31422600 * r ^ (-(κ + 2 * ε)) := by
    unfold twoEndedConst
    calc
      _ = 31422600 * (r ^ (-κ) * (r ^ (-ε)) ^ (2 : ℕ)) := by ring
      _ = _ := by
        rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
        congr 1
        norm_num
        ring
  have htwo' : twoEndedConst r κ ε ≤ caseAPowerConst s * r ^ (-U) := by
    rw [htwo]
    exact lift (by norm_num) hB.2.2.2.2 (by dsimp [U]; nlinarith only [hε, hε₀, hℓ, hs0, hν, hd, hlen])
  have hcode' : winC2 r s ε d Z * 2 ^ s ≤ caseAPowerConst s * r ^ (-U) := by
    calc
      _ ≤ (caseACodeConst * r ^ (-(24 * ε + (ε₀ + ℓ * s + ν) + 3 * d))) * 2 ^ s :=
        mul_le_mul_of_nonneg_right hcode (Real.rpow_nonneg (by norm_num) _)
      _ = (caseACodeConst * 2 ^ s) * r ^ (-(24 * ε + (ε₀ + ℓ * s + ν) + 3 * d)) := by ring
      _ ≤ _ := lift (by unfold caseACodeConst; positivity) hB.2.2.2.1
        (by dsimp [U]; linarith only [hε, hd, hlen, hκ])
  exact ⟨max_le (max_le h27 hline') hquad', htwo', hcode'⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
