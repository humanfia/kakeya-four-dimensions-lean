-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAContradiction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 High/CaseAContradiction.lean (1a70b6b).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseANumerics
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowTwoEnded

/-!
# Case A at a window, with a dense tube: the contradiction

`caseA_window_contradiction` puts the pieces together at one window `(a, h)` of a `HighConfig`
(`δ = palScale a`, `ρ = palScale h`, columns of width `ρ / 2`) and one composed tube `T` whose
(column, `δ`-line) relation has density `dens`:

* geometry: `window_geometry`;
* pin degree `M = avg_h / (K² C · 2 r^-ε (3δ/r)^s)`: `window_pin_degree`;
* `64 #J ≤ K0J M²` and `8 #J / M ≤ winC2 (ρ/δ)^s`: `window_lines_card_le_avg`, `arcAvg_bounds`,
  `quad_algebra`, `code_algebra`;
* two-ended lines: `window_two_ended` (`A = twoEndedConst`, exponent `β = 1 - s`);
* tube-line Frostman: x0688's `HighConfig.window_line_frostman` (exponent `2 s = 1 + b`);
* x0665's `tube_two_ends_false` in the tube frame: `caseA_window_two_ends_false`.

The numeric conditions (all constants `≤ tol^-η`, `tol^η ≤ dens`, the code bound) are
hypotheses here; the leaf discharges them for small parameters.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance 10] Classical.propDecidable

noncomputable section

/-- The count constant of `window_lines_card_le_avg`. -/
def winZ (r s ε c₂ CY : ℝ) (KY : ℕ) (L ρ : ℝ) : ℝ :=
  (r ^ (-ε)) ^ 2 * (quadConst r s ε (r ^ (-ε)) c₂ * L) * (nearTubeConst * pinConst ρ CY KY)

/-- The constant of `64 #J ≤ K0J M²`. -/
def winK0J (r s ε d Z : ℝ) : ℝ :=
  64 * Z * ((r ^ (-ε)) ^ 2 * arcTubeConst) ^ 4 * (2 * (49 * r ^ (-ε))) ^ 2 *
    (2 * r ^ (-ε) * 3 ^ s) ^ 2 / ((r ^ (ε + d)) ^ 2 * (r ^ (ε - s)) ^ 2)

/-- The constant of `8 #J / M ≤ winC2 (ρ / δ)^s`. -/
def winC2 (r s ε d Z : ℝ) : ℝ :=
  8 * Z * ((r ^ (-ε)) ^ 2 * arcTubeConst) ^ 3 * (2 * (49 * r ^ (-ε))) ^ 2 *
    (2 * r ^ (-ε) * 3 ^ s) * (2 ^ s * r ^ (-(ε + d))) / ((r ^ (ε + d)) ^ 2 * (r ^ (ε - s)) ^ 2)

/-- **Case A at a window with a dense tube is contradictory.** -/
theorem caseA_window_contradiction {s η δ₀ : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hTE : TwoEndsFalse ((1 - s) / 2) (2 * s - 1) (1 - s) η δ₀)
    {r ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) (hn : 0 < n) (hr1 : r < 1)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hrδ : 10 * r ≤ palScale r n a) (hδρ30 : 30 * palScale r n a ≤ palScale r n h)
    (hρδ : palScale r n h ^ 2 ≤ palScale r n a)
    (hρsmall : 21440 * palBase r n * palScale r n h ≤ 1 / 2)
    {d : ℝ} (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n)
    {c₂ : ℝ} (hrc : r ≤ c₂) (hcfar : r ^ (-κ) * c₂ ^ (1 - s) ≤ 1 / 2) (KY : ℕ)
    (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY)
    {T : E2 × E2} (hT : T ∈ S.image (fun q => tb h (tb a (cls q))))
    {dens : ℝ}
    (hdens : dens * (((windowPins S cls tb a h T).image
        (tubeCol (tubeAxis T) (palScale r n h / 2))).card : ℝ) *
        (windowLines S cls tb a h T).card ≤
      ((((windowPins S cls tb a h T).image (tubeCol (tubeAxis T) (palScale r n h / 2))) ×ˢ
        (windowLines S cls tb a h T)).filter (fun p : ℝ × (E2 × E2) =>
          ∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T p.2 x ∧
            tubeCol (tubeAxis T) (palScale r n h / 2) x = p.1)).card)
    (hdens1 : dens ≤ 1)
    (htol : tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤ δ₀)
    (hdη : (tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2)) ^ η ≤ dens)
    (hK₀η : max (max 27 (lineFrConst r s ε c₂ (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
        (S.image cls).card d (palBase r n)))
        (winK0J r s ε d (winZ r s ε c₂ (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
          (S.image cls).card (palScale r n h))) ≤
      (tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2)) ^ (-η))
    (hAη : twoEndedConst r κ ε ≤
      (tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2)) ^ (-η))
    (hcode : winC2 r s ε d (winZ r s ε c₂ (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
          (S.image cls).card (palScale r n h)) * (palScale r n h / palScale r n a) ^ s ≤
      (tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2)) ^
        (-(1 - (1 - s) / 2))) : False := by
  set δ := palScale r n a with hδ
  set ρ := palScale r n h with hρ
  set K := r ^ (-ε) with hK
  have hr0 : 0 < r := hC.fail.r_pos
  have hK0 : 0 < K := Real.rpow_pos_of_pos hr0 _
  have hδ0 : 0 < δ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hB1 : 1 ≤ palBase r n := (palBase_gt_one hr0 hr1 hn).le
  have hρ142 : 142 * ρ ≤ 1 / 2 := by
    have h1 : 1 * ρ ≤ palBase r n * ρ := mul_le_mul_of_nonneg_right hB1 hρ0.le
    linarith
  have hρ12 : ρ ≤ 1 / 2 := by linarith
  have hδρ2 : 2 * δ ≤ ρ := by linarith
  have hrδ1 : r ≤ δ := by linarith
  -- the tube `T`
  obtain ⟨qT, hqT, hqTT⟩ := Finset.mem_image.mp hT
  have hDn : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 := fun q hq =>
    ⟨hC.fail.P_norm _ (hC.fail.D_mem q hq).1, (hC.fail.D_mem q hq).2⟩
  have hclsJ : cls qT ∈ J₀ := hC.cls_mem qT (hC.sub hqT)
  have hlJ : tb a (cls qT) ∈ J₀ := hC.tubes_sub a (hC.tube_mem a ha _ hclsJ)
  have hTJ : T ∈ J₀ := by rw [← hqTT]; exact hC.tubes_sub h (hC.tube_mem h hh _ hlJ)
  obtain ⟨hT4, hT2⟩ := hDn T (hC.lines_sub hTJ)
  have hqTW : qT ∈ windowLabels S cls tb a h T := mem_windowLabels.mpr ⟨hqT, hqTT⟩
  have hJne : (windowLines S cls tb a h T).Nonempty := ⟨_, Finset.mem_image_of_mem _ hqTW⟩
  have hUne : (windowPins S cls tb a h T).Nonempty := ⟨_, Finset.mem_image_of_mem _ hqTW⟩
  -- geometry
  obtain ⟨hgeo, hsep, hpinw, hU4⟩ := window_geometry hC ha hh hrδ1 T
  -- arc averages
  set avgH := arcAvg ρ S p₀ with havgH
  set avgA := arcAvg δ S p₀ with havgA
  obtain ⟨havgH_lo, havgH_hi⟩ := arcAvg_bounds hC hr1 hn hp₀ hunif hh
  obtain ⟨havgA_lo, -⟩ := arcAvg_bounds hC hr1 hn hp₀ hunif ha
  have havgH0 : 0 < avgH := lt_of_lt_of_le (by positivity) havgH_lo
  -- pin degree
  have harc : ∀ p ∈ S.image Prod.fst, ∀ e ∈ bushOf S p,
      avgH ≤ K * ((arcNormals ρ S p e).card : ℝ) := by
    intro p _ e he
    exact (hC.arc_avg_bounds hh hp₀ (p, e) (mem_bushOf.mp he)).2
  set Kc := K ^ 2 * arcTubeConst with hKc
  have hCa : 0 < arcTubeConst := by unfold arcTubeConst; norm_num
  have hKc0 : 0 < Kc := by positivity
  set q := 2 * K * 3 ^ s with hq
  set u := (δ / r) ^ s with hu
  have hq0 : 0 < q := by positivity
  have hu0 : 0 < u := by positivity
  set M := avgH / (Kc * (q * u)) with hM
  have hM0 : 0 < M := by positivity
  have h3δ : (3 * δ / r) ^ s = 3 ^ s * u := by
    rw [hu, show 3 * δ / r = 3 * (δ / r) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  have hdeg : ∀ x ∈ windowPins S cls tb a h T,
      M ≤ (((windowLines S cls tb a h T).filter
        (fun j => windowPin S cls tb a h T j x)).card : ℝ) := by
    intro x hx
    have hpd := window_pin_degree hC ha hh hrδ1 (by linarith) hρ142 hK0
      (hC.bal_pin_tube2 h hh a ha) harc T hx
    have e : M = avgH / (K ^ 2 * arcTubeConst) / (2 * (K * (3 * δ / r) ^ s)) := by
      rw [hM, hKc, hq, h3δ]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  -- the window count
  set CY := r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ) with hCY
  set Z := winZ r s ε c₂ CY KY (S.image cls).card ρ with hZ
  have hcount := window_lines_card_le_avg hC hs0 hs1.le ha hh hrδ hδρ2 hρ142 hT hp₀ hrc hcfar
    KY hKY
  have hZ0 : 0 ≤ Z := by
    rw [hZ]; unfold winZ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
      (quadConst_nonneg hr0 hK0.le (by linarith)) (Nat.cast_nonneg _)))
      (mul_nonneg nearTubeConst_pos.le (pinConst_nonneg' hρ0 (by linarith) (by positivity)))
  set v := r ^ (ε + d) with hv
  set Rm := r ^ (ε - s) with hRm
  have hv0 : 0 < v := Real.rpow_pos_of_pos hr0 _
  have hRm0 : 0 < Rm := Real.rpow_pos_of_pos hr0 _
  -- `64 #J ≤ K0J M²`
  have hq64 := quad_algebra (Jc := ((windowLines S cls tb a h T).card : ℝ)) (Z := Z) (a := avgA)
    (H := avgH) (Kc := Kc) (K := K) (Rm := Rm) (u := u) (v := v) (q := q) hZ0 hKc0 hK0 havgH0
    hRm0 hu0 hv0 hq0 hcount havgA_lo
  have hK0J : 64 * Z * Kc ^ 4 * (2 * (49 * K)) ^ 2 * q ^ 2 / (v ^ 2 * Rm ^ 2) =
      winK0J r s ε d Z := by
    unfold winK0J; rw [hKc, hq, hv, hRm]
  rw [hK0J] at hq64
  -- `8 #J / M ≤ winC2 (ρ / δ)^s`
  have hHu : avgH / u ≤ 2 ^ s * r ^ (-(ε + d)) * (ρ / δ) ^ s := by
    rw [div_le_iff₀ hu0]
    have e1 : (ρ / δ) ^ s * (δ / r) ^ s = (ρ / r) ^ s := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    have e : 2 ^ s * r ^ (-(ε + d)) * (ρ / δ) ^ s * u = 2 ^ s * (ρ / r) ^ s * r ^ (-(ε + d)) := by
      calc 2 ^ s * r ^ (-(ε + d)) * (ρ / δ) ^ s * u
          = 2 ^ s * r ^ (-(ε + d)) * ((ρ / δ) ^ s * (δ / r) ^ s) := by rw [hu]; ring
        _ = 2 ^ s * (ρ / r) ^ s * r ^ (-(ε + d)) := by rw [e1]; ring
    rw [e]; exact havgH_hi
  have hcode0 := code_algebra (Jc := ((windowLines S cls tb a h T).card : ℝ)) (Z := Z)
    (a := avgA) (H := avgH) (Kc := Kc) (K := K) (Rm := Rm) (u := u) (v := v) (q := q)
    (Hu := 2 ^ s * r ^ (-(ε + d)) * (ρ / δ) ^ s) hZ0 hKc0 hK0 havgH0 hRm0 hu0 hv0 hq0 hcount
    havgA_lo hHu
  have hC2 : 8 * Z * Kc ^ 3 * (2 * (49 * K)) ^ 2 * q * (2 ^ s * r ^ (-(ε + d)) * (ρ / δ) ^ s) /
      (v ^ 2 * Rm ^ 2) = winC2 r s ε d Z * (ρ / δ) ^ s := by
    unfold winC2; rw [hKc, hq, hv, hRm]; ring
  rw [hC2] at hcode0
  -- the constants of the tube contradiction
  set LF := lineFrConst r s ε c₂ CY KY (S.image cls).card d (palBase r n) with hLF
  set K₀ := max (max 27 LF) (winK0J r s ε d Z) with hK₀
  have hK₀27 : 27 ≤ K₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hLFK : LF ≤ K₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hK0JK : winK0J r s ε d Z ≤ K₀ := le_max_right _ _
  have hquad : 64 * ((windowLines S cls tb a h T).card : ℝ) ≤ K₀ * M ^ 2 :=
    hq64.trans (mul_le_mul_of_nonneg_right hK0JK (sq_nonneg _))
  have hF : 8 * ((windowLines S cls tb a h T).card : ℝ) / M ≤
      (tubeTol (27 * δ) (16 * ρ) (ρ / 2)) ^ (-(1 - (1 - s) / 2)) := by
    refine le_trans ?_ hcode
    rw [hM]; exact hcode0
  -- two-ended lines
  have htwo := window_two_ended hC ha hh hs0 hs1.le hrδ1 hρ12 hδρ2 hρδ T hT2
  have hA0 : 0 ≤ twoEndedConst r κ ε := by unfold twoEndedConst; positivity
  -- tube-line Frostman
  have htolδ : δ / (100 * ρ) ≤ tubeTol (27 * δ) (16 * ρ) (ρ / 2) := by
    rw [tubeTol_half hρ0, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 ≤ 8 * ρ ^ 2 * (100 * ρ) := by positivity
    have h2 : δ * (64 * ρ) ≤ 108 * δ * (100 * ρ) := by
      have := mul_pos hδ0 hρ0
      linarith
    linarith
  have hlf := hC.window_line_frostman hs0 hs1.le hn hr1 ha hh hδρ2 (by linarith) hρsmall hT hp₀
    hrc hcfar KY hKY hunif
  have hlinefr : ∀ x y ρ' : ℝ, tubeTol (27 * δ) (16 * ρ) (ρ / 2) ≤ ρ' →
      (((windowLines S cls tb a h T).filter (fun j =>
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).1 - x| ≤ ρ' ∧
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).2 - y| ≤ ρ')).card : ℝ) ≤
        K₀ * ρ' ^ (1 + (2 * s - 1)) * (windowLines S cls tb a h T).card := by
    intro x y ρ' hρ'
    have h1 := hlf x y ρ' (htolδ.trans hρ')
    have he : (1 + (2 * s - 1)) = 2 * s := by ring
    rw [he]
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right hLFK
    have hρ'0 : 0 ≤ ρ' := (le_trans (by positivity) htolδ).trans hρ'
    exact Real.rpow_nonneg hρ'0 _
  -- the contradiction in the tube
  have hscale : 4 * (16 * ρ) * (ρ / 2) ≤ 2 * (27 * δ) := by
    have e : 4 * (16 * ρ) * (ρ / 2) = 32 * ρ ^ 2 := by ring
    rw [e]; linarith
  exact caseA_window_two_ends_false hTE hT2 hT4 hρ0 hδ0 hρ12 (by positivity) hscale hM0 hK₀27 hA0
    htol hK₀η hAη hdη hdens1 (windowLines S cls tb a h T) (windowPins S cls tb a h T)
    (windowPin S cls tb a h T) hJne hUne hF hgeo hsep hpinw hU4 hdeg hdens htwo hlinefr hquad

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
