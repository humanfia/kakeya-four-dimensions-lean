-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAFromDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAParameters
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseACutoffs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.OneLeaf

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The remaining density input, on the original fine pins and the actual
window objects. All geometric and numerical consequences are supplied by
`caseALeaf_of_density`. -/
def DenseWindowLeaf (s : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ ε' : ℝ, 0 < ε' ∧ ∃ N₀ : ℕ,
    ∀ n : ℕ, N₀ ≤ n → ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (r ε₀ ε κ : ℝ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
        (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
        (tb : ℕ → E2 × E2 → E2 × E2),
        0 < r → r ≤ r₀ → 0 < ε₀ → ε₀ ≤ ε' → 0 < ε → ε ≤ ε' → 0 < κ → κ ≤ ε' →
        HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb →
        ∀ d : ℝ, 0 ≤ d → ∀ p₀ ∈ S.image Prod.fst, ∀ h a : ℕ,
          0 < h → h < a → a ≤ n →
          (∀ i : ℕ, h ≤ i → i ≤ a → ptProfile r n S h - s * h ≤ ptProfile r n S i - s * i) →
          (∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) →
          ∃ T ∈ S.image (fun q => tb h (tb a (cls q))),
            r ^ (3 * d + e) * (((windowPins S cls tb a h T).image
              (tubeCol (tubeAxis T) (palScale r n h / 2))).card : ℝ) *
              (windowLines S cls tb a h T).card ≤
            ((((windowPins S cls tb a h T).image (tubeCol (tubeAxis T) (palScale r n h / 2))) ×ˢ
              windowLines S cls tb a h T).filter (fun p : ℝ × (E2 × E2) =>
                ∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T p.2 x ∧
                  tubeCol (tubeAxis T) (palScale r n h / 2) x = p.1)).card

/-- Dense window columns complete Case A, including the palette endpoint
and every parameter choice required by the top-level leaf. -/
theorem caseALeaf_of_density {s : ℝ} (hslo : 1 / 2 < s) (hs1 : s < 1)
    (hD : DenseWindowLeaf s) : CaseALeaf s := by
  intro c L hc hL
  have hs0 : 0 ≤ s := by linarith
  have hL0 : 0 < L := by linarith
  let c' := c / 2
  let L' := 2 * L
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hL' : 1 ≤ L' := by dsimp [L']; linarith
  let γ := c' / L'
  have hγ : 0 < γ := by dsimp [γ, L']; positivity
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀1, hTE⟩ := exists_twoEndsFalse
    (e := (1 - s) / 2) (b := 2 * s - 1) (β := 1 - s)
    (by positivity) (by linarith) (by linarith)
  obtain ⟨ℓ, d₀, εK, NK, hℓ, hℓ1, hd₀, hεK, hεK1, hNK, hKcut⟩ :=
    caseA_parameter_cutoff hs0 hs1 hγ hη
  let e := γ * η / 4
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨εD, hεD, ND, hDcut⟩ := hD e he
  obtain ⟨NG, hNG, hGcut⟩ := caseA_geometry_cutoff hc' hL' hδ₀
  obtain ⟨NT, hNT⟩ := exists_nat_gt (4 * L + 4 * L / c + 1)
  let d := min d₀ (γ * η / 12)
  let ε' := min εK εD
  have hd : 0 < d := lt_min hd₀ (by positivity)
  have hε' : 0 < ε' := lt_min hεK hεD
  obtain ⟨rS, hrS, hsmall⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := γ * η / 2) (B := (2 : ℝ) ^ (-η)) (by positivity) (by positivity)
  refine ⟨d, ε', hd, hε', max NK (max ND (max NG NT)), ?_⟩
  intro n hn
  have hnK : NK ≤ n := (le_max_left _ _).trans hn
  have hnD : ND ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnG : NG ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnT : NT ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnpos : 0 < n := hNK.trans_le hnK
  have hnL : 4 * L ≤ (n : ℝ) := by
    have hh : (NT : ℝ) ≤ n := by exact_mod_cast hnT
    have hpos : 0 < 4 * L / c := by positivity
    linarith
  have hnc : 4 * L / c ≤ (n : ℝ) := by
    have hh : (NT : ℝ) ≤ n := by exact_mod_cast hnT
    linarith
  obtain ⟨rK, hrK, hrK52, hnum⟩ := hKcut n hnK
  obtain ⟨rD, hrD, hdense⟩ := hDcut n hnD
  obtain ⟨rG, hrG, hrG52, hgeom⟩ := hGcut n hnG
  refine ⟨min rD (min rK (min rG rS)), lt_min hrD (lt_min hrK (lt_min hrG hrS)), ?_⟩
  intro r ε₀ ε κ P D S J₀ cls J₁ tb hr hrr hε₀ hε₀' hε hεsmall hκ hκsmall H
    p₀ hp₀ h a han hna hah hgap hmin hunif
  have hrD' := hrr.trans (min_le_left _ _)
  have hrK' := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrG' := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrS' := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r < 1 := lt_of_le_of_lt (hrK'.trans hrK52) (by norm_num)
  have hwin := caseA_trim_window hc hL hnpos han hnL hnc hna hah hgap
  let a' := a - 1
  have hha : h < a' := hwin.1
  have ha'n : a' < n := hwin.2.1
  have hna' : (n : ℝ) ≤ L' * a' := hwin.2.2.1
  have hah' : (a' : ℝ) ≤ 2 * h := hwin.2.2.2.1
  have hgap' : (h : ℝ) + c' * a' ≤ a' := hwin.2.2.2.2
  have hh0 := (caseA_window_indices hc hL hnpos hna hah hgap).1
  have hhn : h ≤ n := hha.le.trans ha'n.le
  obtain ⟨hrR, hRρ, hsquare, hρsmall, htol, htolγ⟩ :=
    hgeom r hr hrG' h a' ha'n hna' hah' hgap'
  let ρ := palScale r n h
  let R := palScale r n a'
  let δ := tubeTol (27 * R) (16 * ρ) (ρ / 2)
  have hρ : 0 < ρ := palScale_pos (n := n) hr h
  have hR : 0 < R := palScale_pos (n := n) hr a'
  have hδ : 0 < δ := tubeTol_pos (by positivity) (by positivity) (by positivity)
  have hδ1 : δ ≤ 1 := htol.trans (by linarith only [hδ₀1])
  have hB := (palBase_gt_one hr hr1 hnpos).le
  have hBρ : ρ ≤ palBase r n * ρ := le_mul_of_one_le_left hρ.le hB
  have hρ26 : 26 * ρ ≤ 1 / 2 := by nlinarith only [hρsmall, hBρ, hρ]
  have hrρ : r ≤ ρ := r_le_palScale hr hr1 hnpos hhn
  obtain ⟨hrℓ, hfar, KY, hKY, hKK, hAA, hCC⟩ :=
    hnum r ε₀ ε κ d P D S J₀ cls J₁ tb H hrK'
      hε₀.le (hε₀'.trans (min_le_left _ _)) hε.le (hεsmall.trans (min_le_left _ _))
      hκ.le (hκsmall.trans (min_le_left _ _)) hd.le (min_le_left _ _)
      ρ δ hrρ hρ26 hδ hδ1 htolγ
  obtain ⟨T, hT, hTdense⟩ := hdense r ε₀ ε κ P D S J₀ cls J₁ tb hr hrD'
    hε₀ (hε₀'.trans (min_le_right _ _)) hε (hεsmall.trans (min_le_right _ _))
    hκ (hκsmall.trans (min_le_right _ _)) H d hd.le p₀ hp₀ h a' hh0 hha ha'n.le
    (fun i hhi hia => hmin i hhi (hia.trans (Nat.sub_le a 1))) hunif
  have hden1 : r ^ (3 * d + e) ≤ 1 := Real.rpow_le_one hr.le hr1.le (by positivity)
  have hbudget : 3 * d + e ≤ γ * η / 2 := by
    have hh : d ≤ γ * η / 12 := min_le_right _ _
    dsimp [e]
    linarith only [hh]
  have h2fit : (2 : ℝ) ^ η * r ^ (γ * η / 2) ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ η * 2 ^ (-η) :=
        mul_le_mul_of_nonneg_left (hsmall r hr hrS') (Real.rpow_nonneg (by norm_num) _)
      _ = 1 := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; simp
  have hdη : δ ^ η ≤ r ^ (3 * d + e) := by
    calc
      δ ^ η ≤ (2 * r ^ γ) ^ η := Real.rpow_le_rpow hδ.le htolγ hη.le
      _ = (2 : ℝ) ^ η * r ^ (γ * η) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
      _ = ((2 : ℝ) ^ η * r ^ (γ * η / 2)) * r ^ (γ * η / 2) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 1
        ring
      _ ≤ r ^ (γ * η / 2) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h2fit (Real.rpow_nonneg hr.le _)
      _ ≤ r ^ (3 * d + e) := Real.rpow_le_rpow_of_exponent_ge hr hr1.le hbudget
  have htRatio : δ ≤ 2 * (R / ρ) := by
    dsimp [δ]
    rw [tubeTol_half hρ, mul_div_assoc', div_le_div_iff₀ (by positivity) hρ]
    nlinarith only [hsquare, hR, hρ]
  have hcode := caseA_code_transfer hρ hR hδ hs0 htRatio hCC
  have hexp : -((1 - s) / 2 + s) = -(1 - (1 - s) / 2) := by ring
  rw [hexp] at hcode
  exact caseA_window_contradiction hs0 hs1 hTE H hnpos hr1 hp₀ ha'n.le hhn
    hrR hRρ hsquare hρsmall hunif hrℓ hfar KY hKY hT hTdense hden1 htol hdη hKK hAA hcode

/-- With the explicit dense-window estimate, the original high-range
Katz--Tao conclusion follows with no further geometric hypotheses. -/
theorem high_range_of_density {s : ℝ} (hslo : 1 / 2 < s) (hs1 : s < 1)
    (hD : DenseWindowLeaf s) : FixedKatzTaoAt s :=
  high_range_of_caseA (by linarith) hs1 (caseALeaf_of_density hslo hs1 hD)

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
