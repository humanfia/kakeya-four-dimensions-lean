-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyProfile
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.DenseCellTube

/-!
# A dense window tube in cells, from the premise counts

`HighConfig.dense_window_cells` has the hypotheses of x0651's
`HighConfig.energy_witness_of_coefficients` (the counts of the energy premise at the window
`(a, h)`, with their coefficient bounds) together with the window conditions of `CaseALeaf`:
`h` is a right-min of `G - s·id` on `[h, a]` and the bush profile is within `dn` of `s·id`.
It gives a window tube `t` whose (`δ`-line, `ρ`-cell) density is at least
`B^-(3 dn + 9 e) / 8` (`Columns.dense_cell_tube_of_profiles`). The setup of the counts is
copied from `energy_witness_of_coefficients` (x0651, High/EnergyProfile.lean).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- **A dense window tube in cells.** -/
theorem HighConfig.dense_window_cells
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    {h a : ℕ} (hha : h ≤ a) (han : a ≤ n) (hRsmall : palScale r n a ≤ 1 / 8)
    {ℓ ν e : ℝ} (hℓ1 : ℓ ≤ 1) (hfar : r ^ (-κ + ℓ * (1 - s)) ≤ 1 / 2) (he : 0 ≤ e)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst)
    (hsecond :
      (∑ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
        ((Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) (S.image (fun q => tb a (cls q))) (tb h) t).card : ℝ) ^ 2)
        ≤ 3 * r ^ (-(4 * ε + ν)) * (cellCount (S.image Prod.fst) (palScale r n h) : ℝ) ^ 2)
    (hWcoef : 8586240 * r ^ (-4 * ε) ≤ palBase r n ^ e)
    (hEcoef : 3 * r ^ (-(4 * ε + ν)) ≤ palBase r n ^ e)
    (hJcoef : (67080 : ℝ) ^ (2 : ℕ) * 5200 * r ^ (-(12 * ε + ε₀ + ℓ * s)) ≤ palBase r n ^ e)
    (hIcoef : 72 * r ^ (-2 * ε) ≤ palBase r n ^ e)
    (hUcoef : 4829760000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-4 * ε) ≤ palBase r n ^ e)
    (hpalette : ((Finset.Icc h a).card : ℝ) ≤ palBase r n ^ e)
    {dn : ℝ}
    (hright : ∀ i : ℕ, h ≤ i → i ≤ a →
      ptProfile r n S h - s * h ≤ ptProfile r n S i - s * i)
    (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ dn) :
    ∃ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
      palBase r n ^ (-(3 * dn + 9 * e)) / 8 *
          ((((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t)).card : ℝ) *
            (Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst)
              (cellOf (palScale r n h)) (S.image (fun q => tb a (cls q))) (tb h) t).card) ≤
        ∑ j ∈ (S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t),
          ((Columns.cellsHit S (fun q => tb a (cls q)) (S.image Prod.fst)
            (cellOf (palScale r n h)) j).card : ℝ) := by
  have hr := H.fail.r_pos
  let B := palBase r n
  let Q := S.image Prod.fst
  let J := S.image (fun q => tb a (cls q))
  let F := bushProfile r n S p₀
  let G := ptProfile r n S
  let N := Real.logb B (Q.card : ℝ)
  let W := 8586240 * r ^ (-4 * ε) * Q.card *
    cellCount (bushOf S p₀) (palScale r n a) /
      ((cellCount Q (palScale r n h) : ℝ) * cellCount (bushOf S p₀) (palScale r n h))
  let E := 3 * r ^ (-(4 * ε + ν)) * (cellCount Q (palScale r n h) : ℝ) ^ (2 : ℕ)
  have hB : 1 < B := palBase_gt_one hr hr1 hn
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hQ : 0 < (Q.card : ℝ) := Nat.cast_pos.mpr H.failS.P_ne.card_pos
  have hG (i : ℕ) : B ^ G i = (cellCount Q (palScale r n i) : ℝ) :=
    rpow_ptProfile hr hr1 hn H.failS.P_ne i
  have hF (i : ℕ) : B ^ F i = (cellCount (bushOf S p₀) (palScale r n i) : ℝ) :=
    rpow_bushProfile hr hr1 hn (H.bush_nonempty hp₀) i
  have hN : B ^ N = (Q.card : ℝ) := Real.rpow_logb hB0 hB.ne' hQ
  have hNh : (0 : ℝ) < cellCount Q (palScale r n h) :=
    Nat.cast_pos.mpr (cellCount_pos H.failS.P_ne _)
  have hMa : (0 : ℝ) < cellCount (bushOf S p₀) (palScale r n a) :=
    Nat.cast_pos.mpr (cellCount_pos (H.bush_nonempty hp₀) _)
  have hMh : (0 : ℝ) < cellCount (bushOf S p₀) (palScale r n h) :=
    Nat.cast_pos.mpr (cellCount_pos (H.bush_nonempty hp₀) _)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  have hwpow : W = (8586240 * r ^ (-4 * ε)) * B ^ (N - G h + F a - F h) := by
    simp only [Real.rpow_sub hB0, Real.rpow_add hB0, hN, hF, hG]
    dsimp only [W]
    ring
  have hWprofile : W ≤ B ^ (N - G h + F a - F h + e) := by
    rw [hwpow, Real.rpow_add hB0]
    exact mul_le_mul_of_nonneg_right hWcoef (Real.rpow_nonneg hB0.le _) |>.trans_eq (mul_comm _ _)
  have hep : E = (3 * r ^ (-(4 * ε + ν))) * B ^ (2 * G h) := by
    rw [show 2 * G h = G h * (2 : ℕ) by norm_num; ring,
      Real.rpow_mul_natCast hB0.le, hG]
  have hEprofile : E ≤ B ^ (2 * G h + e) := by
    rw [hep, Real.rpow_add hB0]
    exact (mul_le_mul_of_nonneg_right hEcoef (Real.rpow_nonneg hB0.le _)).trans_eq (mul_comm _ _)
  have hJprofile : (J.card : ℝ) ≤ B ^ (2 * F a + e) := by
    have hh := H.coarse_class_count hr1 hn hs0 hs1 hε hℓ1 hfar han hRsmall hp₀
    have hid : (cellCount (bushOf S p₀) (palScale r n a) : ℝ) ^ (2 : ℕ) = B ^ (2 * F a) := by
      rw [show 2 * F a = F a * (2 : ℕ) by norm_num; ring, Real.rpow_mul_natCast hB0.le, hF]
    rw [hid] at hh
    apply hh.trans
    rw [Real.rpow_add hB0]
    exact (mul_le_mul_of_nonneg_right hJcoef (Real.rpow_nonneg hB0.le _)).trans_eq (mul_comm _ _)
  have hIprofile : B ^ (N + F a - e) ≤
      ∑ j ∈ J, ((pinsOf S (fun q => tb a (cls q)) j ∩ Q).card : ℝ) := by
    have hh := H.coarse_incidence_lower hr1 hn han hp₀
    apply le_trans _ hh
    rw [Real.rpow_sub hB0, Real.rpow_add hB0, hN, hF]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hIcoef
  have hsum : (∑ i ∈ Finset.Icc h a, 1 /
      ((cellCount Q (palScale r n i) : ℝ) * cellCount (bushOf S p₀) (palScale r n (a - i)))) =
      ∑ i ∈ Finset.Icc h a, B ^ (-(G i + F (a - i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.rpow_neg hB0.le, Real.rpow_add hB0, hG, hF, one_div]
  have henergy : (∑ j ∈ J, ∑ c ∈ Q.image (cellOf (palScale r n h)),
      ((Columns.cellPins S (fun q => tb a (cls q)) Q (cellOf (palScale r n h)) j c).card : ℝ) ^ 2) ≤
      B ^ (2 * N + F a + 2 * e) * ∑ i ∈ Finset.Icc h a, B ^ (-(G i + F (a - i))) := by
    have hh := H.cell_energy_count hr1 hn hha han hRsmall hp₀
    change _ ≤ _ * ∑ i ∈ Finset.Icc h a, 1 /
      ((cellCount Q (palScale r n i) : ℝ) * cellCount (bushOf S p₀) (palScale r n (a - i))) at hh
    rw [hsum] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _
      (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg hB0.le _))
    have hid : (Q.card : ℝ) ^ (2 : ℕ) * cellCount (bushOf S p₀) (palScale r n a) =
        B ^ (2 * N + F a) := by
      rw [Real.rpow_add hB0, show 2 * N = N * (2 : ℕ) by norm_num; ring,
        Real.rpow_mul_natCast hB0.le, hN, hF]
    calc
      _ = (4829760000000 * B ^ (2 : ℕ) * r ^ (-4 * ε)) * B ^ (2 * N + F a) := by
        rw [← hid]
        ring
      _ ≤ B ^ e * B ^ (2 * N + F a) :=
        mul_le_mul_of_nonneg_right hUcoef (Real.rpow_nonneg hB0.le _)
      _ = B ^ (2 * N + F a + e) := by rw [← Real.rpow_add hB0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB.le (by linarith)
  obtain ⟨t, ht, -, hdense⟩ := Columns.dense_cell_tube_of_profiles
    S J (fun q => tb a (cls q)) Q (cellOf (palScale r n h)) (tb h) F G hha hB hW hE
    (by
      intro t ht
      exact Columns.tube_mass_le_of_cell_bound S (fun q => tb a (cls q)) Q
        (cellOf (palScale r n h)) J (tb h) t
        (fun c _ => H.cell_tube_incidence_le hr1 hn hha han hRsmall hp₀ c t))
    hsecond hWprofile hEprofile hJprofile hIprofile henergy hpalette
    (fun i hi => hright i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
    (by have := (abs_le.mp (hunif a han)).2; linarith)
    (by have := (abs_le.mp (hunif h (hha.trans han))).1; linarith)
    (fun i hi => by
      have hia := (Finset.mem_Icc.mp hi).2
      have := (abs_le.mp (hunif (a - i) ((Nat.sub_le a i).trans han))).1
      linarith)
  exact ⟨t, ht, hdense⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/High/WindowCells.lean
