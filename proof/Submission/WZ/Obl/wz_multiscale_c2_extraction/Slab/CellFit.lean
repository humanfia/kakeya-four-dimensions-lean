-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.CellFit.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Cells

/-!
# One cell of height `√ρ`

The full grid rows of a cell `[j √ρ, (j + 1) √ρ)` are covered by at most `3 √ρ / √s` windows of
`L = ⌊1/√s⌋` rows. If the best window is heavy (mass at least `√s M / 60`), the window lemma
gives an affine fit on rows carrying `s ^ εl √s / (12 √ρ)` of the mass of the cell's full rows;
otherwise the full rows of the cell carry at most `√ρ M / 20`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

/-- The number of rows of the windows. -/
noncomputable def winLen (s : ℝ) : ℕ := ⌊1 / Real.sqrt s⌋₊

lemma winLen_spec {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 4) :
    1 ≤ winLen s ∧ (winLen s : ℝ) * s ≤ Real.sqrt s ∧ 1 / (2 * Real.sqrt s) ≤ winLen s := by
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hs2 : Real.sqrt s ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs1
  have h2 : (2 : ℝ) ≤ 1 / Real.sqrt s := by rw [le_div_iff₀ hsp]; linarith
  have hfl := Nat.floor_le (show 0 ≤ 1 / Real.sqrt s by positivity)
  have hfl2 := Nat.lt_floor_add_one (1 / Real.sqrt s)
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ ⌊1 / Real.sqrt s⌋₊ := by linarith
    exact_mod_cast this
  · unfold winLen
    calc (⌊1 / Real.sqrt s⌋₊ : ℝ) * s ≤ 1 / Real.sqrt s * s := by gcongr
      _ = Real.sqrt s := by field_simp; linarith
  · unfold winLen
    have : 1 / (2 * Real.sqrt s) = (1 / Real.sqrt s) / 2 := by field_simp
    rw [this]; linarith

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

/-- The first and last full rows of a cell. -/
noncomputable def cellLo (s rt : ℝ) (j : ℤ) : ℤ := ⌈j * rt / s⌉
noncomputable def cellHi (s rt : ℝ) (j : ℤ) : ℤ := ⌊(j + 1) * rt / s⌋

lemma cell_rows {s rt : ℝ} (hs : 0 < s) (j : ℤ) :
    j * rt ≤ s * cellLo s rt j ∧ s * cellLo s rt j < j * rt + s ∧
      s * cellHi s rt j ≤ (j + 1) * rt ∧ (j + 1) * rt < s * cellHi s rt j + s := by
  unfold cellLo cellHi
  have h1 := Int.le_ceil (j * rt / s)
  have h2 := Int.ceil_lt_add_one (j * rt / s)
  have h3 := Int.floor_le ((j + 1) * rt / s)
  have h4 := Int.lt_floor_add_one ((j + 1) * rt / s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs] at h1; rw [mul_comm s]; exact h1
  · have := mul_lt_mul_of_pos_left h2 hs
    rw [mul_add, mul_div_cancel₀ _ hs.ne', mul_one] at this; exact this
  · rw [le_div_iff₀ hs] at h3; rw [mul_comm s]; exact h3
  · have := mul_lt_mul_of_pos_left h4 hs
    rw [mul_div_cancel₀ _ hs.ne', mul_add, mul_one] at this; exact this

/-- One cell: a fit on heavy cells, a mass bound on light ones. -/
theorem cell_fit (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    {εl ηl ρ₀ : ℝ} (hspec : SlabSpec σ εl ηl ρ₀) (hsρ : s ≤ ρ₀)
    (hs8 : 8 * s ≤ s ^ ((1 : ℝ) / 2 + εl))
    (hK : 162 * K ≤ s ^ (-ηl)) (hθη : s ^ ηl ≤ (θ - δ) / 2 - 8 * s)
    (hN : 0 < N) (hn : 0 < n) {rt M : ℝ} (hM : 0 ≤ M)
    (hrt : 2 * Real.sqrt s ≤ rt) (hrt1 : rt ≤ 1)
    (hheavy : ∀ Mw : ℝ, Real.sqrt s * M / 60 ≤ Mw → s ^ (1 + σ / 2 + ηl) ≤
      9 * s * θ ^ 4 * Mw ^ 2 / (16 * 2304 * N * δ ^ 4 *
        pieceBound σ δ s θ K ((winLen s : ℝ) * s) * winLen s * n))
    (j : ℤ) (hj1 : -1 ≤ j * rt) (hj2 : (j + 2) * rt ≤ 1) (hj3 : 3 ≤ j ∨ j ≤ -4) :
    ∃ (a b : ℝ) (G : Finset ℤ), G ⊆ Finset.Ico (cellLo s rt j) (cellHi s rt j) ∧
      (∀ m ∈ G, ∀ z ∈ row s m, |f z - (a + b * z)| ≤ 4 * s) ∧
      (ENNReal.ofReal (s ^ εl * Real.sqrt s / (12 * rt)) *
          heightMass Y (rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j))) ≤
            heightMass Y (rowUnion s G) ∨
        heightMass Y (rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j))) ≤
          ENNReal.ofReal (rt * M / 20)) := by
  classical
  have hs := s_pos hS
  have hb := sqrt_s_bounds hS
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hs14 : s ≤ 1 / 4 := hS.s_small.trans (by norm_num)
  have hrtpos : 0 < rt := by linarith
  obtain ⟨hL1, hLs, hL2⟩ := winLen_spec hs hs14
  set L := winLen s with hLdef
  set a := cellLo s rt j
  set b := cellHi s rt j
  obtain ⟨ha1, ha2, hb1, hb2⟩ := cell_rows (rt := rt) hs j
  have hYb : ∀ i, Y i ⊆ ball (0 : Space) 1 := fun i => (hS.sub_Eo i).trans hS.Eo_ball
  -- the cell holds at least one window
  have hba_r : rt - 2 * s < s * ((b : ℝ) - a) := by nlinarith
  have hba_u : s * ((b : ℝ) - a) ≤ rt := by nlinarith
  have hLba : (L : ℤ) ≤ b - a := by
    have h1 : (L : ℝ) * s ≤ Real.sqrt s := hLs
    have h2 : 2 * s ≤ Real.sqrt s := by nlinarith
    have h3 : (L : ℝ) * s < s * ((b : ℝ) - a) := by linarith
    have h4 : (L : ℝ) < (b : ℝ) - a := by nlinarith
    have : (L : ℝ) ≤ ((b - a : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨m₀, hm₀, hbest⟩ := exists_best_window hS.meas hs hL1 hLba
  obtain ⟨hm₀a, hm₀b⟩ := windowStarts_sub hL1 hLba m₀ hm₀
  -- the number of windows
  have hstarts : ((windowStarts a b L).card : ℝ) ≤ 3 * rt / Real.sqrt s := by
    have h1 := windowStarts_card_le a b L
    have hba0 : (0 : ℤ) ≤ b - a := le_trans (Int.natCast_nonneg L) hLba
    have h2 : (((b - a).toNat / L : ℕ) : ℝ) ≤ ((b - a).toNat : ℝ) / L := Nat.cast_div_le
    have h3 : (((b - a).toNat : ℕ) : ℝ) = (b : ℝ) - a := by
      have := Int.toNat_of_nonneg hba0
      exact_mod_cast this
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have h4 : ((b : ℝ) - a) / L ≤ 2 * rt / Real.sqrt s := by
      rw [div_le_iff₀ hLpos]
      have : (b : ℝ) - a ≤ rt / s := by rw [le_div_iff₀ hs]; linarith
      have e : 2 * rt / Real.sqrt s * (1 / (2 * Real.sqrt s)) = rt / (Real.sqrt s * Real.sqrt s) := by
        field_simp
      rw [hsq] at e
      have hrt0 : 0 ≤ rt := by linarith
      calc (b : ℝ) - a ≤ rt / s := this
        _ = 2 * rt / Real.sqrt s * (1 / (2 * Real.sqrt s)) := e.symm
        _ ≤ 2 * rt / Real.sqrt s * L := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h5 : (1 : ℝ) ≤ rt / Real.sqrt s := by rw [le_div_iff₀ hsp]; linarith
    calc ((windowStarts a b L).card : ℝ) ≤ (((b - a).toNat / L : ℕ) : ℝ) + 1 := by
          exact_mod_cast h1
      _ ≤ ((b : ℝ) - a) / L + 1 := by rw [← h3]; linarith
      _ ≤ 2 * rt / Real.sqrt s + 1 := by linarith
      _ ≤ 3 * rt / Real.sqrt s := by
          have : 2 * rt / Real.sqrt s + 1 ≤ 2 * rt / Real.sqrt s + rt / Real.sqrt s := by linarith
          calc _ ≤ 2 * rt / Real.sqrt s + rt / Real.sqrt s := this
            _ = 3 * rt / Real.sqrt s := by ring
  -- window rows lie in the cell
  have hwin_rows : ∀ m ∈ Finset.Ico m₀ (m₀ + L), ∀ z ∈ row s m,
      (j : ℝ) * rt ≤ z ∧ z < (j + 1) * rt := by
    intro m hm z hz
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    have e1 : (a : ℝ) ≤ m := by exact_mod_cast hm₀a.trans hm1
    have e2 : (m : ℝ) + 1 ≤ b := by
      have : m + 1 ≤ b := by omega
      exact_mod_cast this
    obtain ⟨hz1, hz2⟩ := hz
    have f1 : s * (a : ℝ) ≤ s * m := mul_le_mul_of_nonneg_left e1 hs.le
    have f2 : s * ((m : ℝ) + 1) ≤ s * b := mul_le_mul_of_nonneg_left e2 hs.le
    constructor
    · linarith
    · linarith
  have hfar : ∀ m ∈ Finset.Ico m₀ (m₀ + L), ∀ z ∈ row s m, 2 * Real.sqrt s ≤ |z| := by
    intro m hm z hz
    obtain ⟨h1, h2⟩ := hwin_rows m hm z hz
    have hrt0 : 0 ≤ rt := by linarith
    rcases hj3 with hj | hj
    · have h3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
      have h4 : 3 * rt ≤ j * rt := mul_le_mul_of_nonneg_right h3 hrt0
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h3 : (j : ℝ) + 1 ≤ -3 := by
        have : (j : ℝ) ≤ -4 := by exact_mod_cast hj
        linarith
      have h4 : ((j : ℝ) + 1) * rt ≤ -3 * rt := mul_le_mul_of_nonneg_right h3 hrt0
      rw [abs_of_neg (by linarith)]; linarith
  have hpos1 : -1 ≤ s * m₀ := by
    have h1 : (a : ℝ) ≤ m₀ := by exact_mod_cast hm₀a
    have h2 : s * (a : ℝ) ≤ s * m₀ := mul_le_mul_of_nonneg_left h1 hs.le
    linarith
  have hpos2 : s * m₀ + Real.sqrt s ≤ 1 := by
    have h1 : (m₀ : ℝ) ≤ b := by
      have : (m₀ : ℝ) + L ≤ b := by exact_mod_cast hm₀b
      have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      linarith
    have h2 : s * (m₀ : ℝ) ≤ s * b := mul_le_mul_of_nonneg_left h1 hs.le
    have h3 : ((j : ℝ) + 2) * rt = (j + 1) * rt + rt := by ring
    linarith
  set Mw := (heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L)))).toReal with hMw
  have hMwfin : heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L))) = ENNReal.ofReal Mw := by
    rw [hMw, ENNReal.ofReal_toReal (heightMass_ne_top hYb _)]
  have hsub : Finset.Ico m₀ (m₀ + L) ⊆ Finset.Ico a b := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    exact Finset.mem_Ico.mpr ⟨hm₀a.trans hm1, by omega⟩
  by_cases hhv : Real.sqrt s * M / 60 ≤ Mw
  · -- heavy window
    obtain ⟨a', b', G, hG, hfit, hmass⟩ := window_fit hS hspec hsρ hs8 hK hθη hN hn m₀ L hL1 hLs
      hpos1 hpos2 hfar (hheavy Mw hhv)
    refine ⟨a', b', G, hG.trans hsub, hfit, Or.inl ?_⟩
    refine le_trans ?_ hmass
    calc ENNReal.ofReal (s ^ εl * Real.sqrt s / (12 * rt)) *
          heightMass Y (rowUnion s (Finset.Ico a b))
        ≤ ENNReal.ofReal (s ^ εl * Real.sqrt s / (12 * rt)) *
          (((windowStarts a b L).card : ℝ≥0∞) * ENNReal.ofReal Mw) := by
          gcongr; rw [← hMwfin]; exact hbest
      _ = ENNReal.ofReal (s ^ εl * Real.sqrt s / (12 * rt) *
            ((windowStarts a b L).card * Mw)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (s ^ εl * Mw / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hMw0 : 0 ≤ Mw := ENNReal.toReal_nonneg
          have hspow : 0 ≤ s ^ εl := Real.rpow_nonneg hs.le _
          have hrt0 : 0 < rt := by linarith
          calc s ^ εl * Real.sqrt s / (12 * rt) * ((windowStarts a b L).card * Mw)
              ≤ s ^ εl * Real.sqrt s / (12 * rt) * (3 * rt / Real.sqrt s * Mw) := by
                gcongr
            _ = s ^ εl * Mw / 4 := by field_simp; ring
  · -- light window
    push Not at hhv
    refine ⟨0, 0, ∅, Finset.empty_subset _, fun m hm => absurd hm (Finset.notMem_empty m),
      Or.inr ?_⟩
    calc heightMass Y (rowUnion s (Finset.Ico a b))
        ≤ ((windowStarts a b L).card : ℝ≥0∞) * ENNReal.ofReal Mw := by rw [← hMwfin]; exact hbest
      _ = ENNReal.ofReal ((windowStarts a b L).card * Mw) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (rt * M / 20) := by
          apply ENNReal.ofReal_le_ofReal
          have hMw0 : 0 ≤ Mw := ENNReal.toReal_nonneg
          calc ((windowStarts a b L).card : ℝ) * Mw ≤ 3 * rt / Real.sqrt s * (Real.sqrt s * M / 60) :=
                mul_le_mul hstarts hhv.le hMw0 (by positivity)
            _ = rt * M / 20 := by field_simp; ring

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
