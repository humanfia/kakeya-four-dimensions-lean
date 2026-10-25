import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.BlockFit
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.RowFit

/-!
# From the first-jet data to the block-fit hypotheses

`FirstJet.Data ν y β γ E F d K ζ` (x0854's statement of the first-jet input: static `y`,
affine scalar `β + t γ`, time-only row `F`) gives `JetHyp (ofData ν y β γ E F) ζ (10 K³) d`,
the hypotheses of `block_fit` (the coefficient-bin caps are not needed there). The only
non-trivial field is the local count: the support count of `Data` (cells of width `q` in windows
of length `r ≤ 1`) gives covers by balls; windows longer than `1` are handled with the bound
`|S| ≤ 4K²` of the labeled scalars and at most `8K² + 1` unit windows.
-/

open MeasureTheory Set Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first-jet data as a `JetData`. -/
def ofData (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) : JetData Ω where
  ν := ν
  E := E
  x0 := β
  x1 := γ
  y := y
  F := F

theorem ofData_S (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    (ofData ν y β γ E F).S l t = FirstJet.scal y β γ F l t := rfl

theorem ofData_xb (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    (ofData ν y β γ E F).xb l t = FirstJet.xbar β γ l t := rfl

/-- Cells of width `q ≤ 2s` give a cover by closed `s`-balls, one for each cell. -/
theorem cover_of_cells {X : Set ℝ} {C : Finset ℤ} {q s : ℝ} (hq : 0 < q) (hqs : q ≤ 2 * s)
    (hX : ∀ x ∈ X, ⌊x / q⌋ ∈ C) :
    ∃ cc : Fin C.card → ℝ, X ⊆ ⋃ j, closedBall (cc j) s := by
  refine ⟨fun j => ((C.equivFin.symm j : ℤ) : ℝ) * q + q / 2, ?_⟩
  intro x hx
  have hc := hX x hx
  rw [Set.mem_iUnion]
  refine ⟨C.equivFin ⟨_, hc⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [mem_closedBall, Real.dist_eq]
  have h1 := Int.floor_le (x / q)
  have h2 := Int.lt_floor_add_one (x / q)
  have e1 : (⌊x / q⌋ : ℝ) * q ≤ x := by rwa [le_div_iff₀ hq] at h1
  have e2 : x < ((⌊x / q⌋ : ℝ) + 1) * q := by rwa [div_lt_iff₀ hq] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- The labeled scalars are bounded by `4K²`. -/
theorem abs_scal_le {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : FirstJet.Data ν y β γ E F d K ζ) (hK : 1 ≤ K)
    {l : Ω} {t : ℝ} (hl : (l, t) ∈ E) : |FirstJet.scal y β γ F l t| ≤ 4 * K ^ 2 := by
  have ht := (h.subset_E hl).2
  have hβ := h.bound_β l
  have hγ := h.bound_γ l
  have hy0 := h.bound_y l 0
  have hy1 := h.bound_y l 1
  have hF0 := h.bound_F t 0
  have hF1 := h.bound_F t 1
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1 : |t * γ l| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht0]
    calc t * |γ l| ≤ 1 * |γ l| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ ≤ K := by linarith
  have h2 : |F t 0 * y l 0| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul hF0 hy0 (abs_nonneg _) (by linarith)
  have h3 : |F t 1 * y l 1| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul hF1 hy1 (abs_nonneg _) (by linarith)
  unfold FirstJet.scal FirstJet.xbar
  calc |β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1)|
      ≤ |β l| + |t * γ l| + (|F t 0 * y l 0| + |F t 1 * y l 1|) := by
        have := abs_sub (β l + t * γ l) (F t 0 * y l 0 + F t 1 * y l 1)
        have := abs_add_le (β l) (t * γ l)
        have := abs_add_le (F t 0 * y l 0) (F t 1 * y l 1)
        linarith
    _ ≤ 4 * K ^ 2 := by nlinarith

theorem two_mul_le_ten_mul_cube {K : ℝ} (hK : 1 ≤ K) : 2 * K ≤ 10 * K ^ 3 := by
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hK2 (by linarith : (0:ℝ) ≤ K)]

theorem le_ten_mul_cube {K : ℝ} (hK : 1 ≤ K) : K ≤ 10 * K ^ 3 := by
  have := two_mul_le_ten_mul_cube hK; linarith

/-- The support count of the first-jet data gives the local count of `JetHyp`. -/
theorem supp_of_data {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : FirstJet.Data ν y β γ E F d K ζ) (hK : 1 ≤ K)
    (hd : 0 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (t : ℝ) :
    LocalCount {s | ∃ l, (l, t) ∈ (ofData ν y β γ E F).E ∧ s = (ofData ν y β γ E F).S l t}
      ζ (10 * K ^ 3) d := by
  intro a L s hζs hsL
  have hs : 0 < s := hζ.trans_le hζs
  have hLs : 0 ≤ L / s := div_nonneg (hs.le.trans hsL) hs.le
  have hK3 : K ≤ 10 * K ^ 3 := le_ten_mul_cube hK
  by_cases hL1 : L ≤ 1
  · obtain ⟨C, hC, hmem⟩ := h.support t s L a hζs hsL hL1
    obtain ⟨cc, hcc⟩ := cover_of_cells (X := {s' | ∃ l, (l, t) ∈ (ofData ν y β γ E F).E ∧
        s' = (ofData ν y β γ E F).S l t} ∩ Icc a (a + L)) (q := s) (s := s) hs (by linarith) (fun x hx => by
      obtain ⟨⟨l, hl, rfl⟩, hx1, hx2⟩ := hx
      exact hmem l hl hx1 hx2)
    refine ⟨C.card, cc, hcc, ?_⟩
    have : 0 ≤ (L / s) ^ d := Real.rpow_nonneg hLs d
    exact hC.trans (mul_le_mul_of_nonneg_right hK3 this)
  · push Not at hL1
    set q : ℝ := min s 1 with hq_def
    have hq : 0 < q := lt_min hs one_pos
    have hζq : ζ ≤ q := le_min hζs hζ1
    have hq1 : q ≤ 1 := min_le_right _ _
    have hqs : q ≤ s := min_le_left _ _
    set M : ℕ := ⌈8 * K ^ 2⌉₊ with hM_def
    have hwin : ∀ k : ℕ, ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (1 / q) ^ d ∧
        ∀ l, (l, t) ∈ E → (-(4 * K ^ 2) + k) ≤ FirstJet.scal y β γ F l t →
          FirstJet.scal y β γ F l t ≤ (-(4 * K ^ 2) + k) + 1 →
          ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C :=
      fun k => h.support t q 1 _ hζq hq1 le_rfl
    choose C hC hCmem using hwin
    set C' : Finset ℤ := (Finset.range (M + 1)).biUnion C with hC'_def
    have hcard : (C'.card : ℝ) ≤ (M + 1) * (K * (1 / q) ^ d) := by
      have h1 : C'.card ≤ ∑ k ∈ Finset.range (M + 1), (C k).card := Finset.card_biUnion_le
      have h2 : (∑ k ∈ Finset.range (M + 1), ((C k).card : ℝ)) ≤
          ∑ _k ∈ Finset.range (M + 1), K * (1 / q) ^ d := Finset.sum_le_sum (fun k _ => hC k)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
      calc (C'.card : ℝ) ≤ ((∑ k ∈ Finset.range (M + 1), (C k).card : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ = ∑ k ∈ Finset.range (M + 1), ((C k).card : ℝ) := by push_cast; rfl
        _ ≤ ((M + 1 : ℕ) : ℝ) * (K * (1 / q) ^ d) := h2
        _ = (M + 1) * (K * (1 / q) ^ d) := by push_cast; ring
    have hmemC : ∀ x ∈ {s' | ∃ l, (l, t) ∈ (ofData ν y β γ E F).E ∧
        s' = (ofData ν y β γ E F).S l t} ∩ Icc a (a + L), ⌊x / q⌋ ∈ C' := by
      rintro x ⟨⟨l, hl, rfl⟩, -⟩
      have hb := abs_scal_le h hK (l := l) (t := t) hl
      rw [ofData_S]
      set x := FirstJet.scal y β γ F l t
      have hx := abs_le.1 hb
      set k : ℕ := ⌊x + 4 * K ^ 2⌋₊ with hk_def
      have hk0 : 0 ≤ x + 4 * K ^ 2 := by linarith
      have hk1 : (k : ℝ) ≤ x + 4 * K ^ 2 := Nat.floor_le hk0
      have hk2 : x + 4 * K ^ 2 < k + 1 := Nat.lt_floor_add_one _
      have hkM : k < M + 1 := by
        have : (k : ℝ) ≤ 8 * K ^ 2 := by linarith
        have hM : 8 * K ^ 2 ≤ (M : ℝ) := Nat.le_ceil _
        have : (k : ℝ) < (M : ℝ) + 1 := by linarith
        exact_mod_cast this
      rw [hC'_def, Finset.mem_biUnion]
      exact ⟨k, Finset.mem_range.2 hkM, hCmem k l hl (by linarith) (by linarith)⟩
    obtain ⟨cc, hcc⟩ := cover_of_cells (s := s) hq (by linarith) hmemC
    refine ⟨C'.card, cc, hcc, ?_⟩
    have hM : (M : ℝ) ≤ 8 * K ^ 2 + 1 := by
      have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 8 * K ^ 2 by positivity)
      rw [← hM_def] at this; linarith
    have hqL : 1 / q ≤ L / s := by
      rcases le_total s 1 with hs1 | hs1
      · have : q = s := min_eq_left hs1
        rw [this]; exact div_le_div_of_nonneg_right hL1.le hs.le
      · have : q = 1 := min_eq_right hs1
        rw [this, div_one, le_div_iff₀ hs]; linarith
    have hpow : (1 / q) ^ d ≤ (L / s) ^ d :=
      Real.rpow_le_rpow (by positivity) hqL hd
    have hp0 : 0 ≤ (1 / q) ^ d := Real.rpow_nonneg (by positivity) d
    calc (C'.card : ℝ) ≤ (M + 1) * (K * (1 / q) ^ d) := hcard
      _ ≤ (8 * K ^ 2 + 2) * (K * (L / s) ^ d) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hpow (by linarith))
            (by positivity) (by positivity)
      _ = ((8 * K ^ 2 + 2) * K) * (L / s) ^ d := by ring
      _ ≤ 10 * K ^ 3 * (L / s) ^ d := by
          have : 0 ≤ (L / s) ^ d := Real.rpow_nonneg hLs d
          have h2 := two_mul_le_ten_mul_cube hK
          have : (8 * K ^ 2 + 2) * K ≤ 10 * K ^ 3 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hLs d)

theorem vec3_eq_iff {a b c : ℤ} {m : Fin 3 → ℤ} :
    (![a, b, c] = m) ↔ (a = m 0 ∧ b = m 1 ∧ c = m 2) := by
  constructor
  · intro h; subst h; simp
  · rintro ⟨h0, h1, h2⟩; ext k; fin_cases k <;> simp [h0, h1, h2]

/-- **The bridge**: the first-jet data give the block-fit hypotheses with constant `10 K³`. -/
theorem jetHyp_of_data {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : FirstJet.Data ν y β γ E F d K ζ) (hK : 1 ≤ K) (hd : 0 ≤ d) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) : JetHyp (ofData ν y β γ E F) ζ (10 * K ^ 3) d where
  prob := by change IsProbabilityMeasure ν; infer_instance
  measE := h.measurableSet_E
  E01 := fun q hq => (h.subset_E hq).2
  meas_x0 := h.measurable_β
  meas_x1 := h.measurable_γ
  meas_y := fun i => (measurable_pi_apply i).comp h.measurable_y
  meas_F := fun i => (measurable_pi_apply i).comp h.measurable_F
  bound_x := fun l => by
    have := h.bound_β l; have := h.bound_γ l
    change |β l| + |γ l| ≤ 10 * K ^ 3
    have := two_mul_le_ten_mul_cube hK
    linarith
  bound_y := fun l i => by
    have := h.bound_y l i
    change |y l i| ≤ 10 * K ^ 3
    have := le_ten_mul_cube hK
    linarith
  bound_F := fun t i => by
    have := h.bound_F t i
    change |F t i| ≤ 10 * K ^ 3
    have := le_ten_mul_cube hK
    linarith
  supp := fun t => supp_of_data h hK hd hζ hζ1 t
  abscap := fun t q hζq hq1 m => by
    have e : {l | (l, t) ∈ (ofData ν y β γ E F).E ∧ (ofData ν y β γ E F).cube q l t = m} =
        {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = m 0 ∧ ⌊y l 0 / q⌋ = m 1 ∧
          ⌊y l 1 / q⌋ = m 2} := by
      ext l
      simp only [Set.mem_setOf_eq, JetData.cube, vec3_eq_iff]
      rfl
    rw [e]
    refine (h.absCap t q hζq hq1 m).trans (ENNReal.ofReal_le_ofReal ?_)
    have hq : 0 < q := hζ.trans_le hζq
    exact mul_le_mul_of_nonneg_right (le_ten_mul_cube hK) (Real.rpow_nonneg hq.le _)
  rowcomp := fun l t l' u hl hl' i => by
    have := h.rowLip t u ⟨l, hl⟩ ⟨l', hl'⟩ i
    have hζ0 : 0 ≤ |t - u| + ζ := by positivity
    change |F t i - F u i| ≤ 10 * K ^ 3 * (|t - u| + ζ)
    exact this.trans (mul_le_mul_of_nonneg_right (le_ten_mul_cube hK) hζ0)
  rescomp := fun l t l' u hl hl' => by
    have := h.slopeLip l l' t u hl hl'
    have hζ0 : 0 ≤ |t - u| + |FirstJet.xbar β γ l t - FirstJet.xbar β γ l' u| +
      |y l 0 - y l' 0| + |y l 1 - y l' 1| + ζ := by positivity
    change |γ l - γ l'| ≤ 10 * K ^ 3 * (|t - u| + |FirstJet.xbar β γ l t -
      FirstJet.xbar β γ l' u| + |y l 0 - y l' 0| + |y l 1 - y l' 1| + ζ)
    exact this.trans (mul_le_mul_of_nonneg_right (le_ten_mul_cube hK) hζ0)
  mass := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h.mass
    rw [one_div]
    exact inv_anti₀ (by positivity) (le_ten_mul_cube hK)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
