-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/RowShared.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Window

/-!
# The shared-line bound of the row comparison

Paper §9, "Regularizing the scalar-normal input": for active times `|t - u| ≤ r` with
`M = |F(t) - F(u)| ≫ r`, the prior weight of the lines labeled at both times is
`≤ K (r/M)^(1-d)`. Given the scalar `r`-bin `σ` of `S_l(t)` (at most `K r^(-d)` choices by the
global support count), the target `S_l(u)` lies within `K(r + 2M)` of it, hence in at most
`80 K⁴ (M/r)^d` bins `σ'` by the local count at `u` (`LocalCounts.long`); then the signal
equation `S_l(u) - S_l(t) = (u - t) γ_l - (F(u) - F(t)) · y_l` puts `y_l` in a strip of width
`≈ r K / M`, covered by `≈ K/r` slabs of `≈ K/M` squares of side `r`, each of mass
`≲ K² r^(2+d)` (`slab_cap_gen`). In total `61440 K⁹ (r/M)^(1-d)` (`shared_line_bound`, for the
larger of the two row components; `shared_line_bound'` for either one through the coordinate
swap).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The labeled scalars are bounded by `4K²`. -/
theorem abs_scal_le_of_chart {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hK : 1 ≤ K) {l : Ω} {t : ℝ}
    (hl : (l, t) ∈ E) : |FirstJet.scal y β γ F l t| ≤ 4 * K ^ 2 := by
  have ht := (hU.subset_E hl).2
  have hβ := hU.bound_β l
  have hγ := hU.bound_γ l
  have hy0 := hU.bound_y l 0
  have hy1 := hU.bound_y l 1
  have hF0 := hU.bound_F t 0
  have hF1 := hU.bound_F t 1
  have h1 : |t * γ l| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht.1]
    calc t * |γ l| ≤ 1 * |γ l| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
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

/-- Local counts in windows of any length `L ≥ q` (`q ≤ 1`), with constant `10 K³`. -/
theorem LocalCounts.long {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hL : LocalCounts y β γ E F d K ζ)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d) (t q L a : ℝ) (hq : ζ ≤ q) (hq1 : q ≤ 1)
    (hqL : q ≤ L) :
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ 10 * K ^ 3 * (L / q) ^ d ∧
      ∀ l, (l, t) ∈ E → a ≤ FirstJet.scal y β γ F l t → FirstJet.scal y β γ F l t ≤ a + L →
        ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C := by
  classical
  have hq0 : 0 < q := hζ.trans_le hq
  have hLq : 0 ≤ L / q := div_nonneg (hq0.le.trans hqL) hq0.le
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hK3 : K ≤ 10 * K ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hK2 (by linarith : (0:ℝ) ≤ K)]
  by_cases hL1 : L ≤ 1
  · obtain ⟨C, hC, hmem⟩ := hL t q L a hq hqL hL1
    exact ⟨C, hC.trans (mul_le_mul_of_nonneg_right hK3 (Real.rpow_nonneg hLq _)), hmem⟩
  · push Not at hL1
    set M : ℕ := ⌈8 * K ^ 2⌉₊ with hM_def
    have hwin : ∀ k : ℕ, ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (1 / q) ^ d ∧
        ∀ l, (l, t) ∈ E → (-(4 * K ^ 2) + k) ≤ FirstJet.scal y β γ F l t →
          FirstJet.scal y β γ F l t ≤ (-(4 * K ^ 2) + k) + 1 →
          ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C :=
      fun k => hL t q 1 _ hq hq1 le_rfl
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
    refine ⟨C', ?_, ?_⟩
    · have hM : (M : ℝ) ≤ 8 * K ^ 2 + 1 := by
        have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 8 * K ^ 2 by positivity)
        rw [← hM_def] at this; linarith
      have hqL' : 1 / q ≤ L / q := div_le_div_of_nonneg_right hL1.le hq0.le
      have hpow : (1 / q) ^ d ≤ (L / q) ^ d := Real.rpow_le_rpow (by positivity) hqL' hd
      have hLd : 0 ≤ (L / q) ^ d := Real.rpow_nonneg hLq d
      calc (C'.card : ℝ) ≤ (M + 1) * (K * (1 / q) ^ d) := hcard
        _ ≤ (8 * K ^ 2 + 2) * (K * (L / q) ^ d) := by
            apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hpow (by linarith))
              (by positivity) (by positivity)
        _ = ((8 * K ^ 2 + 2) * K) * (L / q) ^ d := by ring
        _ ≤ 10 * K ^ 3 * (L / q) ^ d := by
            apply mul_le_mul_of_nonneg_right _ hLd
            nlinarith [mul_le_mul_of_nonneg_left hK2 (by linarith : (0:ℝ) ≤ K)]
    · intro l hl _ _
      have hb := abs_scal_le_of_chart hU hK hl
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

set_option maxHeartbeats 4000000 in
/-- **The shared-line bound** (larger row component first). -/
theorem shared_line_bound {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hL : LocalCounts y β γ E F d K ζ)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (t u r : ℝ) (hr : ζ ≤ r)
    (hr1 : r ≤ 1) (htu : |u - t| ≤ r) (hM : r ≤ |F u 0 - F t 0|)
    (h10 : |F u 1 - F t 1| ≤ |F u 0 - F t 0|) :
    ν {l | (l, t) ∈ E ∧ (l, u) ∈ E} ≤
      ENNReal.ofReal (61440 * K ^ 9 * (r / |F u 0 - F t 0|) ^ (1 - d)) := by
  classical
  have hr0 : 0 < r := hζ.trans_le hr
  set M := |F u 0 - F t 0| with hM_def
  have hM0 : 0 < M := hr0.trans_le hM
  have hMK : M ≤ 2 * K := by
    have h1 := hU.bound_F u 0; have h2 := hU.bound_F t 0
    calc M ≤ |F u 0| + |F t 0| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  have hΔ0 : F u 0 - F t 0 ≠ 0 := by
    intro h; rw [hM_def, h, abs_zero] at hM0; exact lt_irrefl _ hM0
  set Δ0 := F u 0 - F t 0 with hΔ0_def
  set Δ1 := F u 1 - F t 1 with hΔ1_def
  -- the source bins
  obtain ⟨Cs, hCs, hCsmem⟩ := hU.support t r hr hr1
  -- the target bins
  set L : ℝ := r + K * (r + 2 * M) with hL_def
  have hrL : r ≤ L := by
    have : 0 ≤ K * (r + 2 * M) := by positivity
    linarith
  have htarget : ∀ σ : ℤ, ∃ T : Finset ℤ, (T.card : ℝ) ≤ 10 * K ^ 3 * ((L + L) / r) ^ d ∧
      ∀ l, (l, u) ∈ E → σ * r - K * (r + 2 * M) ≤ FirstJet.scal y β γ F l u →
        FirstJet.scal y β γ F l u ≤ σ * r - K * (r + 2 * M) + (L + L) →
        ⌊FirstJet.scal y β γ F l u / r⌋ ∈ T :=
    fun σ => hL.long hU hK hζ hd u r (L + L) _ hr hr1 (by linarith)
  choose T hT hTmem using htarget
  -- the second coordinate bins
  set B : Finset ℤ := Finset.Icc ⌊-K / r⌋ ⌊K / r⌋ with hB_def
  -- the slab of `(σ, σ', b)`
  set h : ℝ := r * ((K + 1) / M + 1) with hh_def
  set n₀ : ℕ := ⌈2 * h / r⌉₊ with hn₀_def
  set c₀ : ℤ → ℤ → ℤ → ℝ := fun σ σ' b => ((σ - σ') * r - Δ1 * (b * r)) / Δ0 with hc₀_def
  set X : ℤ → ℤ → ℤ → Set Ω := fun σ σ' b =>
    {l | (l, t) ∈ E ∧ c₀ σ σ' b - h ≤ y l 0 ∧ y l 0 ≤ c₀ σ σ' b - h + n₀ * r ∧
      (b : ℝ) * r ≤ y l 1 ∧ y l 1 ≤ (b : ℝ) * r + (1 : ℕ) * r ∧
      (σ : ℝ) * r ≤ FirstJet.scal y β γ F l t ∧
      FirstJet.scal y β γ F l t ≤ (σ : ℝ) * r + (1 : ℕ) * r} with hX_def
  -- covering
  have hcover : {l | (l, t) ∈ E ∧ (l, u) ∈ E} ⊆
      ⋃ σ ∈ Cs, ⋃ σ' ∈ T σ, ⋃ b ∈ B, X σ σ' b := by
    rintro l ⟨hlt, hlu⟩
    set st := FirstJet.scal y β γ F l t
    set su := FirstJet.scal y β γ F l u
    set σ := ⌊st / r⌋
    set σ' := ⌊su / r⌋
    set b := ⌊y l 1 / r⌋
    have f1 := Int.floor_le (st / r); have f2 := Int.lt_floor_add_one (st / r)
    have g1 := Int.floor_le (su / r); have g2 := Int.lt_floor_add_one (su / r)
    have k1 := Int.floor_le (y l 1 / r); have k2 := Int.lt_floor_add_one (y l 1 / r)
    rw [le_div_iff₀ hr0] at f1 g1 k1
    rw [div_lt_iff₀ hr0] at f2 g2 k2
    -- the signal equation
    have hsig : su - st = (u - t) * γ l - (Δ0 * y l 0 + Δ1 * y l 1) := by
      simp only [su, st, FirstJet.scal, FirstJet.xbar, hΔ0_def, hΔ1_def]; ring
    have hγ := hU.bound_γ l
    have hy0 := hU.bound_y l 0
    have hy1 := hU.bound_y l 1
    have hut : |(u - t) * γ l| ≤ r * K := by
      rw [abs_mul]; exact mul_le_mul htu hγ (abs_nonneg _) hr0.le
    have hd0 : |Δ0 * y l 0| ≤ M * K := by
      rw [abs_mul]; exact mul_le_mul le_rfl hy0 (abs_nonneg _) hM0.le
    have hd1' : |Δ1 * y l 1| ≤ M * K := by
      rw [abs_mul]; exact mul_le_mul h10 hy1 (abs_nonneg _) hM0.le
    have hdiff : |su - st| ≤ K * (r + 2 * M) := by
      rw [hsig]
      calc |(u - t) * γ l - (Δ0 * y l 0 + Δ1 * y l 1)|
          ≤ |(u - t) * γ l| + (|Δ0 * y l 0| + |Δ1 * y l 1|) := by
            have := abs_sub ((u - t) * γ l) (Δ0 * y l 0 + Δ1 * y l 1)
            have := abs_add_le (Δ0 * y l 0) (Δ1 * y l 1)
            linarith
        _ ≤ r * K + (M * K + M * K) := by linarith
        _ = K * (r + 2 * M) := by ring
    have hdiff' := abs_le.1 hdiff
    have hσ : σ ∈ Cs := hCsmem l hlt
    have hσ' : σ' ∈ T σ := by
      refine hTmem σ l hlu ?_ ?_
      · linarith
      · simp only [hL_def]; linarith
    have hb : b ∈ B := by
      rw [hB_def, Finset.mem_Icc]
      constructor
      · apply Int.floor_le_floor
        rw [div_le_div_iff_of_pos_right hr0]; linarith [(abs_le.1 hy1).1]
      · apply Int.floor_le_floor
        rw [div_le_div_iff_of_pos_right hr0]; linarith [(abs_le.1 hy1).2]
    refine mem_iUnion₂.2 ⟨σ, hσ, mem_iUnion₂.2 ⟨σ', hσ', mem_iUnion₂.2 ⟨b, hb, ?_⟩⟩⟩
    -- the strip
    have hstrip : |y l 0 - c₀ σ σ' b| ≤ h := by
      have he : Δ0 * (y l 0 - c₀ σ σ' b) = (u - t) * γ l - ((su - σ' * r) - (st - σ * r)) -
          Δ1 * (y l 1 - b * r) := by
        simp only [hc₀_def]
        field_simp
        linear_combination hsig
      have hb1 : |Δ1 * (y l 1 - b * r)| ≤ M * r := by
        rw [abs_mul]
        exact mul_le_mul h10 (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hM0.le
      have hss : |(su - σ' * r) - (st - σ * r)| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
      have hbound : |Δ0 * (y l 0 - c₀ σ σ' b)| ≤ r * K + r + M * r := by
        rw [he]
        calc |(u - t) * γ l - ((su - σ' * r) - (st - σ * r)) - Δ1 * (y l 1 - b * r)|
            ≤ |(u - t) * γ l| + |(su - σ' * r) - (st - σ * r)| + |Δ1 * (y l 1 - b * r)| := by
              have := abs_sub ((u - t) * γ l - ((su - σ' * r) - (st - σ * r)))
                (Δ1 * (y l 1 - b * r))
              have := abs_sub ((u - t) * γ l) ((su - σ' * r) - (st - σ * r))
              linarith
          _ ≤ r * K + r + M * r := by linarith
      rw [abs_mul] at hbound
      have : |y l 0 - c₀ σ σ' b| ≤ (r * K + r + M * r) / M := by
        rw [le_div_iff₀ hM0]; linarith [mul_comm M |y l 0 - c₀ σ σ' b|]
      refine this.trans (le_of_eq ?_)
      simp only [hh_def]; field_simp
    have hn₀ : 2 * h ≤ n₀ * r := by
      have := Nat.le_ceil (2 * h / r)
      rwa [div_le_iff₀ hr0] at this
    refine ⟨hlt, by linarith [(abs_le.1 hstrip).1], by linarith [(abs_le.1 hstrip).2], k1,
      by push_cast; linarith, f1, by push_cast; linarith⟩
  -- the slab caps
  set M' : ℕ := ⌈2 * K⌉₊ with hM'_def
  set sb : ℝ := ((n₀ + 1) * (1 + 1) * (1 + 2 * M' + 1) : ℕ) * (K * r ^ (2 + d)) with hsb_def
  have hslab : ∀ σ σ' b, ν (X σ σ' b) ≤ ENNReal.ofReal sb := by
    intro σ σ' b
    have := slab_cap_gen (ν := ν) (y := y) (β := β) (γ := γ) (E := E) (F := F) (d := d)
      (t := t) (by linarith) hr0 (fun i => hU.bound_F t i)
      (fun m => absCap_of_mixedCap hU hζ t r hr hr1 m) (c₀ σ σ' b - h) (b * r) (σ * r)
      n₀ 1 1 (X σ σ' b) (fun l hl => hl)
    refine this.trans (le_of_eq ?_)
    rw [hsb_def, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hsb0 : 0 ≤ sb := by positivity
  -- summing
  have hsum : ν {l | (l, t) ∈ E ∧ (l, u) ∈ E} ≤
      ENNReal.ofReal (Cs.card * ((10 * K ^ 3 * ((L + L) / r) ^ d) * (B.card * sb))) := by
    calc ν {l | (l, t) ∈ E ∧ (l, u) ∈ E}
        ≤ ν (⋃ σ ∈ Cs, ⋃ σ' ∈ T σ, ⋃ b ∈ B, X σ σ' b) := measure_mono hcover
      _ ≤ ∑ σ ∈ Cs, ν (⋃ σ' ∈ T σ, ⋃ b ∈ B, X σ σ' b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ σ ∈ Cs, ∑ σ' ∈ T σ, ν (⋃ b ∈ B, X σ σ' b) :=
          Finset.sum_le_sum (fun σ _ => measure_biUnion_finset_le _ _)
      _ ≤ ∑ σ ∈ Cs, ∑ σ' ∈ T σ, ∑ b ∈ B, ν (X σ σ' b) :=
          Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun σ' _ =>
            measure_biUnion_finset_le _ _))
      _ ≤ ∑ σ ∈ Cs, ∑ σ' ∈ T σ, ∑ b ∈ B, ENNReal.ofReal sb :=
          Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun σ' _ =>
            Finset.sum_le_sum (fun b _ => hslab σ σ' b)))
      _ = ∑ σ ∈ Cs, ENNReal.ofReal ((T σ).card * (B.card * sb)) := by
          apply Finset.sum_congr rfl; intro σ _
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∑ _σ ∈ Cs, ENNReal.ofReal ((10 * K ^ 3 * ((L + L) / r) ^ d) * (B.card * sb)) :=
          Finset.sum_le_sum (fun σ _ => ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (hT σ) (by positivity)))
      _ = ENNReal.ofReal (Cs.card * ((10 * K ^ 3 * ((L + L) / r) ^ d) * (B.card * sb))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
  refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the arithmetic
  have hBcard : (B.card : ℝ) ≤ 4 * K / r := by
    rw [hB_def, Int.card_Icc]
    have e1 := Int.floor_le (K / r)
    have e2 := Int.lt_floor_add_one (-K / r)
    have hKr : 1 ≤ K / r := by rw [le_div_iff₀ hr0]; linarith
    have : ((⌊K / r⌋ + 1 - ⌊-K / r⌋).toNat : ℝ) = (⌊K / r⌋ : ℝ) + 1 - ⌊-K / r⌋ := by
      have hnn : 0 ≤ ⌊K / r⌋ + 1 - ⌊-K / r⌋ := by
        have : ⌊-K / r⌋ ≤ ⌊K / r⌋ := Int.floor_le_floor (div_le_div_of_nonneg_right
          (by linarith) hr0.le)
        omega
      have hc : (((⌊K / r⌋ + 1 - ⌊-K / r⌋).toNat : ℕ) : ℝ) =
          ((⌊K / r⌋ + 1 - ⌊-K / r⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      rw [hc]; push_cast; ring
    rw [this]
    have hneg : -K / r = -(K / r) := by ring
    have h4 : 4 * K / r = 4 * (K / r) := by ring
    linarith
  have hn₀le : (n₀ : ℝ) + 1 ≤ 12 * K / M := by
    have h1 : (n₀ : ℝ) ≤ 2 * h / r + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : 2 * h / r = 2 * ((K + 1) / M + 1) := by simp only [hh_def]; field_simp
    rw [h2] at h1
    have h3 : 2 * ((K + 1) / M + 1) + 2 ≤ 12 * K / M := by
      rw [show 2 * ((K + 1) / M + 1) + 2 = (2 * (K + 1) + 4 * M) / M by field_simp; ring]
      apply div_le_div_of_nonneg_right _ hM0.le
      linarith
    linarith
  have hM'le : (M' : ℝ) ≤ 2 * K + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hsb : sb ≤ (12 * K / M) * 2 * (8 * K) * (K * r ^ (2 + d)) := by
    rw [hsb_def]; push_cast
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul (mul_le_mul hn₀le le_rfl (by norm_num) (by positivity)) (by linarith)
      (by positivity) (by positivity)
  have hLr : (L + L) / r ≤ 8 * K * (M / r) := by
    rw [div_le_iff₀ hr0]
    have : (8 * K * (M / r)) * r = 8 * K * M := by field_simp
    rw [this, hL_def]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ K - 1) hM0.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ K) (by linarith : (0:ℝ) ≤ M - r)]
  have hLd : ((L + L) / r) ^ d ≤ 8 * K * (M / r) ^ d := by
    have h1 : ((L + L) / r) ^ d ≤ (8 * K * (M / r)) ^ d :=
      Real.rpow_le_rpow (by positivity) hLr hd
    rw [Real.mul_rpow (by positivity) (by positivity)] at h1
    have h2 : (8 * K) ^ d ≤ 8 * K := by
      calc (8 * K) ^ d ≤ (8 * K) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hd1
        _ = 8 * K := Real.rpow_one _
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by positivity) _))
  have hCs' : (Cs.card : ℝ) ≤ K * r ^ (-d) := hCs
  have hrd : r ^ (-d) * r ^ d = 1 := by
    rw [← Real.rpow_add hr0]; simp
  have hfinal : (r / M) ^ (1 - d) = (r / M) * (M / r) ^ d := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.div_rpow hr0.le hM0.le,
      Real.div_rpow hM0.le hr0.le]
    have : 0 < r ^ d := Real.rpow_pos_of_pos hr0 _
    have : 0 < M ^ d := Real.rpow_pos_of_pos hM0 _
    field_simp
  have hpow : r ^ (2 + d) = r ^ 2 * r ^ d := by rw [Real.rpow_add hr0, Real.rpow_two]
  have hMrd : 0 ≤ (M / r) ^ d := Real.rpow_nonneg (by positivity) _
  calc (Cs.card : ℝ) * ((10 * K ^ 3 * ((L + L) / r) ^ d) * (B.card * sb))
      ≤ (K * r ^ (-d)) * ((10 * K ^ 3 * (8 * K * (M / r) ^ d)) *
          ((4 * K / r) * ((12 * K / M) * 2 * (8 * K) * (K * r ^ (2 + d))))) := by
        apply mul_le_mul hCs' _ (by positivity) (by positivity)
        apply mul_le_mul (mul_le_mul_of_nonneg_left hLd (by positivity)) _ (by positivity)
          (by positivity)
        exact mul_le_mul hBcard hsb hsb0 (by positivity)
    _ = 61440 * K ^ 9 * ((r / M) * (M / r) ^ d) * (r ^ (-d) * r ^ d) := by
        rw [hpow]; field_simp; ring
    _ = 61440 * K ^ 9 * (r / M) ^ (1 - d) := by rw [hrd, hfinal]; ring

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
