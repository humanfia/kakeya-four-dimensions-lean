-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/Local.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Window

/-!
# Stage 1: local scalar counts

Paper §9 ("At each tested width `w`, discard scalar bins of instantaneous `ν_H`-labeled mass
less than `w^d/K` ... Division by the retained scalar-bin floor gives the local count
`K(r/w)^d`"). At every width `w` of a finite grid `ws` we keep a label `(l, t)` only if the
`w`-bin of its scalar `S_l(t)` carries prior mass `≥ w^d/K'` at time `t` among the labels of
`E` (`floorSet`). By the global support count this deletes at most `K/K'` per width
(`deleted_le`). A retained `w`-bin inside a window of length `r` carries at least the floor,
while all bins of the window carry at most `600 K⁴ r^d` (`window_mass`); hence the local count
`1200 K⁴ K' Λ (r/q)^d` at every width `q ∈ [w, Λ w]` (`floorSet_localCounts`). The floors are
measured in `E`, so the counts persist under any later restriction.
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The prior mass at time `t` of the labels of `E` whose scalar lies in the `w`-bin `j`. -/
def binMass (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) (w t : ℝ) (j : ℤ) : ENNReal :=
  ν {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j}

/-- The labels whose scalar bins pass the floor `τ w` at every tested width `w ∈ ws`. -/
def floorSet (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) (ws : Finset ℝ) (τ : ℝ → ℝ) : Set (Ω × ℝ) :=
  {p | p ∈ E ∧ ∀ w ∈ ws, ENNReal.ofReal (τ w) ≤
    binMass ν y β γ E F w p.2 ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋}

section Meas

variable {ν : Measure Ω} [SFinite ν] {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
  {F : ℝ → Fin 2 → ℝ}

theorem measurableSet_bin (hS : Measurable (fun p : Ω × ℝ => FirstJet.scal y β γ F p.1 p.2))
    (w : ℝ) (j : ℤ) :
    MeasurableSet {p : Ω × ℝ | ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋ = j} :=
  (Int.measurable_floor.comp (hS.div_const w)) (measurableSet_singleton j)

theorem measurable_binMass (hE : MeasurableSet E)
    (hS : Measurable (fun p : Ω × ℝ => FirstJet.scal y β γ F p.1 p.2)) (w : ℝ) (j : ℤ) :
    Measurable (fun t => binMass ν y β γ E F w t j) :=
  measurable_measure_prodMk_right (hE.inter (measurableSet_bin hS w j))

theorem measurableSet_floorSet (hE : MeasurableSet E)
    (hS : Measurable (fun p : Ω × ℝ => FirstJet.scal y β γ F p.1 p.2)) (ws : Finset ℝ)
    (τ : ℝ → ℝ) : MeasurableSet (floorSet ν y β γ E F ws τ) := by
  have e : floorSet ν y β γ E F ws τ = E ∩ ⋂ w ∈ ws, ⋃ j : ℤ,
      ({p : Ω × ℝ | ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋ = j} ∩
        Prod.snd ⁻¹' {t | ENNReal.ofReal (τ w) ≤ binMass ν y β γ E F w t j}) := by
    ext p
    simp only [floorSet, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, fun w hw => ⟨_, rfl, h w hw⟩⟩
    · rintro ⟨hp, h⟩
      refine ⟨hp, fun w hw => ?_⟩
      obtain ⟨j, hj, hle⟩ := h w hw
      rw [hj]; exact hle
  rw [e]
  refine hE.inter (Finset.measurableSet_biInter ws fun w _ => MeasurableSet.iUnion fun j => ?_)
  exact (measurableSet_bin hS w j).inter
    (measurable_snd (measurableSet_le measurable_const (measurable_binMass hE hS w j)))

/-- The labels failing the floor at one width. -/
def lightSet (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (F : ℝ → Fin 2 → ℝ) (w τ : ℝ) : Set (Ω × ℝ) :=
  {p | p ∈ E ∧ binMass ν y β γ E F w p.2 ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋ <
    ENNReal.ofReal τ}

theorem measurableSet_lightSet (hE : MeasurableSet E)
    (hS : Measurable (fun p : Ω × ℝ => FirstJet.scal y β γ F p.1 p.2)) (w τ : ℝ) :
    MeasurableSet (lightSet ν y β γ E F w τ) := by
  have e : lightSet ν y β γ E F w τ = E ∩ ⋃ j : ℤ,
      ({p : Ω × ℝ | ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋ = j} ∩
        Prod.snd ⁻¹' {t | binMass ν y β γ E F w t j < ENNReal.ofReal τ}) := by
    ext p
    simp only [lightSet, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, ⟨_, rfl, h⟩⟩
    · rintro ⟨hp, j, hj, hlt⟩
      refine ⟨hp, ?_⟩
      rw [hj]; exact hlt
  rw [e]
  exact hE.inter (MeasurableSet.iUnion fun j => (measurableSet_bin hS w j).inter
    (measurable_snd (measurableSet_lt (measurable_binMass hE hS w j) measurable_const)))

end Meas

/-- **Deletion cost at one width**: the labels whose `w`-bin is lighter than `τ` carry
incidence mass at most `K w^(-d) τ`, by the global support count. -/
theorem deleted_le {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (w τ : ℝ) (hw : ζ ≤ w) (hw1 : w ≤ 1)
    (hτ : 0 ≤ τ) :
    (ν.prod volume) (lightSet ν y β γ E F w τ) ≤ ENNReal.ofReal (K * w ^ (-d) * τ) := by
  classical
  have hS := measurable_scal hU.measurable_y hU.measurable_β hU.measurable_γ hU.measurable_F
  have hD := measurableSet_lightSet (ν := ν) hU.measurableSet_E hS w τ
  rw [Measure.prod_apply_symm hD]
  have hpt : ∀ t, ν ((fun l => (l, t)) ⁻¹' lightSet ν y β γ E F w τ) ≤
      (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (K * w ^ (-d) * τ)) t := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem ht]
      obtain ⟨C, hC, hmem⟩ := hU.support t w hw hw1
      have hsub : (fun l => (l, t)) ⁻¹' lightSet ν y β γ E F w τ ⊆
          ⋃ j ∈ C, {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j ∧
            binMass ν y β γ E F w t j < ENNReal.ofReal τ} := by
        intro l hl
        obtain ⟨hlE, hlt⟩ := hl
        exact mem_iUnion₂.2 ⟨_, hmem l hlE, hlE, rfl, hlt⟩
      have hterm : ∀ j ∈ C, ν {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j ∧
          binMass ν y β γ E F w t j < ENNReal.ofReal τ} ≤ ENNReal.ofReal τ := by
        intro j _
        by_cases hj : binMass ν y β γ E F w t j < ENNReal.ofReal τ
        · refine le_trans (measure_mono ?_) hj.le
          rintro l ⟨hl, hlj, -⟩
          exact ⟨hl, hlj⟩
        · have : {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j ∧
              binMass ν y β γ E F w t j < ENNReal.ofReal τ} = ∅ := by
            ext l; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
            rintro ⟨-, -, h⟩; exact hj h
          rw [this, measure_empty]; exact zero_le
      calc ν ((fun l => (l, t)) ⁻¹' lightSet ν y β γ E F w τ)
          ≤ ∑ j ∈ C, ν {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j ∧
            binMass ν y β γ E F w t j < ENNReal.ofReal τ} :=
            (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
        _ ≤ ∑ _j ∈ C, ENNReal.ofReal τ := Finset.sum_le_sum hterm
        _ = ENNReal.ofReal ((C.card : ℝ) * τ) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (K * w ^ (-d) * τ) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hτ)
    · rw [indicator_of_notMem ht]
      have : (fun l => (l, t)) ⁻¹' lightSet ν y β γ E F w τ = ∅ := by
        ext l; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨hl, -⟩
        exact ht (hU.subset_E hl).2
      rw [this, measure_empty]
  calc ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' lightSet ν y β γ E F w τ)
      ≤ ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (K * w ^ (-d) * τ)) t :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (K * w ^ (-d) * τ) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]; simp

/-- Retained bins at a width `w` inside a window of length `r` are few. -/
theorem floorSet_localCount {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hK : 1 ≤ K) (hζ : 0 < ζ)
    (ws : Finset ℝ) (τ : ℝ → ℝ) (t q r a w : ℝ) (hwws : w ∈ ws) (hw : 0 < w) (hwq : w ≤ q)
    (hτ : 0 < τ w) (hζr : ζ ≤ r) (hqr : q ≤ r) (hr : r ≤ 1) :
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ 2 * (600 * K ^ 4 * r ^ d / τ w) ∧
      ∀ l, (l, t) ∈ floorSet ν y β γ E F ws τ → a ≤ FirstJet.scal y β γ F l t →
        FirstJet.scal y β γ F l t ≤ a + r → ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C := by
  classical
  have hq : 0 < q := hw.trans_le hwq
  have hS := measurable_scal hU.measurable_y hU.measurable_β hU.measurable_γ hU.measurable_F
  set W : Finset ℤ := (Finset.Icc ⌊a / w⌋ ⌊(a + r) / w⌋).filter
    (fun j => ENNReal.ofReal (τ w) ≤ binMass ν y β γ E F w t j) with hW
  set C : Finset ℤ := W.biUnion (fun j => {⌊(j : ℝ) * w / q⌋, ⌊(j : ℝ) * w / q⌋ + 1}) with hC
  -- the bins of `W` lie in three windows of length `r`
  have hbin_sub : (⋃ j ∈ W, {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j}) ⊆
      {l | (l, t) ∈ E ∧ a - r ≤ FirstJet.scal y β γ F l t ∧
          FirstJet.scal y β γ F l t ≤ a - r + r} ∪
        {l | (l, t) ∈ E ∧ a ≤ FirstJet.scal y β γ F l t ∧ FirstJet.scal y β γ F l t ≤ a + r} ∪
        {l | (l, t) ∈ E ∧ a + r ≤ FirstJet.scal y β γ F l t ∧
          FirstJet.scal y β γ F l t ≤ a + r + r} := by
    intro l hl
    obtain ⟨j, hjW, hl⟩ := mem_iUnion₂.1 hl
    obtain ⟨hlE, hlj⟩ := hl
    have hjI := (Finset.mem_filter.1 hjW).1
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hjI
    set s := FirstJet.scal y β γ F l t
    have f1 := Int.floor_le (s / w)
    have f2 := Int.lt_floor_add_one (s / w)
    have g1 := Int.lt_floor_add_one (a / w)
    have g2 := Int.floor_le ((a + r) / w)
    rw [hlj] at f1 f2
    have hj1' : (⌊a / w⌋ : ℝ) ≤ j := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ ⌊(a + r) / w⌋ := by exact_mod_cast hj2
    rw [le_div_iff₀ hw] at f1
    rw [div_lt_iff₀ hw] at f2 g1
    rw [le_div_iff₀ hw] at g2
    have m1 : (⌊a / w⌋ : ℝ) * w ≤ (j : ℝ) * w := mul_le_mul_of_nonneg_right hj1' hw.le
    have m2 : ((j : ℝ) + 1) * w ≤ ((⌊(a + r) / w⌋ : ℝ) + 1) * w :=
      mul_le_mul_of_nonneg_right (by linarith) hw.le
    have hwr : w ≤ r := hwq.trans hqr
    have hlo : a - r ≤ s := by nlinarith
    have hhi : s ≤ a + r + r := by nlinarith
    by_cases h1 : s ≤ a
    · left; left; exact ⟨hlE, hlo, by linarith⟩
    · by_cases h2 : s ≤ a + r
      · left; right; exact ⟨hlE, by linarith, h2⟩
      · right; exact ⟨hlE, by linarith, hhi⟩
  have hr0 : 0 ≤ r := hζ.le.trans hζr
  have hrd : 0 ≤ r ^ d := Real.rpow_nonneg hr0 d
  have hwin := window_mass hU hK hζ t r
  have hmassW : (W.card : ENNReal) * ENNReal.ofReal (τ w) ≤
      ENNReal.ofReal (600 * K ^ 4 * r ^ d) := by
    calc (W.card : ENNReal) * ENNReal.ofReal (τ w)
        = ∑ _j ∈ W, ENNReal.ofReal (τ w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ W, binMass ν y β γ E F w t j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.1 hj).2)
      _ = ν (⋃ j ∈ W, {l | (l, t) ∈ E ∧ ⌊FirstJet.scal y β γ F l t / w⌋ = j}) := by
          rw [measure_biUnion_finset]
          · rfl
          · intro i _ j _ hij
            exact Set.disjoint_left.2 (fun l hi hj' => hij (hi.2.symm.trans hj'.2))
          · intro j _
            exact (hU.measurableSet_E.inter (measurableSet_bin hS w j)).preimage
              measurable_prodMk_right
      _ ≤ _ := measure_mono hbin_sub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ENNReal.ofReal (200 * K ^ 4 * r ^ d) + ENNReal.ofReal (200 * K ^ 4 * r ^ d) +
          ENNReal.ofReal (200 * K ^ 4 * r ^ d) :=
          add_le_add (add_le_add (hwin (a - r) hζr hr) (hwin a hζr hr)) (hwin (a + r) hζr hr)
      _ = ENNReal.ofReal (600 * K ^ 4 * r ^ d) := by
          have h0 : 0 ≤ 200 * K ^ 4 * r ^ d := mul_nonneg (by positivity) hrd
          rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (add_nonneg h0 h0) h0]
          ring_nf
  have hWcard : (W.card : ℝ) ≤ 600 * K ^ 4 * r ^ d / τ w := by
    rw [le_div_iff₀ hτ]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hmassW
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hrd)).1 hmassW
  refine ⟨C, ?_, ?_⟩
  · have h1 : C.card ≤ ∑ j ∈ W, ({⌊(j : ℝ) * w / q⌋, ⌊(j : ℝ) * w / q⌋ + 1} :
        Finset ℤ).card := Finset.card_biUnion_le
    have h2 : ∀ j ∈ W, ({⌊(j : ℝ) * w / q⌋, ⌊(j : ℝ) * w / q⌋ + 1} : Finset ℤ).card ≤ 2 :=
      fun j _ => Finset.card_le_two
    have h3 : C.card ≤ 2 * W.card := by
      calc C.card ≤ _ := h1
        _ ≤ ∑ _j ∈ W, 2 := Finset.sum_le_sum h2
        _ = 2 * W.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    calc (C.card : ℝ) ≤ 2 * W.card := by exact_mod_cast h3
      _ ≤ 2 * (600 * K ^ 4 * r ^ d / τ w) := by linarith
  · intro l hl h1 h2
    obtain ⟨hlE, hfl⟩ := hl
    set s := FirstJet.scal y β γ F l t
    set j := ⌊s / w⌋ with hj
    have hjW : j ∈ W := by
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, hfl w hwws⟩
      · exact Int.floor_le_floor (div_le_div_of_nonneg_right h1 hw.le)
      · exact Int.floor_le_floor (div_le_div_of_nonneg_right h2 hw.le)
    refine Finset.mem_biUnion.2 ⟨j, hjW, ?_⟩
    have f1 := Int.floor_le (s / w)
    have f2 := Int.lt_floor_add_one (s / w)
    rw [le_div_iff₀ hw] at f1
    rw [div_lt_iff₀ hw] at f2
    have k1 : ⌊(j : ℝ) * w / q⌋ ≤ ⌊s / q⌋ :=
      Int.floor_le_floor (div_le_div_of_nonneg_right f1 hq.le)
    have k2 : ⌊s / q⌋ ≤ ⌊(j : ℝ) * w / q⌋ + 1 := by
      have e1 : s / q < (j : ℝ) * w / q + 1 := by
        rw [div_add_one hq.ne', div_lt_div_iff_of_pos_right hq]; nlinarith
      have e2 := Int.lt_floor_add_one ((j : ℝ) * w / q)
      have : s / q < (⌊(j : ℝ) * w / q⌋ : ℝ) + 2 := by linarith
      have : ⌊s / q⌋ < ⌊(j : ℝ) * w / q⌋ + 2 := by
        rw [Int.floor_lt]; push_cast; linarith
      omega
    rcases eq_or_lt_of_le k1 with h | h
    · simp [← h]
    · have : ⌊s / q⌋ = ⌊(j : ℝ) * w / q⌋ + 1 := by omega
      simp [this]

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
