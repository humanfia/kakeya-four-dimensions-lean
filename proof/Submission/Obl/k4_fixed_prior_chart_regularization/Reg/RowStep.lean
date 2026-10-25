-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/RowStep.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.RowShared
import Submission.Obl.k4_fixed_prior_chart_regularization.RegKernels

/-!
# One scale of the row comparison

Paper §9: "By averaging choose one anchor time per interval; retaining labels at times with
`|F - F_anchor| ≤ K r` leaves dense total mass ... Retain also a separated residue class of
intervals with dense total mass, so that active times within distance `r` compare in the same
interval." On each interval `[j r, (j+1) r)` an anchor `a_j` with
`m_j² ≤ r · (labels sharing a line with a_j)` exists by Cauchy–Schwarz (`exists_heavy_time`);
the shared labels at times `u` with `|F(u) - F(a_j)| > Λ r` weigh at most `r · 61440 K⁹ Λ^(d-1)`
by the shared-line bound (`shared_line_bound'`). Keeping the labels at times close to the anchor
in the intervals of the best residue class modulo `3` (`row_scale_step`) retains mass
`≥ m²/12` once `61440 K⁹ Λ^(d-1) ≤ m²/24`, and any two retained times within distance `r`
satisfy `|F(t) - F(u)| ≤ 2 Λ r`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The coordinate swap -/

/-- Swap the two static coordinates. -/
def swapY (y : Ω → Fin 2 → ℝ) : Ω → Fin 2 → ℝ := fun l => ![y l 1, y l 0]

/-- Swap the two row components. -/
def swapF (F : ℝ → Fin 2 → ℝ) : ℝ → Fin 2 → ℝ := fun t => ![F t 1, F t 0]

theorem scal_swap (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    FirstJet.scal (swapY y) β γ (swapF F) l t = FirstJet.scal y β γ F l t := by
  simp only [FirstJet.scal, swapY, swapF, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

theorem chart_swap {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) :
    UnregularizedChart ν (swapY y) β γ E (swapF F) d K ζ where
  measurable_y := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact (measurable_pi_apply 1).comp h.measurable_y
    · exact (measurable_pi_apply 0).comp h.measurable_y
  measurable_β := h.measurable_β
  measurable_γ := h.measurable_γ
  measurable_F := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact (measurable_pi_apply 1).comp h.measurable_F
    · exact (measurable_pi_apply 0).comp h.measurable_F
  measurableSet_E := h.measurableSet_E
  subset_E := h.subset_E
  bound_y := fun l i => by
    fin_cases i
    · exact h.bound_y l 1
    · exact h.bound_y l 0
  bound_β := h.bound_β
  bound_γ := h.bound_γ
  bound_F := fun t i => by
    fin_cases i
    · exact h.bound_F t 1
    · exact h.bound_F t 0
  mass := h.mass
  mixedCap := fun t r w hr hr1 hw hw1 z j => by
    refine le_trans (measure_mono ?_) (h.mixedCap t r w hr hr1 hw hw1 ![z 1, z 0] j)
    rintro l ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h4, h3⟩
  support := fun t w hw hw1 => by
    obtain ⟨C, hC, hmem⟩ := h.support t w hw hw1
    exact ⟨C, hC, fun l hl => by rw [scal_swap]; exact hmem l hl⟩

theorem LocalCounts.swap {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : LocalCounts y β γ E F d K ζ) :
    LocalCounts (swapY y) β γ E (swapF F) d K ζ := by
  intro t q r a hq hqr hr
  obtain ⟨C, hC, hmem⟩ := h t q r a hq hqr hr
  refine ⟨C, hC, fun l hl h1 h2 => ?_⟩
  rw [scal_swap] at h1 h2 ⊢
  exact hmem l hl h1 h2

/-- The shared-line bound for either row component (the larger one). -/
theorem shared_line_bound' {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hL : LocalCounts y β γ E F d K ζ)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (t u r : ℝ) (hr : ζ ≤ r)
    (hr1 : r ≤ 1) (htu : |u - t| ≤ r) (i₀ : Fin 2) (hM : r ≤ |F u i₀ - F t i₀|)
    (hmax : ∀ i, |F u i - F t i| ≤ |F u i₀ - F t i₀|) :
    ν {l | (l, t) ∈ E ∧ (l, u) ∈ E} ≤
      ENNReal.ofReal (61440 * K ^ 9 * (r / |F u i₀ - F t i₀|) ^ (1 - d)) := by
  fin_cases i₀
  · exact shared_line_bound hU hL hK hζ hd hd1 t u r hr hr1 htu hM (hmax 1)
  · exact shared_line_bound (chart_swap hU) hL.swap hK hζ hd hd1 t u r hr hr1 htu hM (hmax 0)

/-- Cauchy–Schwarz for finite sums in `ℝ≥0∞`. -/
theorem ennreal_sq_sum_le {ι : Type*} (s : Finset ι) (f : ι → ENNReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) : (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  set g : ι → NNReal := fun i => (f i).toNNReal with hg
  have hfg : ∀ i ∈ s, f i = (g i : ENNReal) := fun i hi => (ENNReal.coe_toNNReal (hf i hi)).symm
  have h1 : (∑ i ∈ s, f i) = ((∑ i ∈ s, g i : NNReal) : ENNReal) := by
    rw [Finset.sum_congr rfl hfg]; push_cast; rfl
  have h2 : (∑ i ∈ s, f i ^ 2) = ((∑ i ∈ s, g i ^ 2 : NNReal) : ENNReal) := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [hfg i hi])]; push_cast; rfl
  rw [h1, h2]
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := g)
  calc ((∑ i ∈ s, g i : NNReal) : ENNReal) ^ 2 = (((∑ i ∈ s, g i) ^ 2 : NNReal) : ENNReal) := by
        push_cast; rfl
    _ ≤ ((s.card * ∑ i ∈ s, g i ^ 2 : NNReal) : ENNReal) := ENNReal.coe_le_coe.2 this
    _ = _ := by push_cast; rfl

/-- The time interval of index `j` at scale `r`. -/
def slice (G : Set (Ω × ℝ)) (r : ℝ) (j : ℕ) : Set (Ω × ℝ) := G ∩ {p | ⌊p.2 / r⌋₊ = j}

theorem measurableSet_slice {G : Set (Ω × ℝ)} (hG : MeasurableSet G) (r : ℝ) (j : ℕ) :
    MeasurableSet (slice G r j) :=
  hG.inter ((Nat.measurable_floor.comp (measurable_snd.div_const r)) (measurableSet_singleton j))

theorem slice_time {G : Set (Ω × ℝ)} (hG01 : ∀ q ∈ G, q.2 ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : 0 < r)
    (j : ℕ) : ∀ q ∈ slice G r j, q.2 ∈ Icc ((j : ℝ) * r) (((j : ℝ) + 1) * r) := by
  rintro q ⟨hq, hj⟩
  have h0 : 0 ≤ q.2 / r := div_nonneg (hG01 q hq).1 hr.le
  have f1 := Nat.floor_le h0
  have f2 := Nat.lt_floor_add_one (q.2 / r)
  simp only [mem_ofPred_eq] at hj
  rw [hj] at f1 f2
  rw [le_div_iff₀ hr] at f1
  rw [div_lt_iff₀ hr] at f2
  exact ⟨f1, f2.le⟩

set_option maxHeartbeats 4000000 in
/-- **One scale of the row comparison.** -/
theorem row_scale_step {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hL : LocalCounts y β γ E F d K ζ)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d) (hd1 : d < 1) (G : Set (Ω × ℝ))
    (hG : MeasurableSet G) (hGE : G ⊆ E) (r Λ m : ℝ) (hr : ζ ≤ r) (hr1 : r ≤ 1) (hΛ : 1 ≤ Λ)
    (hm : 0 ≤ m) (hmass : ENNReal.ofReal m ≤ (ν.prod volume) G)
    (hB : 61440 * K ^ 9 * Λ ^ (d - 1) ≤ m ^ 2 / 24) :
    ∃ G' : Set (Ω × ℝ), G' ⊆ G ∧ MeasurableSet G' ∧
      ENNReal.ofReal (m ^ 2 / 12) ≤ (ν.prod volume) G' ∧
      ∀ t u, (∃ l, (l, t) ∈ G') → (∃ l, (l, u) ∈ G') → |t - u| ≤ r → ∀ i,
        |F t i - F u i| ≤ 2 * Λ * r := by
  classical
  have hr0 : 0 < r := hζ.trans_le hr
  set B : ℝ := 61440 * K ^ 9 * Λ ^ (d - 1) with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hG01 : ∀ q ∈ G, q.2 ∈ Icc (0 : ℝ) 1 := fun q hq => (hU.subset_E (hGE hq)).2
  have hFm : ∀ i, Measurable (fun t => F t i) := fun i =>
    (measurable_pi_apply i).comp hU.measurable_F
  set n : ℕ := ⌊1 / r⌋₊ with hn_def
  have hnr : ((n : ℝ) + 1) * r ≤ 2 := by
    have h1 : (n : ℝ) ≤ 1 / r := Nat.floor_le (by positivity)
    rw [le_div_iff₀ hr0] at h1
    linarith
  -- anchors
  have hanchor : ∀ j : ℕ, ∃ t₀ ∈ Icc ((j : ℝ) * r) (((j : ℝ) + 1) * r),
      ((ν.prod volume) (slice G r j)) ^ 2 ≤ ENNReal.ofReal (((j : ℝ) + 1) * r - j * r) *
        ν univ * (ν.prod volume) (slice G r j ∩ {q | (q.1, t₀) ∈ slice G r j}) :=
    fun j => JetFit.exists_heavy_time ν (measurableSet_slice hG r j) (by nlinarith)
      (slice_time hG01 hr0 j)
  choose a ha hamass using hanchor
  -- the retained part of each slice
  set R : ℕ → Set (Ω × ℝ) := fun j =>
    slice G r j ∩ {q | ∀ i, |F q.2 i - F (a j) i| ≤ Λ * r} with hR_def
  have hcloseM : ∀ j, MeasurableSet {q : Ω × ℝ | ∀ i, |F q.2 i - F (a j) i| ≤ Λ * r} := by
    intro j
    have : {q : Ω × ℝ | ∀ i, |F q.2 i - F (a j) i| ≤ Λ * r} =
        ⋂ i, {q : Ω × ℝ | |F q.2 i - F (a j) i| ≤ Λ * r} := by ext q; simp
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((((hFm i).comp measurable_snd).sub_const _).abs) measurable_const
  have hRm : ∀ j, MeasurableSet (R j) := fun j =>
    (measurableSet_slice hG r j).inter (hcloseM j)
  -- far shared labels
  have hfar : ∀ j, (ν.prod volume) (slice G r j ∩ {q | (q.1, a j) ∈ slice G r j}) ≤
      (ν.prod volume) (R j) + ENNReal.ofReal (r * B) := by
    intro j
    set Far : Set (Ω × ℝ) := slice G r j ∩ ((fun q : Ω × ℝ => (q.1, a j)) ⁻¹' slice G r j) ∩
          {q | ∀ i, |F q.2 i - F (a j) i| ≤ Λ * r}ᶜ with hFar_def
    have hsub : slice G r j ∩ {q | (q.1, a j) ∈ slice G r j} ⊆ R j ∪ Far := by
      rintro q ⟨hq1, hq2⟩
      by_cases hc : ∀ i, |F q.2 i - F (a j) i| ≤ Λ * r
      · exact Or.inl ⟨hq1, hc⟩
      · exact Or.inr ⟨⟨hq1, hq2⟩, hc⟩
    have hFarm : MeasurableSet Far :=
      ((measurableSet_slice hG r j).inter ((measurable_fst.prodMk measurable_const)
        (measurableSet_slice hG r j))).inter (hcloseM j).compl
    have hpt : ∀ u, ν ((fun l => (l, u)) ⁻¹' Far) ≤
        (Icc ((j : ℝ) * r) (((j : ℝ) + 1) * r)).indicator (fun _ => ENNReal.ofReal B) u := by
      intro u
      by_cases hu : u ∈ Icc ((j : ℝ) * r) (((j : ℝ) + 1) * r)
      · rw [indicator_of_mem hu]
        by_cases hc : ∀ i, |F u i - F (a j) i| ≤ Λ * r
        · have : (fun l => (l, u)) ⁻¹' Far = ∅ := by
            ext l; simp only [mem_preimage, mem_empty_iff_false, iff_false]
            rintro ⟨-, h⟩; exact h hc
          rw [this, measure_empty]; exact zero_le
        · push Not at hc
          obtain ⟨i, hi⟩ := hc
          -- the larger component
          set i₀ : Fin 2 := if |F u 1 - F (a j) 1| ≤ |F u 0 - F (a j) 0| then 0 else 1
            with hi₀
          have hmax : ∀ i', |F u i' - F (a j) i'| ≤ |F u i₀ - F (a j) i₀| := by
            intro i'
            by_cases h10 : |F u 1 - F (a j) 1| ≤ |F u 0 - F (a j) 0|
            · have : i₀ = 0 := by simp [hi₀, h10]
              rw [this]; fin_cases i' <;> simp [h10]
            · have : i₀ = 1 := by simp [hi₀, h10]
              rw [this]; push Not at h10; fin_cases i' <;> simp [h10.le]
          have hMi : Λ * r < |F u i₀ - F (a j) i₀| := hi.trans_le (hmax i)
          have hrM : r ≤ |F u i₀ - F (a j) i₀| := by nlinarith
          have hau : |u - a j| ≤ r := by
            have := ha j
            rw [abs_le]; constructor <;> nlinarith [hu.1, hu.2, this.1, this.2]
          have hsl := shared_line_bound' hU hL hK hζ hd hd1.le (a j) u r hr hr1 hau i₀ hrM hmax
          refine le_trans (measure_mono ?_) (hsl.trans (ENNReal.ofReal_le_ofReal ?_))
          · rintro l ⟨⟨h1, h2⟩, -⟩
            exact ⟨hGE h2.1, hGE h1.1⟩
          · -- `(r/M)^(1-d) ≤ Λ^(d-1)`
            set M := |F u i₀ - F (a j) i₀|
            have hM0 : 0 < M := hr0.trans_le hrM
            have hrM' : r / M ≤ 1 / Λ := by
              rw [div_le_div_iff₀ hM0 (by linarith)]; nlinarith
            have h1 : (r / M) ^ (1 - d) ≤ (1 / Λ) ^ (1 - d) :=
              Real.rpow_le_rpow (by positivity) hrM' (by linarith)
            have h2 : (1 / Λ) ^ (1 - d) = Λ ^ (d - 1) := by
              rw [one_div, Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)]
              ring_nf
            rw [h2] at h1
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · rw [indicator_of_notMem hu]
        have : (fun l => (l, u)) ⁻¹' Far = ∅ := by
          ext l; simp only [mem_preimage, mem_empty_iff_false, iff_false]
          rintro ⟨⟨h1, -⟩, -⟩
          exact hu (slice_time hG01 hr0 j _ h1)
        rw [this, measure_empty]
    have hFar : (ν.prod volume) Far ≤ ENNReal.ofReal (r * B) := by
      rw [Measure.prod_apply_symm hFarm]
      calc ∫⁻ u, ν ((fun l => (l, u)) ⁻¹' Far)
          ≤ ∫⁻ u, (Icc ((j : ℝ) * r) (((j : ℝ) + 1) * r)).indicator
              (fun _ => ENNReal.ofReal B) u := lintegral_mono hpt
        _ = ENNReal.ofReal (r * B) := by
            rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
              ← ENNReal.ofReal_mul hB0]
            congr 1; ring
    calc (ν.prod volume) (slice G r j ∩ {q | (q.1, a j) ∈ slice G r j})
        ≤ (ν.prod volume) (R j ∪ Far) := measure_mono hsub
      _ ≤ (ν.prod volume) (R j) + (ν.prod volume) Far := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hFar
  -- each slice
  have hslice : ∀ j, ((ν.prod volume) (slice G r j)) ^ 2 ≤
      ENNReal.ofReal r * ((ν.prod volume) (R j) + ENNReal.ofReal (r * B)) := by
    intro j
    refine (hamass j).trans ?_
    rw [measure_univ, mul_one, show ((j : ℝ) + 1) * r - j * r = r by ring]
    exact mul_le_mul_of_nonneg_left (hfar j) (by positivity)
  -- the slices cover `G`
  have hcover : G = ⋃ j ∈ Finset.range (n + 1), slice G r j := by
    ext q
    simp only [mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro hq
      refine ⟨⌊q.2 / r⌋₊, ?_, hq, rfl⟩
      have := Nat.floor_le_floor (div_le_div_of_nonneg_right (hG01 q hq).2 hr0.le)
      omega
    · rintro ⟨j, -, hq, -⟩; exact hq
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint (slice G r) := by
    intro i _ j _ hij
    exact Set.disjoint_left.2 (fun q hi hj => hij (hi.2.symm.trans hj.2))
  have hsumG : (ν.prod volume) G = ∑ j ∈ Finset.range (n + 1), (ν.prod volume) (slice G r j) := by
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset hdisj (fun j _ => measurableSet_slice hG r j)
  have hfin : ∀ j ∈ Finset.range (n + 1), (ν.prod volume) (slice G r j) ≠ ⊤ := by
    intro j _
    refine ne_top_of_le_ne_top (b := (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1)) ?_ ?_
    · rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp
    · exact measure_mono (fun q hq => ⟨mem_univ _, hG01 q hq.1⟩)
  -- the best residue class
  set cls : Fin 3 → Finset ℕ := fun ρ =>
    (Finset.range (n + 1)).filter (fun j => (⟨j % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ρ)
    with hcls
  set X : Fin 3 → ENNReal := fun ρ => ∑ j ∈ cls ρ, ((ν.prod volume) (slice G r j)) ^ 2
  have hXsum : ∑ ρ, X ρ = ∑ j ∈ Finset.range (n + 1), ((ν.prod volume) (slice G r j)) ^ 2 :=
    Finset.sum_fiberwise _ _ _
  obtain ⟨ρ, -, hρ⟩ := Finset.exists_max_image Finset.univ X Finset.univ_nonempty
  have hX3 : ∑ j ∈ Finset.range (n + 1), ((ν.prod volume) (slice G r j)) ^ 2 ≤ 3 * X ρ := by
    rw [← hXsum]
    calc ∑ ρ', X ρ' ≤ ∑ _ρ' : Fin 3, X ρ := Finset.sum_le_sum (fun ρ' _ => hρ ρ' (Finset.mem_univ _))
      _ = 3 * X ρ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  -- the retained set
  set G' : Set (Ω × ℝ) := ⋃ j ∈ cls ρ, R j with hG'_def
  have hG'm : MeasurableSet G' := Finset.measurableSet_biUnion _ (fun j _ => hRm j)
  have hRdisj : (↑(cls ρ) : Set ℕ).PairwiseDisjoint R := by
    intro i _ j _ hij
    exact Set.disjoint_left.2 (fun q hi hj => hij (hi.1.2.symm.trans hj.1.2))
  have hG'sum : (ν.prod volume) G' = ∑ j ∈ cls ρ, (ν.prod volume) (R j) :=
    measure_biUnion_finset hRdisj (fun j _ => hRm j)
  have hclscard : ((cls ρ).card : ℝ) ≤ (n : ℝ) + 1 := by
    have := Finset.card_filter_le (Finset.range (n + 1))
      (fun j => (⟨j % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ρ)
    rw [Finset.card_range] at this
    exact_mod_cast this
  refine ⟨G', ?_, hG'm, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, -, hq⟩ := mem_iUnion₂.1 hq
    exact hq.1.1
  · -- the mass
    set T := (ν.prod volume) G'
    have hXρ : X ρ ≤ ENNReal.ofReal r * (T + ENNReal.ofReal (((n : ℝ) + 1) * (r * B))) := by
      calc X ρ ≤ ∑ j ∈ cls ρ, ENNReal.ofReal r * ((ν.prod volume) (R j) +
            ENNReal.ofReal (r * B)) := Finset.sum_le_sum (fun j _ => hslice j)
        _ = ENNReal.ofReal r * (T + (cls ρ).card * ENNReal.ofReal (r * B)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              hG'sum]
        _ ≤ ENNReal.ofReal r * (T + ENNReal.ofReal (((n : ℝ) + 1) * (r * B))) := by
            gcongr
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right hclscard (mul_nonneg hr0.le hB0))
    have hmain : ENNReal.ofReal (m ^ 2) ≤
        ENNReal.ofReal (3 * ((n : ℝ) + 1) * r) * (T + ENNReal.ofReal (2 * B)) := by
      calc ENNReal.ofReal (m ^ 2) = (ENNReal.ofReal m) ^ 2 := by rw [ENNReal.ofReal_pow hm]
        _ ≤ ((ν.prod volume) G) ^ 2 := by gcongr
        _ = (∑ j ∈ Finset.range (n + 1), (ν.prod volume) (slice G r j)) ^ 2 := by rw [hsumG]
        _ ≤ (Finset.range (n + 1)).card *
            ∑ j ∈ Finset.range (n + 1), ((ν.prod volume) (slice G r j)) ^ 2 :=
            ennreal_sq_sum_le _ _ hfin
        _ ≤ ((n : ENNReal) + 1) * (3 * X ρ) := by
            rw [Finset.card_range]; push_cast; gcongr
        _ ≤ ((n : ENNReal) + 1) * (3 * (ENNReal.ofReal r *
            (T + ENNReal.ofReal (((n : ℝ) + 1) * (r * B))))) := by gcongr
        _ = ENNReal.ofReal (3 * ((n : ℝ) + 1) * r) *
            (T + ENNReal.ofReal (((n : ℝ) + 1) * (r * B))) := by
            have e3 : ENNReal.ofReal (3 * ((n : ℝ) + 1) * r) =
                3 * ((n : ENNReal) + 1) * ENNReal.ofReal r := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
                ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
            rw [e3]; ring
        _ ≤ ENNReal.ofReal (3 * ((n : ℝ) + 1) * r) * (T + ENNReal.ofReal (2 * B)) := by
            refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
              (by positivity)
            calc ((n : ℝ) + 1) * (r * B) = (((n : ℝ) + 1) * r) * B := by ring
              _ ≤ 2 * B := mul_le_mul_of_nonneg_right hnr hB0
    have h6 : ENNReal.ofReal (3 * ((n : ℝ) + 1) * r) ≤ 6 := by
      rw [show (6 : ENNReal) = ENNReal.ofReal 6 by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h12 : ENNReal.ofReal (m ^ 2) ≤ 6 * T + ENNReal.ofReal (m ^ 2 / 2) := by
      calc ENNReal.ofReal (m ^ 2) ≤ 6 * (T + ENNReal.ofReal (2 * B)) :=
            hmain.trans (mul_le_mul_of_nonneg_right h6 (by positivity))
        _ = 6 * T + ENNReal.ofReal (12 * B) := by
            rw [mul_add, show (6 : ENNReal) = ENNReal.ofReal 6 by simp,
              ← ENNReal.ofReal_mul (by norm_num)]
            ring_nf
        _ ≤ 6 * T + ENNReal.ofReal (m ^ 2 / 2) := by
            gcongr; linarith
    have hsplit : ENNReal.ofReal (m ^ 2) = ENNReal.ofReal (m ^ 2 / 2) +
        ENNReal.ofReal (m ^ 2 / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    rw [hsplit] at h12
    have h13 : ENNReal.ofReal (m ^ 2 / 2) ≤ 6 * T :=
      (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h12
    have h14 : ENNReal.ofReal (m ^ 2 / 2) = 6 * ENNReal.ofReal (m ^ 2 / 12) := by
      rw [show (6 : ENNReal) = ENNReal.ofReal 6 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [h14] at h13
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h13
  · -- the comparison
    rintro t u ⟨l, hl⟩ ⟨l', hl'⟩ htu i
    obtain ⟨j, hj, hlj⟩ := mem_iUnion₂.1 hl
    obtain ⟨j', hj', hlj'⟩ := mem_iUnion₂.1 hl'
    have ht := slice_time hG01 hr0 j _ hlj.1
    have hu := slice_time hG01 hr0 j' _ hlj'.1
    have hjj : j = j' := by
      have hmod : j % 3 = j' % 3 := by
        have e1 := (Finset.mem_filter.1 hj).2
        have e2 := (Finset.mem_filter.1 hj').2
        have := e1.trans e2.symm
        simpa using congrArg Fin.val this
      have ht1 : t < ((j : ℝ) + 1) * r := by
        have := hlj.1.2
        simp only [mem_ofPred_eq] at this
        have f2 := Nat.lt_floor_add_one (t / r)
        rw [this] at f2
        rwa [div_lt_iff₀ hr0] at f2
      have hu1 : u < ((j' : ℝ) + 1) * r := by
        have := hlj'.1.2
        simp only [mem_ofPred_eq] at this
        have f2 := Nat.lt_floor_add_one (u / r)
        rw [this] at f2
        rwa [div_lt_iff₀ hr0] at f2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h3 : j + 3 ≤ j' := by omega
        have h3' : (j : ℝ) + 3 ≤ j' := by exact_mod_cast h3
        have h4 := mul_le_mul_of_nonneg_right h3' hr0.le
        have := (abs_le.1 htu).1
        nlinarith [hu.1, ht1]
      · have h3 : j' + 3 ≤ j := by omega
        have h3' : (j' : ℝ) + 3 ≤ j := by exact_mod_cast h3
        have h4 := mul_le_mul_of_nonneg_right h3' hr0.le
        have := (abs_le.1 htu).2
        nlinarith [ht.1, hu1]
    subst hjj
    have h1 := hlj.2 i
    have h2 := hlj'.2 i
    calc |F t i - F u i| = |(F t i - F (a j) i) - (F u i - F (a j) i)| := by ring_nf
      _ ≤ |F t i - F (a j) i| + |F u i - F (a j) i| := abs_sub _ _
      _ ≤ Λ * r + Λ * r := add_le_add h1 h2
      _ = 2 * Λ * r := by ring

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
