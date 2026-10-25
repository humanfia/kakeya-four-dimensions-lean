import Submission.Obl.k4_scalar_initial_true_horizon.InitialGroupFinal

/-!
# Covered mass of one world

The incidences of a world lying in no good cell are: incidences of short trajectories
(at most `φ₀` in total), incidences of bad long trajectories of all groups (the group
bound, summed over groups with a bounded multiplicity of the hidden-bin windows), and
null sets.  Letting the grid scale tend to zero, the light-square part of the group
bounds is controlled by the lower density exception.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden obsL)

/-- Incidence mass of a product set as an integral of occupation times. -/
theorem restrict_prod_apply_eq (ν : Measure Coeff) [SFinite ν] {E : Set (Coeff × ℝ)}
    (hE : MeasurableSet E) {S : Set Coeff} (hS : MeasurableSet S) {Ib : Set ℝ}
    (hIb : MeasurableSet Ib) :
    ((ν.prod volume).restrict E) (S ×ˢ Ib) =
      ∫⁻ l in S, volume {t ∈ Ib | (l, t) ∈ E} ∂ν := by
  rw [Measure.restrict_apply (hS.prod hIb), Measure.prod_apply ((hS.prod hIb).inter hE),
    ← lintegral_indicator hS]
  apply lintegral_congr
  intro l
  by_cases hl : l ∈ S
  · rw [indicator_of_mem hl]
    congr 1
    ext t
    simp [hl]
  · rw [indicator_of_notMem hl]
    have : Prod.mk l ⁻¹' (S ×ˢ Ib ∩ E) = ∅ := by ext t; simp [hl]
    rw [this, measure_empty]

/-- Short trajectories carry at most `φ₀ q` in a block. -/
theorem short_mass_le (ν : Measure Coeff) [IsProbabilityMeasure ν] {E : Set (Coeff × ℝ)}
    (hE : MeasurableSet E) (t₀ q φ₀ : ℝ) :
    ((ν.prod volume).restrict E) ({l | ¬ longTraj E t₀ q φ₀ l} ×ˢ Ico t₀ (t₀ + q)) ≤
      ENNReal.ofReal (φ₀ * q) := by
  have hS : MeasurableSet {l | ¬ longTraj E t₀ q φ₀ l} :=
    (measurableSet_longTraj hE t₀ q φ₀).compl
  rw [restrict_prod_apply_eq ν hE hS measurableSet_Ico]
  calc ∫⁻ l in {l | ¬ longTraj E t₀ q φ₀ l}, volume {t ∈ Ico t₀ (t₀ + q) | (l, t) ∈ E} ∂ν
      ≤ ∫⁻ _l in {l | ¬ longTraj E t₀ q φ₀ l}, ENNReal.ofReal (φ₀ * q) ∂ν := by
        apply setLIntegral_mono' hS
        intro l hl
        exact (not_le.mp hl).le
    _ = ENNReal.ofReal (φ₀ * q) * ν {l | ¬ longTraj E t₀ q φ₀ l} := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (φ₀ * q) * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal (φ₀ * q) := mul_one _

/-- Each point lies in exactly `2c + 1` windows `[m - c, m + c]`. -/
theorem tsum_window_indicator (x : ℤ) {c : ℤ} (hc : 0 ≤ c) :
    ∑' m : ℤ, (if x ∈ Icc (m - c) (m + c) then (1 : ℝ≥0∞) else 0) = ((2 * c + 1).toNat : ℝ≥0∞) := by
  classical
  have hsupp : ∀ m ∉ Finset.Icc (x - c) (x + c), (if x ∈ Icc (m - c) (m + c) then (1 : ℝ≥0∞)
      else 0) = 0 := by
    intro m hm
    rw [if_neg]
    intro hx
    apply hm
    simp only [Finset.mem_Icc, mem_Icc] at hx ⊢
    omega
  rw [tsum_eq_sum hsupp]
  have : ∀ m ∈ Finset.Icc (x - c) (x + c), (if x ∈ Icc (m - c) (m + c) then (1 : ℝ≥0∞)
      else 0) = 1 := by
    intro m hm
    rw [if_pos]
    simp only [Finset.mem_Icc, mem_Icc] at hm ⊢
    omega
  rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
  congr 2
  omega

/-- The windows of all groups of a block cover each incidence of the block `2c + 1` times. -/
theorem tsum_strip_le (μ : Measure (Coeff × ℝ)) (aL : ℝ) (Ib : Set ℝ) (hIb : MeasurableSet Ib)
    {c : ℤ} (hc : 0 ≤ c) :
    ∑' m : ℤ, μ {p | p.2 ∈ Ib ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)} =
      ((2 * c + 1).toNat : ℝ≥0∞) * μ {p | p.2 ∈ Ib} := by
  have hfl : Measurable (fun p : Coeff × ℝ => ⌊hidden p.1 p.2 / aL⌋) :=
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_hidden.div_const aL).floor
  have hmeas : ∀ m : ℤ, MeasurableSet {p : Coeff × ℝ | p.2 ∈ Ib ∧
      ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)} := fun m =>
    (measurable_snd hIb).inter (hfl measurableSet_Icc)
  have hIbm : MeasurableSet {p : Coeff × ℝ | p.2 ∈ Ib} := measurable_snd hIb
  simp_rw [← lintegral_indicator_one (hmeas _)]
  rw [← lintegral_tsum fun m => (measurable_one.indicator (hmeas m)).aemeasurable,
    ← lintegral_indicator_one hIbm, ← lintegral_const_mul _ (measurable_one.indicator hIbm)]
  apply lintegral_congr
  intro p
  by_cases hp : p.2 ∈ Ib
  · have h1 : ∀ m : ℤ, ({p : Coeff × ℝ | p.2 ∈ Ib ∧
        ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)}).indicator 1 p =
        (if ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c) then (1 : ℝ≥0∞) else 0) := by
      intro m
      classical
      by_cases hm : ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)
      · rw [indicator_of_mem (show p ∈ {p : Coeff × ℝ | p.2 ∈ Ib ∧
          ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)} from ⟨hp, hm⟩), if_pos hm]; rfl
      · rw [indicator_of_notMem (fun h => hm h.2), if_neg hm]
    simp_rw [h1]
    rw [tsum_window_indicator _ hc, indicator_of_mem (show p ∈ {p : Coeff × ℝ | p.2 ∈ Ib} from hp)]
    simp
  · have h1 : ∀ m : ℤ, ({p : Coeff × ℝ | p.2 ∈ Ib ∧
        ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c) (m + c)}).indicator (1 : Coeff × ℝ → ℝ≥0∞) p = 0 :=
      fun m => indicator_of_notMem (fun h => hp h.1) _
    simp_rw [h1]
    rw [indicator_of_notMem (show p ∉ {p : Coeff × ℝ | p.2 ∈ Ib} from hp)]
    simp

/-- Incidences of a world lying in a good cell of their block and group. -/
def covInc (μa : Measure (Coeff × ℝ)) (Nb Kb aL q Φf : ℝ) (T kmax : ℕ) : Set (Coeff × ℝ) :=
  {p | ∃ j : ℕ, j < (2 ^ T : ℕ) ∧ p.2 ∈ Ico ((j : ℝ) * q) (j * q + q) ∧ bddTraj Nb Kb p.1 ∧
    ∃ k ≤ kmax, goodCell μa Nb Kb aL q (j * q) Φf (xBin aL (j * q) p.1) k
      (cellIdx q (j * q) k p.1)}

/-- The constant of the group bound. -/
noncomputable def groupCoef (q Φf φ₀ c₀ : ℝ) (kmax r : ℕ) : ℝ :=
  4 * (8 * q * (30 * 2 ^ r * Φf / (φ₀ * q)) * 2 ^ r * (kmax + r + 3)) / (c₀ * φ₀ * q)

/-- **Uncovered mass of one world at a fixed grid scale.** -/
theorem world_uncovered_le_grid (ν : Measure Coeff) [IsProbabilityMeasure ν]
    {E : Set (Coeff × ℝ)} (hE : MeasurableSet E) (hEt : E ⊆ univ ×ˢ Icc 0 1)
    {Nb Kb : ℝ} (hEn : ∀ p ∈ E, (p.1.1 : ℝ) ≤ Nb) (hbd : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ Kb)
    (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) {aL : ℝ}
    (hlaw : Measure.map (obsL aL) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity f)
    {q Φf φ₀ c₀ Rd : ℝ} (T : ℕ) (hqT : q * 2 ^ T = 1) (haL : 0 < aL) (hqa : q ≤ aL)
    (hKb : 0 ≤ Kb) (hΦf : 0 ≤ Φf) (hφ₀ : 0 < φ₀) (hc₀ : 0 < c₀) (kmax r s : ℕ)
    (hr : Kb + 1 ≤ 2 ^ r)
    (hdens : ∀ j : ℕ, ∀ m : ℤ, ∀ l₀ : Coeff, ∀ w : ℝ, 0 < w →
      ν {l | bddTraj Nb Kb l ∧ xBin aL (j * q) l = m ∧
        l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) (j * q) q l₀ w} ≤
        ENNReal.ofReal (Rd * w ^ 2 / q))
    (hRd : Rd * (q / 2 ^ kmax) ≤ 30 * 2 ^ r * Φf / φ₀) :
    ((ν.prod volume).restrict E) univ ≤
      ((ν.prod volume).restrict E) (covInc ((ν.prod volume).restrict E) Nb Kb aL q Φf T kmax) +
        ENNReal.ofReal φ₀ +
        ((2 * (⌈3 * Kb⌉ + 1) + 1).toNat : ℝ≥0∞) * ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) +
        2 * ((ν.prod volume).restrict E) (obsL aL ⁻¹' lowCells
          ((volume.prod Measure.count).withDensity f) (q / 2 ^ (kmax + s + r)) c₀) := by
  classical
  set μa := (ν.prod volume).restrict E with hμa
  have hq : 0 < q := by
    have : (0 : ℝ) < 2 ^ T := by positivity
    by_contra h; push_neg at h; nlinarith
  set c₁ : ℤ := ⌈3 * Kb⌉ + 1 with hc₁
  have hc₁nn : 0 ≤ c₁ := by
    have h3 : (0 : ℝ) ≤ 3 * Kb := by positivity
    have := Int.ceil_nonneg h3
    omega
  set low := obsL aL ⁻¹' lowCells ((volume.prod Measure.count).withDensity f)
    (q / 2 ^ (kmax + s + r)) c₀ with hlow
  set Ib : ℕ → Set ℝ := fun j => Ico ((j : ℝ) * q) (j * q + q) with hIb
  set BL : ℕ → ℤ → Set Coeff := fun j m =>
    badLong μa E Nb Kb aL q (j * q) Φf φ₀ m kmax with hBL
  set SH : ℕ → Set Coeff := fun j => {l | ¬ longTraj E (j * q) q φ₀ l} with hSH
  set G : Set (Coeff × ℝ) := {p | p.2 < 1 ∧ ∀ e, |p.1.2 e| ≤ Kb} with hG
  -- the bad set of the probability measure
  have hGc : μa Gᶜ = 0 := by
    have hsub : Gᶜ ⊆ (univ ×ˢ {(1 : ℝ)}) ∪ {p : Coeff × ℝ | 1 < p.2} ∪
        ({l : Coeff | ¬ ∀ e, |l.2 e| ≤ Kb} ×ˢ univ) := by
      intro p hp
      simp only [hG, mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt] at hp
      rcases hp with h | h
      · rcases eq_or_lt_of_le h with h' | h'
        · left; left; exact ⟨mem_univ _, h'.symm⟩
        · left; right; exact h'
      · right; exact ⟨h, mem_univ _⟩
    apply measure_mono_null hsub
    apply measure_union_null (measure_union_null ?_ ?_) ?_
    · exact le_antisymm ((Measure.restrict_le_self _).trans_eq (by
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero])) bot_le
    · rw [hμa, Measure.restrict_apply' hE]
      convert measure_empty (μ := ν.prod volume)
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h hp
      have := (hEt hp).2.2
      linarith
    · refine le_antisymm ((Measure.restrict_le_self _).trans_eq ?_) bot_le
      rw [Measure.prod_prod]
      have : ν {l : Coeff | ¬ ∀ e, |l.2 e| ≤ Kb} = 0 := ae_iff.mp hbd
      rw [this, zero_mul]
  -- decomposition of the uncovered incidences
  have hdecomp : (covInc μa Nb Kb aL q Φf T kmax)ᶜ ∩ (E ∩ G) ⊆
      ⋃ j ∈ Finset.range (2 ^ T), ((SH j ×ˢ Ib j) ∪ ⋃ m : ℤ, (BL j m ×ˢ Ib j)) := by
    rintro ⟨l, t⟩ ⟨hnc, hpE, hpG⟩
    have ht0 : 0 ≤ t := (hEt hpE).2.1
    have ht1 : t < 1 := hpG.1
    set j := ⌊t * 2 ^ T⌋₊ with hj
    have hjT : j < 2 ^ T := by
      rw [hj, Nat.floor_lt (by positivity)]
      push_cast
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) T]
    have htj : t ∈ Ib j := by
      simp only [hIb, mem_Ico]
      have h1 := Nat.floor_le (show 0 ≤ t * 2 ^ T by positivity)
      have h2 := Nat.lt_floor_add_one (t * 2 ^ T)
      rw [← hj] at h1 h2
      have htq : t * 2 ^ T * q = t := by
        rw [mul_assoc, mul_comm ((2 : ℝ) ^ T) q, hqT, mul_one]
      constructor
      · calc (j : ℝ) * q ≤ t * 2 ^ T * q := mul_le_mul_of_nonneg_right h1 hq.le
          _ = t := htq
      · calc t = t * 2 ^ T * q := htq.symm
          _ < ((j : ℝ) + 1) * q := mul_lt_mul_of_pos_right h2 hq
          _ = j * q + q := by ring
    have hbdd : bddTraj Nb Kb l := ⟨hEn _ hpE, hpG.2⟩
    have hng : ¬ ∃ k ≤ kmax, goodCell μa Nb Kb aL q (j * q) Φf (xBin aL (j * q) l) k
        (cellIdx q (j * q) k l) := by
      intro hg
      exact hnc ⟨j, hjT, htj, hbdd, hg⟩
    refine mem_biUnion (Finset.mem_range.mpr hjT) ?_
    by_cases hlong : longTraj E (j * q) q φ₀ l
    · right
      exact mem_iUnion.mpr ⟨xBin aL (j * q) l, ⟨hbdd, rfl, hng, hlong⟩, htj⟩
    · left
      exact ⟨hlong, htj⟩
  -- measurability
  have hlowm : MeasurableSet low :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL aL
      (measurableSet_lowCells _ (by positivity) c₀)
  have hBLm : ∀ j m, MeasurableSet (BL j m) := fun j m =>
    measurableSet_badLong _ hE _ _ _ _ _ _ _ m kmax
  have hIbm : ∀ j, MeasurableSet (Ib j) := fun j => measurableSet_Ico
  -- per-group bounds
  have hgroup : ∀ j ∈ Finset.range (2 ^ T), ∀ m : ℤ, μa (BL j m ×ˢ Ib j) ≤
      ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) *
        μa {p | p.2 ∈ Ib j ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c₁) (m + c₁)} +
      2 * μa ((BL j m ×ˢ Ib j) ∩ low) := by
    intro j hj m
    have hj' : (j : ℝ) * q + q ≤ 1 := by
      have : (j : ℝ) + 1 ≤ 2 ^ T := by exact_mod_cast (Finset.mem_range.mp hj)
      nlinarith
    exact group_bad_mass_final ν hE f hlaw haL hq hqa hKb hΦf hφ₀ hc₀ j hj' m kmax r s hr
      (hdens j m) hRd
  -- the uncovered part
  have hμa1 : μa univ ≤ 1 := by
    rw [hμa, Measure.restrict_apply_univ]
    calc (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEt
      _ = 1 := by rw [Measure.prod_prod, Real.volume_Icc]; simp
  have hEc : μa Eᶜ = 0 := by
    rw [hμa, Measure.restrict_apply' hE, compl_inter_self, measure_empty]
  have hU : μa (covInc μa Nb Kb aL q Φf T kmax)ᶜ ≤
      ∑ j ∈ Finset.range (2 ^ T), (μa (SH j ×ˢ Ib j) + ∑' m : ℤ, μa (BL j m ×ˢ Ib j)) := by
    calc μa (covInc μa Nb Kb aL q Φf T kmax)ᶜ
        ≤ μa ((covInc μa Nb Kb aL q Φf T kmax)ᶜ ∩ (E ∩ G)) +
          μa ((covInc μa Nb Kb aL q Φf T kmax)ᶜ \ (E ∩ G)) := measure_le_inter_add_diff _ _ _
      _ ≤ μa (⋃ j ∈ Finset.range (2 ^ T), ((SH j ×ˢ Ib j) ∪ ⋃ m : ℤ, (BL j m ×ˢ Ib j))) + 0 := by
          refine add_le_add (measure_mono hdecomp) (le_of_eq ?_)
          apply measure_mono_null (t := Eᶜ ∪ Gᶜ)
          · intro p hp
            simp only [mem_diff, mem_inter_iff, not_and_or] at hp
            rcases hp.2 with h | h
            · exact Or.inl h
            · exact Or.inr h
          · exact measure_union_null hEc hGc
      _ ≤ ∑ j ∈ Finset.range (2 ^ T), μa ((SH j ×ˢ Ib j) ∪ ⋃ m : ℤ, (BL j m ×ˢ Ib j)) := by
          rw [add_zero]; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (2 ^ T), (μa (SH j ×ˢ Ib j) + ∑' m : ℤ, μa (BL j m ×ˢ Ib j)) := by
          gcongr with j hj
          exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
  -- short trajectories
  have hshort : ∑ j ∈ Finset.range (2 ^ T), μa (SH j ×ˢ Ib j) ≤ ENNReal.ofReal φ₀ := by
    calc ∑ j ∈ Finset.range (2 ^ T), μa (SH j ×ˢ Ib j)
        ≤ ∑ _j ∈ Finset.range (2 ^ T), ENNReal.ofReal (φ₀ * q) := by
          gcongr with j hj
          exact short_mass_le ν hE (j * q) q φ₀
      _ = ENNReal.ofReal φ₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          linear_combination φ₀ * hqT
  -- strips
  have hstrips : ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ,
      μa {p | p.2 ∈ Ib j ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c₁) (m + c₁)} ≤
      ((2 * c₁ + 1).toNat : ℝ≥0∞) := by
    calc ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ,
          μa {p | p.2 ∈ Ib j ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c₁) (m + c₁)}
        = ∑ j ∈ Finset.range (2 ^ T), ((2 * c₁ + 1).toNat : ℝ≥0∞) * μa {p | p.2 ∈ Ib j} := by
          apply Finset.sum_congr rfl
          intro j _
          exact tsum_strip_le μa aL (Ib j) (hIbm j) hc₁nn
      _ = ((2 * c₁ + 1).toNat : ℝ≥0∞) * μa (⋃ j ∈ Finset.range (2 ^ T), {p | p.2 ∈ Ib j}) := by
          rw [← Finset.mul_sum, measure_biUnion_finset]
          · intro i _ j _ hij
            simp only [Function.onFun]
            rw [Set.disjoint_left]
            rintro p hpi hpj
            simp only [hIb, mem_ofPred_eq, mem_Ico] at hpi hpj
            rcases lt_or_gt_of_ne hij with h | h
            · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
              nlinarith
            · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
              nlinarith
          · exact fun j _ => measurable_snd (hIbm j)
      _ ≤ ((2 * c₁ + 1).toNat : ℝ≥0∞) * 1 := by
          gcongr
          exact (measure_mono (subset_univ _)).trans hμa1
      _ = _ := mul_one _
  -- light squares
  have hlight : ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ, μa ((BL j m ×ˢ Ib j) ∩ low) ≤ μa low := by
    have hdm : ∀ j, Pairwise (fun m m' : ℤ => Disjoint ((BL j m ×ˢ Ib j) ∩ low)
        ((BL j m' ×ˢ Ib j) ∩ low)) := by
      intro j m m' hmm
      rw [Set.disjoint_left]
      rintro p ⟨⟨hp1, _⟩, _⟩ ⟨⟨hp1', _⟩, _⟩
      exact hmm (hp1.2.1.symm.trans hp1'.2.1)
    calc ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ, μa ((BL j m ×ˢ Ib j) ∩ low)
        = ∑ j ∈ Finset.range (2 ^ T), μa (⋃ m : ℤ, (BL j m ×ˢ Ib j) ∩ low) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [measure_iUnion (hdm j) fun m => ((hBLm j m).prod (hIbm j)).inter hlowm]
      _ = μa (⋃ j ∈ Finset.range (2 ^ T), ⋃ m : ℤ, (BL j m ×ˢ Ib j) ∩ low) := by
          rw [measure_biUnion_finset]
          · intro i _ j _ hij
            simp only [Function.onFun]
            rw [Set.disjoint_left]
            intro p hpi hpj
            simp only [mem_iUnion] at hpi hpj
            obtain ⟨m, ⟨⟨_, hti⟩, _⟩⟩ := hpi
            obtain ⟨m', ⟨⟨_, htj⟩, _⟩⟩ := hpj
            simp only [hIb, mem_Ico] at hti htj
            rcases lt_or_gt_of_ne hij with h | h
            · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
              nlinarith
            · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
              nlinarith
          · exact fun j _ => MeasurableSet.iUnion fun m =>
              ((hBLm j m).prod (hIbm j)).inter hlowm
      _ ≤ μa low := by
          apply measure_mono
          intro p hp
          simp only [mem_iUnion] at hp
          obtain ⟨_, _, _, hp⟩ := hp
          exact hp.2
  -- assemble
  have hbad : ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ, μa (BL j m ×ˢ Ib j) ≤
      ((2 * c₁ + 1).toNat : ℝ≥0∞) * ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) +
        2 * μa low := by
    calc ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ, μa (BL j m ×ˢ Ib j)
        ≤ ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ,
            (ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) *
              μa {p | p.2 ∈ Ib j ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c₁) (m + c₁)} +
            2 * μa ((BL j m ×ˢ Ib j) ∩ low)) := by
          gcongr with j hj m
          exact hgroup j hj m
      _ = ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) * (∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ,
              μa {p | p.2 ∈ Ib j ∧ ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - c₁) (m + c₁)}) +
            2 * ∑ j ∈ Finset.range (2 ^ T), ∑' m : ℤ, μa ((BL j m ×ˢ Ib j) ∩ low) := by
          simp_rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) * ((2 * c₁ + 1).toNat : ℝ≥0∞) +
            2 * μa low := by gcongr
      _ = _ := by rw [mul_comm]
  calc μa univ ≤ μa (covInc μa Nb Kb aL q Φf T kmax) + μa (covInc μa Nb Kb aL q Φf T kmax)ᶜ :=
        measure_univ_le_add_compl _
    _ ≤ μa (covInc μa Nb Kb aL q Φf T kmax) + (ENNReal.ofReal φ₀ +
          (((2 * c₁ + 1).toNat : ℝ≥0∞) * ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) +
            2 * μa low)) := by
        gcongr
        refine hU.trans ?_
        rw [Finset.sum_add_distrib]
        exact add_le_add hshort hbad
    _ = _ := by ring

/-- **Uncovered mass of one world.**  Letting the grid scale tend to zero. -/
theorem world_uncovered_le (ν : Measure Coeff) [IsProbabilityMeasure ν]
    {E : Set (Coeff × ℝ)} (hE : MeasurableSet E) (hEt : E ⊆ univ ×ˢ Icc 0 1)
    {Nb Kb : ℝ} (hEn : ∀ p ∈ E, (p.1.1 : ℝ) ≤ Nb) (hbd : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ Kb)
    (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) (hf : Measurable f) {aL : ℝ}
    (hlaw : Measure.map (obsL aL) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity f)
    {q Φf φ₀ c₀ Rd : ℝ} (T : ℕ) (hqT : q * 2 ^ T = 1) (haL : 0 < aL) (hqa : q ≤ aL)
    (hKb : 0 ≤ Kb) (hΦf : 0 ≤ Φf) (hφ₀ : 0 < φ₀) (hc₀ : 0 < c₀) (kmax r : ℕ)
    (hr : Kb + 1 ≤ 2 ^ r)
    (hdens : ∀ j : ℕ, ∀ m : ℤ, ∀ l₀ : Coeff, ∀ w : ℝ, 0 < w →
      ν {l | bddTraj Nb Kb l ∧ xBin aL (j * q) l = m ∧
        l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) (j * q) q l₀ w} ≤
        ENNReal.ofReal (Rd * w ^ 2 / q))
    (hRd : Rd * (q / 2 ^ kmax) ≤ 30 * 2 ^ r * Φf / φ₀) :
    ((ν.prod volume).restrict E) univ ≤
      ((ν.prod volume).restrict E) (covInc ((ν.prod volume).restrict E) Nb Kb aL q Φf T kmax) +
        ENNReal.ofReal φ₀ +
        ((2 * (⌈3 * Kb⌉ + 1) + 1).toNat : ℝ≥0∞) * ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r) +
        2 * ((ν.prod volume).restrict E) {p | f (obsL aL p) < ENNReal.ofReal (2 * c₀)} := by
  set μa := (ν.prod volume).restrict E with hμa
  set lam := (volume.prod Measure.count).withDensity f with hlam
  have hq : 0 < q := by
    have : (0 : ℝ) < 2 ^ T := by positivity
    by_contra h; push_neg at h; nlinarith
  set X := μa (covInc μa Nb Kb aL q Φf T kmax) + ENNReal.ofReal φ₀ +
    ((2 * (⌈3 * Kb⌉ + 1) + 1).toNat : ℝ≥0∞) * ENNReal.ofReal (groupCoef q Φf φ₀ c₀ kmax r)
    with hX
  set Y := μa {p | f (obsL aL p) < ENNReal.ofReal (2 * c₀)} with hY
  set δ : ℕ → ℝ := fun s => q / 2 ^ (kmax + s + r) with hδ
  have hδpos : ∀ s, 0 < δ s := fun s => by positivity
  have hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℕ => q / 2 ^ (kmax + r) * (1 / 2) ^ s) Filter.atTop
        (𝓝 (q / 2 ^ (kmax + r) * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [mul_zero] at h
    refine h.congr fun s => ?_
    rw [hδ]
    simp only
    rw [show kmax + s + r = (kmax + r) + s by omega, pow_add, one_div, inv_pow]
    field_simp
    ring
  -- the light-square mass splits into the density exception and a vanishing part
  set Z : ℕ → ℝ≥0∞ := fun s => lam (lowCells lam (δ s) c₀ ∩ {p | ENNReal.ofReal (2 * c₀) ≤ f p})
    with hZ
  have hfin : ∫⁻ p, f p ∂(volume.prod Measure.count) ≠ ⊤ := by
    have h1 : ∫⁻ p, f p ∂(volume.prod Measure.count) = lam univ := by
      rw [hlam, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1, ← hlaw, Measure.map_apply
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL aL)
      MeasurableSet.univ, preimage_univ]
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hμa, Measure.restrict_apply_univ]
    calc (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEt
      _ = 1 := by rw [Measure.prod_prod, Real.volume_Icc]; simp
  have hZlim : Filter.Tendsto Z Filter.atTop (𝓝 0) :=
    tendsto_lowCells_dense f hf hfin (by positivity : (0 : ℝ) < c₀) δ hδpos hδlim
  have hm : Measurable (obsL aL) :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL aL
  have hmap : ∀ S, MeasurableSet S → lam S = μa (obsL aL ⁻¹' S) := by
    intro S hS
    rw [← Measure.map_apply hm hS, hlaw]
  have hlowle : ∀ s, μa (obsL aL ⁻¹' lowCells lam (δ s) c₀) ≤ Y + Z s := by
    intro s
    have hlowm : MeasurableSet (lowCells lam (δ s) c₀) := measurableSet_lowCells lam (hδpos s) c₀
    have hfm : MeasurableSet {p : (Fin 2 → ℝ) × ℤ | f p < ENNReal.ofReal (2 * c₀)} :=
      measurableSet_lt hf measurable_const
    calc μa (obsL aL ⁻¹' lowCells lam (δ s) c₀) = lam (lowCells lam (δ s) c₀) :=
          (hmap _ hlowm).symm
      _ ≤ lam ({p | f p < ENNReal.ofReal (2 * c₀)} ∪
            (lowCells lam (δ s) c₀ ∩ {p | ENNReal.ofReal (2 * c₀) ≤ f p})) := by
          apply measure_mono
          intro p hp
          by_cases h : f p < ENNReal.ofReal (2 * c₀)
          · exact Or.inl h
          · exact Or.inr ⟨hp, not_lt.mp h⟩
      _ ≤ lam {p | f p < ENNReal.ofReal (2 * c₀)} + Z s := measure_union_le _ _
      _ = Y + Z s := by
          rw [hY, hmap _ hfm]
          rfl
  have hbound : ∀ s, μa univ ≤ X + 2 * (Y + Z s) := by
    intro s
    have h := world_uncovered_le_grid ν hE hEt hEn hbd f hlaw T hqT haL hqa hKb hΦf hφ₀ hc₀
      kmax r s hr hdens hRd
    refine h.trans ?_
    rw [hX]
    gcongr
    exact hlowle s
  have hlim : Filter.Tendsto (fun s => X + 2 * (Y + Z s)) Filter.atTop (𝓝 (X + 2 * (Y + 0))) := by
    refine tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hZlim)
      (Or.inr (by norm_num)))
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

end Submission.Obl.k4_scalar_initial_true_horizon
