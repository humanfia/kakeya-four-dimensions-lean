import Submission.Obl.k4_scalar_initial_true_horizon.InitialSlab

/-!
# Planar collision energy of a weighted family of affine traces

A finite measure `ν` on (abstract) traces `t ↦ y₀ l + t * s l` is observed on a grid of
`δ`-cells in time and space.  The squared cell masses are bounded by `δ` times the expected
closeness time of two independent traces, and the latter by dyadic plank masses.  This is
the planar Córdoba `L²` estimate used for the initial horizon bound.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The trace of `l` at time `t`. -/
def trace (y₀ s : α → ℝ) (l : α) (t : ℝ) : ℝ := y₀ l + t * s l

/-- Traces staying within `w` of the trace of `l₀` on the whole interval. -/
def plank (y₀ s : α → ℝ) (t₀ q : ℝ) (l₀ : α) (w : ℝ) : Set α :=
  {l | ∀ t ∈ Icc t₀ (t₀ + q), |trace y₀ s l₀ t - trace y₀ s l t| ≤ w}

theorem measurableSet_plank (y₀ s : α → ℝ) (hy₀ : Measurable y₀) (hs : Measurable s)
    (t₀ q : ℝ) (hq : 0 ≤ q) (l₀ : α) (w : ℝ) :
    MeasurableSet (plank y₀ s t₀ q l₀ w) := by
  have heq : plank y₀ s t₀ q l₀ w =
      {l | |(y₀ l₀ - y₀ l) + t₀ * (s l₀ - s l)| ≤ w ∧
        |(y₀ l₀ - y₀ l) + (t₀ + q) * (s l₀ - s l)| ≤ w} := by
    ext l
    simp only [plank, trace, mem_ofPred_eq]
    have h := affine_abs_le_on_Icc_iff (y₀ l₀ - y₀ l) (s l₀ - s l) t₀ q w hq
    have hrw : ∀ t, y₀ l₀ + t * s l₀ - (y₀ l + t * s l) = (y₀ l₀ - y₀ l) + t * (s l₀ - s l) :=
      fun t => by ring
    simp only [hrw]
    exact h
  rw [heq]
  have h1 : Measurable (fun l => |(y₀ l₀ - y₀ l) + t₀ * (s l₀ - s l)|) := by fun_prop
  have h2 : Measurable (fun l => |(y₀ l₀ - y₀ l) + (t₀ + q) * (s l₀ - s l)|) := by fun_prop
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const)

/-- Time spent by a trace in a time cell `τ` and a space cell `c`. -/
noncomputable def cellTime (y₀ s : α → ℝ) (τ c : Set ℝ) (l : α) : ℝ≥0∞ :=
  volume {t ∈ τ | trace y₀ s l t ∈ c}

theorem measurable_cellTime (y₀ s : α → ℝ) (hy₀ : Measurable y₀) (hs : Measurable s)
    {τ c : Set ℝ} (hτ : MeasurableSet τ) (hc : MeasurableSet c) :
    Measurable (cellTime y₀ s τ c) := by
  have hS : MeasurableSet {p : α × ℝ | p.2 ∈ τ ∧ trace y₀ s p.1 p.2 ∈ c} := by
    apply (measurable_snd hτ).inter
    have : Measurable (fun p : α × ℝ => trace y₀ s p.1 p.2) := by
      unfold trace; fun_prop
    exact this hc
  exact measurable_measure_prodMk_left hS

/-- The space cells. -/
def yCell (δ : ℝ) (i : ℤ) : Set ℝ := Ico (i * δ) ((i + 1) * δ)

theorem yCell_disjoint {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun i j : ℤ => Disjoint (yCell δ i) (yCell δ j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : ⌊x / δ⌋ = i := by
    rw [Int.floor_eq_iff]
    simp only [yCell, mem_Ico] at hxi
    constructor
    · rw [le_div_iff₀ hδ]; exact hxi.1
    · rw [div_lt_iff₀ hδ]; exact hxi.2
  have hj : ⌊x / δ⌋ = j := by
    rw [Int.floor_eq_iff]
    simp only [yCell, mem_Ico] at hxj
    constructor
    · rw [le_div_iff₀ hδ]; exact hxj.1
    · rw [div_lt_iff₀ hδ]; exact hxj.2
  exact hij (hi.symm.trans hj)

theorem mem_yCell_floor {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : x ∈ yCell δ ⌊x / δ⌋ := by
  simp only [yCell, mem_Ico]
  constructor
  · have := Int.floor_le (x / δ)
    rwa [le_div_iff₀ hδ] at this
  · have := Int.lt_floor_add_one (x / δ)
    rwa [div_lt_iff₀ hδ] at this

theorem iUnion_yCell {δ : ℝ} (hδ : 0 < δ) : (⋃ i : ℤ, yCell δ i) = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨_, mem_yCell_floor hδ x⟩

theorem yCell_close {δ : ℝ} {i : ℤ} {x x' : ℝ} (hx : x ∈ yCell δ i) (hx' : x' ∈ yCell δ i) :
    |x - x'| < δ := by
  simp only [yCell, mem_Ico] at hx hx'
  rw [abs_lt]
  constructor <;> nlinarith [hx.1, hx.2, hx'.1, hx'.2]

omit [MeasurableSpace α] in
/-- The pair bound for one time cell: the cell-by-cell product of occupation times is at
most `δ` times the closeness time inside the cell. -/
theorem pair_cell_bound (y₀ s : α → ℝ) {δ K : ℝ} (hδ : 0 < δ) {τ : Set ℝ}
    (hτm : MeasurableSet τ) (hτvol : volume τ ≤ ENNReal.ofReal δ)
    (hτdiam : ∀ t ∈ τ, ∀ t' ∈ τ, |t - t'| < δ) (l l' : α) (hl' : |s l'| ≤ K) :
    ∑' i : ℤ, cellTime y₀ s τ (yCell δ i) l * cellTime y₀ s τ (yCell δ i) l' ≤
      ENNReal.ofReal δ *
        volume {t ∈ τ | |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
  have hterm : ∀ i : ℤ, cellTime y₀ s τ (yCell δ i) l * cellTime y₀ s τ (yCell δ i) l' ≤
      ENNReal.ofReal δ * volume {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
        |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
    intro i
    by_cases h0 : cellTime y₀ s τ (yCell δ i) l' = 0
    · rw [h0, mul_zero]; exact bot_le
    · have hne : {t ∈ τ | trace y₀ s l' t ∈ yCell δ i}.Nonempty := by
        by_contra he
        rw [Set.not_nonempty_iff_eq_empty] at he
        exact h0 (by simp only [cellTime, he, measure_empty])
      obtain ⟨t', ht'τ, ht'c⟩ := hne
      have hsub : {t ∈ τ | trace y₀ s l t ∈ yCell δ i} ⊆
          {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
            |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
        rintro t ⟨htτ, htc⟩
        refine ⟨htτ, htc, ?_⟩
        have h1 : |trace y₀ s l t - trace y₀ s l' t'| < δ := yCell_close htc ht'c
        have h2 : |trace y₀ s l' t' - trace y₀ s l' t| ≤ K * δ := by
          simp only [trace]
          have : y₀ l' + t' * s l' - (y₀ l' + t * s l') = (t' - t) * s l' := by ring
          rw [this, abs_mul]
          have := (hτdiam t' ht'τ t htτ).le
          calc |t' - t| * |s l'| ≤ δ * K := by gcongr
            _ = K * δ := by ring
        calc |trace y₀ s l t - trace y₀ s l' t|
            = |(trace y₀ s l t - trace y₀ s l' t') + (trace y₀ s l' t' - trace y₀ s l' t)| := by
              ring_nf
          _ ≤ |trace y₀ s l t - trace y₀ s l' t'| + |trace y₀ s l' t' - trace y₀ s l' t| :=
              abs_add_le _ _
          _ < δ + K * δ := by linarith
          _ = (K + 1) * δ := by ring
      have hl'le : cellTime y₀ s τ (yCell δ i) l' ≤ ENNReal.ofReal δ :=
        (measure_mono (fun t ht => ht.1)).trans hτvol
      calc cellTime y₀ s τ (yCell δ i) l * cellTime y₀ s τ (yCell δ i) l'
          ≤ volume {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
              |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} * ENNReal.ofReal δ :=
            mul_le_mul' (measure_mono hsub) hl'le
        _ = _ := mul_comm _ _
  calc ∑' i : ℤ, cellTime y₀ s τ (yCell δ i) l * cellTime y₀ s τ (yCell δ i) l'
      ≤ ∑' i : ℤ, ENNReal.ofReal δ * volume {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
          |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal δ * ∑' i : ℤ, volume {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
          |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal δ *
          volume {t ∈ τ | |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
      gcongr
      have hmeasA : ∀ i : ℤ, MeasurableSet {t ∈ τ | trace y₀ s l t ∈ yCell δ i ∧
          |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
        intro i
        refine hτm.inter ?_
        apply MeasurableSet.inter
        · have : Measurable (fun t : ℝ => trace y₀ s l t) := by unfold trace; fun_prop
          exact this measurableSet_Ico
        · have : Measurable (fun t : ℝ => |trace y₀ s l t - trace y₀ s l' t|) := by
            unfold trace; fun_prop
          exact measurableSet_lt this measurable_const
      rw [← measure_iUnion]
      · apply measure_mono
        intro t ht
        obtain ⟨i, hi⟩ := mem_iUnion.mp ht
        exact ⟨hi.1, hi.2.2⟩
      · intro i j hij
        exact Set.disjoint_left.mpr (fun t hti htj =>
          Set.disjoint_left.mp (yCell_disjoint hδ hij) hti.2.1 htj.2.1)
      · exact hmeasA

omit [MeasurableSpace α] in
open Classical in
/-- Pointwise: the summed cell products of two traces are bounded by `δ` times the dyadic
plank sum of the second trace around the first one. -/
theorem pair_total_bound (y₀ s : α → ℝ) {t₀ q δ K ε : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hε : 0 < ε) (hKδ : (K + 1) * δ ≤ ε) (n : ℕ) (htop : ε + 2 * K * q ≤ 2 ^ (n + 1) * ε)
    (τ : ℕ → Set ℝ) (R : ℕ) (hτm : ∀ i, MeasurableSet (τ i))
    (hτvol : ∀ i, volume (τ i) ≤ ENNReal.ofReal δ)
    (hτdiam : ∀ i, ∀ t ∈ τ i, ∀ t' ∈ τ i, |t - t'| < δ)
    (hτsub : ∀ i < R, τ i ⊆ Icc t₀ (t₀ + q)) (hτdisj : Pairwise (fun i j => Disjoint (τ i) (τ j)))
    (l l' : α) (hl : |s l| ≤ K) (hl' : |s l'| ≤ K) :
    ∑ i ∈ Finset.range R, ∑' i' : ℤ,
        cellTime y₀ s (τ i) (yCell δ i') l * cellTime y₀ s (τ i) (yCell δ i') l' ≤
      ENNReal.ofReal δ * ∑ i ∈ Finset.range (n + 1),
        (plank y₀ s t₀ q l (2 ^ (i + 1) * ε)).indicator
          (fun _ => ENNReal.ofReal (4 * q / 2 ^ i)) l' := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hl
  calc ∑ i ∈ Finset.range R, ∑' i' : ℤ,
        cellTime y₀ s (τ i) (yCell δ i') l * cellTime y₀ s (τ i) (yCell δ i') l'
      ≤ ∑ i ∈ Finset.range R, ENNReal.ofReal δ *
          volume {t ∈ τ i | |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} :=
        Finset.sum_le_sum fun i _ =>
          pair_cell_bound y₀ s hδ (hτm i) (hτvol i) (hτdiam i) l l' hl'
    _ = ENNReal.ofReal δ * ∑ i ∈ Finset.range R,
          volume {t ∈ τ i | |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal δ *
          volume {t ∈ Icc t₀ (t₀ + q) | |trace y₀ s l t - trace y₀ s l' t| < ε} := by
      gcongr
      have hmeas : ∀ i, MeasurableSet
          {t ∈ τ i | |trace y₀ s l t - trace y₀ s l' t| < (K + 1) * δ} := by
        intro i
        refine (hτm i).inter ?_
        have : Measurable (fun t : ℝ => |trace y₀ s l t - trace y₀ s l' t|) := by
          unfold trace; fun_prop
        exact measurableSet_lt this measurable_const
      rw [← measure_biUnion_finset]
      · apply measure_mono
        intro t ht
        simp only [mem_iUnion, Finset.mem_range] at ht
        obtain ⟨i, hiR, hti, hlt⟩ := ht
        exact ⟨hτsub i hiR hti, lt_of_lt_of_le hlt hKδ⟩
      · intro i _ j _ hij
        exact Set.disjoint_left.mpr (fun t hti htj =>
          Set.disjoint_left.mp (hτdisj hij) hti.1 htj.1)
      · exact fun i _ => hmeas i
    _ ≤ ENNReal.ofReal δ * ∑ i ∈ Finset.range (n + 1),
          (plank y₀ s t₀ q l (2 ^ (i + 1) * ε)).indicator
            (fun _ => ENNReal.ofReal (4 * q / 2 ^ i)) l' := by
      gcongr
      have hσ : |s l - s l'| ≤ 2 * K := by
        calc |s l - s l'| ≤ |s l| + |s l'| := abs_sub _ _
          _ ≤ 2 * K := by linarith
      have h := near_time_le_dyadic_sum (y₀ l - y₀ l') (s l - s l') t₀ q ε K n hq hε hσ htop
      have hrw : ∀ t, trace y₀ s l t - trace y₀ s l' t = (y₀ l - y₀ l') + t * (s l - s l') :=
        fun t => by simp only [trace]; ring
      simp only [hrw]
      refine h.trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro i _
      simp only [Set.indicator, plank, mem_ofPred_eq, hrw]

/-- **Planar collision energy.**  For a finite measure on traces with slopes bounded by
`K` and prescribed dyadic plank masses `F i`, the squared cell masses of the occupation
measure are bounded by `δ ν(univ)` times the dyadic plank sum. -/
theorem collision_energy_bound (ν : Measure α) [IsFiniteMeasure ν] (y₀ s : α → ℝ)
    (hy₀ : Measurable y₀) (hs : Measurable s) {t₀ q δ K ε : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hε : 0 < ε) (hKδ : (K + 1) * δ ≤ ε) (n : ℕ) (htop : ε + 2 * K * q ≤ 2 ^ (n + 1) * ε)
    (hslope : ∀ᵐ l ∂ν, |s l| ≤ K)
    (τ : ℕ → Set ℝ) (R : ℕ) (hτm : ∀ i, MeasurableSet (τ i))
    (hτvol : ∀ i, volume (τ i) ≤ ENNReal.ofReal δ)
    (hτdiam : ∀ i, ∀ t ∈ τ i, ∀ t' ∈ τ i, |t - t'| < δ)
    (hτsub : ∀ i < R, τ i ⊆ Icc t₀ (t₀ + q)) (hτdisj : Pairwise (fun i j => Disjoint (τ i) (τ j)))
    (F : ℕ → ℝ≥0∞)
    (hplank : ∀ l₀, |s l₀| ≤ K → ∀ i ≤ n, ν (plank y₀ s t₀ q l₀ (2 ^ (i + 1) * ε)) ≤ F i) :
    ∑ i ∈ Finset.range R, ∑' i' : ℤ, (∫⁻ l, cellTime y₀ s (τ i) (yCell δ i') l ∂ν) ^ 2 ≤
      ENNReal.ofReal δ * ν univ *
        ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (4 * q / 2 ^ i) * F i := by
  set g : ℕ → ℤ → α → ℝ≥0∞ := fun i i' => cellTime y₀ s (τ i) (yCell δ i') with hg
  have hgm : ∀ i i', Measurable (g i i') := fun i i' =>
    measurable_cellTime y₀ s hy₀ hs (hτm i) measurableSet_Ico
  set S : ℝ≥0∞ := ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (4 * q / 2 ^ i) * F i with hS
  -- square as a double integral
  have hsq : ∀ i i', (∫⁻ l, g i i' l ∂ν) ^ 2 = ∫⁻ l, ∫⁻ l', g i i' l * g i i' l' ∂ν ∂ν := by
    intro i i'
    rw [lintegral_lintegral_mul (hgm i i').aemeasurable (hgm i i').aemeasurable, pow_two]
  -- inner bound
  have hinner : ∀ᵐ l ∂ν, ∫⁻ l', ∑ i ∈ Finset.range R, ∑' i' : ℤ, g i i' l * g i i' l' ∂ν ≤
      ENNReal.ofReal δ * S := by
    filter_upwards [hslope] with l hl
    calc ∫⁻ l', ∑ i ∈ Finset.range R, ∑' i' : ℤ, g i i' l * g i i' l' ∂ν
        ≤ ∫⁻ l', ENNReal.ofReal δ * ∑ i ∈ Finset.range (n + 1),
            (plank y₀ s t₀ q l (2 ^ (i + 1) * ε)).indicator
              (fun _ => ENNReal.ofReal (4 * q / 2 ^ i)) l' ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hslope] with l' hl'
          exact pair_total_bound y₀ s hq hδ hε hKδ n htop τ R hτm hτvol hτdiam hτsub hτdisj
            l l' hl hl'
      _ = ENNReal.ofReal δ * ∑ i ∈ Finset.range (n + 1),
            ENNReal.ofReal (4 * q / 2 ^ i) * ν (plank y₀ s t₀ q l (2 ^ (i + 1) * ε)) := by
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ =>
            (measurable_const.indicator (measurableSet_plank y₀ s hy₀ hs t₀ q hq.le l _)))]
          congr 1
          rw [lintegral_finsetSum _ fun i _ =>
            (measurable_const.indicator (measurableSet_plank y₀ s hy₀ hs t₀ q hq.le l _))]
          apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_indicator_const (measurableSet_plank y₀ s hy₀ hs t₀ q hq.le l _)]
      _ ≤ ENNReal.ofReal δ * S := by
          rw [hS]
          gcongr with i hi
          exact hplank l hl i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  -- exchange sums and integrals
  have hexch : ∑ i ∈ Finset.range R, ∑' i' : ℤ, ∫⁻ l, ∫⁻ l', g i i' l * g i i' l' ∂ν ∂ν =
      ∫⁻ l, ∫⁻ l', ∑ i ∈ Finset.range R, ∑' i' : ℤ, g i i' l * g i i' l' ∂ν ∂ν := by
    have hm2 : ∀ i i' l, Measurable (fun l' => g i i' l * g i i' l') :=
      fun i i' l => measurable_const.mul (hgm i i')
    have hm1 : ∀ i i', Measurable (fun l => ∫⁻ l', g i i' l * g i i' l' ∂ν) := by
      intro i i'
      have : (fun l => ∫⁻ l', g i i' l * g i i' l' ∂ν) =
          fun l => g i i' l * ∫⁻ l', g i i' l' ∂ν := by
        funext l; rw [lintegral_const_mul _ (hgm i i')]
      rw [this]; exact (hgm i i').mul_const _
    have hinnerEq : ∀ l, ∫⁻ l', ∑ i ∈ Finset.range R, ∑' i' : ℤ, g i i' l * g i i' l' ∂ν =
        ∑ i ∈ Finset.range R, ∑' i' : ℤ, ∫⁻ l', g i i' l * g i i' l' ∂ν := by
      intro l
      rw [lintegral_finsetSum _ fun i _ => Measurable.ennreal_tsum fun i' => hm2 i i' l]
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_tsum fun i' => (hm2 i i' l).aemeasurable]
    simp_rw [hinnerEq]
    rw [lintegral_finsetSum _ fun i _ => Measurable.ennreal_tsum fun i' => hm1 i i']
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_tsum fun i' => (hm1 i i').aemeasurable]
  calc ∑ i ∈ Finset.range R, ∑' i' : ℤ, (∫⁻ l, cellTime y₀ s (τ i) (yCell δ i') l ∂ν) ^ 2
      = ∑ i ∈ Finset.range R, ∑' i' : ℤ, ∫⁻ l, ∫⁻ l', g i i' l * g i i' l' ∂ν ∂ν := by
        apply Finset.sum_congr rfl; intro i _; congr 1; funext i'; exact hsq i i'
    _ = ∫⁻ l, ∫⁻ l', ∑ i ∈ Finset.range R, ∑' i' : ℤ, g i i' l * g i i' l' ∂ν ∂ν := hexch
    _ ≤ ∫⁻ _l, ENNReal.ofReal δ * S ∂ν := lintegral_mono_ae hinner
    _ = ENNReal.ofReal δ * ν univ * S := by rw [lintegral_const]; ring

end Submission.Obl.k4_scalar_initial_true_horizon
