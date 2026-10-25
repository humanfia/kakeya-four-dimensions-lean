import Mathlib

/-!
# Grid squares of small original mass

For a finite measure `λ = (vol × count).withDensity f` on observations
`(Fin 2 → ℝ) × ℤ`, the observations whose `δ`-grid square (at their own hidden bin)
has mass below `c δ²` while `f ≥ 2c` carry vanishing mass as `δ → 0`.  This is
Lebesgue's differentiation theorem (Mathlib's Vitali family of closed sup-norm balls)
applied slice by slice.  No quantitative flattening is needed.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- The half-open grid square of side `δ` containing `z`. -/
def gridSquare (δ : ℝ) (z : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi fun i => Ico (⌊z i / δ⌋ * δ) ((⌊z i / δ⌋ + 1) * δ)

/-- The centre of the grid square containing `z`. -/
noncomputable def gridCenter (δ : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => (⌊z i / δ⌋ + 1 / 2) * δ

theorem mem_gridSquare {δ : ℝ} (hδ : 0 < δ) (z : Fin 2 → ℝ) : z ∈ gridSquare δ z := by
  intro i _
  constructor
  · have := Int.floor_le (z i / δ)
    rwa [le_div_iff₀ hδ] at this
  · have := Int.lt_floor_add_one (z i / δ)
    rwa [div_lt_iff₀ hδ] at this

theorem gridSquare_eq_of_mem {δ : ℝ} (hδ : 0 < δ) {z z' : Fin 2 → ℝ}
    (h : z' ∈ gridSquare δ z) : gridSquare δ z' = gridSquare δ z := by
  have hfl : ∀ i, ⌊z' i / δ⌋ = ⌊z i / δ⌋ := by
    intro i
    have hi := h i (mem_univ i)
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hδ]; exact hi.1
    · rw [div_lt_iff₀ hδ]; exact hi.2
  simp only [gridSquare, hfl]

theorem measurableSet_gridSquare (δ : ℝ) (z : Fin 2 → ℝ) : MeasurableSet (gridSquare δ z) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem gridSquare_subset_closedBall {δ : ℝ} (hδ : 0 < δ) (z : Fin 2 → ℝ) :
    gridSquare δ z ⊆ closedBall (gridCenter δ z) (δ / 2) := by
  intro x hx
  rw [closedBall_pi _ (by positivity)]
  intro i _
  have hi : x i ∈ Ico (⌊z i / δ⌋ * δ) ((⌊z i / δ⌋ + 1) * δ) := hx i (mem_univ i)
  show x i ∈ closedBall (gridCenter δ z i) (δ / 2)
  rw [Real.closedBall_eq_Icc]
  simp only [gridCenter]
  constructor <;> nlinarith [hi.1, hi.2]

theorem volume_gridSquare {δ : ℝ} (hδ : 0 < δ) (z : Fin 2 → ℝ) :
    volume (gridSquare δ z) = ENNReal.ofReal (δ ^ 2) := by
  rw [gridSquare, Real.volume_pi_Ico]
  simp only [Fin.prod_univ_two]
  rw [← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

theorem volume_closedBall_gridCenter {δ : ℝ} (hδ : 0 < δ) (z : Fin 2 → ℝ) :
    volume (closedBall (gridCenter δ z) (δ / 2)) = ENNReal.ofReal (δ ^ 2) := by
  rw [Real.volume_pi_closedBall _ (by positivity)]
  congr 1
  simp only [Fintype.card_fin]
  ring

theorem mem_closedBall_gridCenter {δ : ℝ} (hδ : 0 < δ) (z : Fin 2 → ℝ) :
    z ∈ closedBall (gridCenter δ z) (1 * (δ / 2)) := by
  rw [one_mul]
  exact gridSquare_subset_closedBall hδ z (mem_gridSquare hδ z)

/-- For a measure absolutely continuous with respect to volume, grid squares and their
circumscribed closed balls have the same mass. -/
theorem measure_gridSquare_eq_ball (ρ : Measure (Fin 2 → ℝ)) (hρ : ρ ≪ volume) {δ : ℝ}
    (hδ : 0 < δ) (z : Fin 2 → ℝ) :
    ρ (gridSquare δ z) = ρ (closedBall (gridCenter δ z) (δ / 2)) := by
  have hsub := gridSquare_subset_closedBall hδ z
  have hmeas : MeasurableSet (gridSquare δ z) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hnull : volume (closedBall (gridCenter δ z) (δ / 2) \ gridSquare δ z) = 0 := by
    rw [measure_diff hsub hmeas.nullMeasurableSet (by
      rw [volume_gridSquare hδ]; exact ENNReal.ofReal_ne_top),
      volume_gridSquare hδ, volume_closedBall_gridCenter hδ, tsub_self]
  have hρnull := hρ hnull
  apply le_antisymm (measure_mono hsub)
  calc ρ (closedBall (gridCenter δ z) (δ / 2))
      = ρ (gridSquare δ z ∪ (closedBall (gridCenter δ z) (δ / 2) \ gridSquare δ z)) := by
        rw [union_diff_cancel hsub]
    _ ≤ ρ (gridSquare δ z) + ρ (closedBall (gridCenter δ z) (δ / 2) \ gridSquare δ z) :=
        measure_union_le _ _
    _ = ρ (gridSquare δ z) := by rw [hρnull, add_zero]

/-- The mass of `S × {m}` is the mass of `S` for the density slice at `m`. -/
theorem withDensity_prod_singleton (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) (hf : Measurable f)
    {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) (m : ℤ) :
    ((volume.prod Measure.count).withDensity f) (S ×ˢ {m}) =
      (volume.withDensity (fun z => f (z, m))) S := by
  rw [withDensity_apply _ (hS.prod (measurableSet_singleton m)),
    withDensity_apply _ hS, ← lintegral_indicator (hS.prod (measurableSet_singleton m)),
    ← lintegral_indicator hS,
    lintegral_prod _ ((hf.indicator (hS.prod (measurableSet_singleton m))).aemeasurable)]
  congr 1
  funext z
  rw [lintegral_count]
  classical
  have : ∀ m' : ℤ, (S ×ˢ {m}).indicator f (z, m') =
      if m' = m then S.indicator (fun z => f (z, m)) z else 0 := by
    intro m'
    by_cases hm : m' = m
    · subst hm
      by_cases hz : z ∈ S
      · simp [Set.indicator, hz]
      · simp [Set.indicator, hz]
    · simp [Set.indicator, hm]
  simp_rw [this]
  exact tsum_ite_eq m _

/-- Observations whose grid square (at their hidden bin) has small mass. -/
def lowCells (lam : Measure ((Fin 2 → ℝ) × ℤ)) (δ c : ℝ) : Set ((Fin 2 → ℝ) × ℤ) :=
  {p | lam (gridSquare δ p.1 ×ˢ {p.2}) < ENNReal.ofReal (c * δ ^ 2)}

theorem measurableSet_lowCells (lam : Measure ((Fin 2 → ℝ) × ℤ)) {δ : ℝ} (hδ : 0 < δ)
    (c : ℝ) : MeasurableSet (lowCells lam δ c) := by
  let key : (Fin 2 → ℝ) × ℤ → (ℤ × ℤ) × ℤ := fun p => ((⌊p.1 0 / δ⌋, ⌊p.1 1 / δ⌋), p.2)
  have hkey : Measurable key := by
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) measurable_snd
    · exact Int.measurable_floor.comp ((measurable_pi_apply 0).comp measurable_fst |>.div_const _)
    · exact Int.measurable_floor.comp ((measurable_pi_apply 1).comp measurable_fst |>.div_const _)
  let G : (ℤ × ℤ) × ℤ → ℝ≥0∞ := fun k =>
    lam ((Set.univ.pi fun i : Fin 2 =>
      Ico ((if i = 0 then k.1.1 else k.1.2 : ℤ) * δ)
        (((if i = 0 then k.1.1 else k.1.2 : ℤ) + 1) * δ)) ×ˢ {k.2})
  have hG : ∀ p, lam (gridSquare δ p.1 ×ˢ {p.2}) = G (key p) := by
    intro p
    simp only [G, key, gridSquare]
    congr 3
    funext i
    fin_cases i <;> simp
  have : lowCells lam δ c = key ⁻¹' {k | G k < ENNReal.ofReal (c * δ ^ 2)} := by
    ext p
    simp only [lowCells, mem_ofPred_eq, mem_preimage, hG]
  rw [this]
  exact hkey (Measurable.of_discrete (f := G) measurableSet_Iio)

/-- **Lebesgue differentiation on grid squares.**  The mass of observations with density
at least `2c` whose grid square has mass below `c δ²` tends to zero as `δ → 0`. -/
theorem tendsto_lowCells_dense (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) (hf : Measurable f)
    (hfin : ∫⁻ p, f p ∂(volume.prod Measure.count) ≠ ⊤) {c : ℝ} (hc : 0 < c)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ((volume.prod Measure.count).withDensity f)
      (lowCells ((volume.prod Measure.count).withDensity f) (δ n) c ∩
        {p | ENNReal.ofReal (2 * c) ≤ f p})) atTop (𝓝 0) := by
  set lam := (volume.prod Measure.count).withDensity f with hlam
  set B : ℕ → Set ((Fin 2 → ℝ) × ℤ) := fun n =>
    lowCells lam (δ n) c ∩ {p | ENNReal.ofReal (2 * c) ≤ f p} with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    (measurableSet_lowCells lam (hδpos n) c).inter (measurableSet_le measurable_const hf)
  have heq : ∀ n, lam (B n) = ∫⁻ p, (B n).indicator f p ∂(volume.prod Measure.count) := by
    intro n
    rw [hlam, withDensity_apply _ (hBm n), lintegral_indicator (hBm n)]
  show Tendsto (fun n => lam (B n)) atTop (𝓝 0)
  simp_rw [heq]
  have hlim0 : (0 : ℝ≥0∞) = ∫⁻ _p : (Fin 2 → ℝ) × ℤ, (0 : ℝ≥0∞) ∂(volume.prod Measure.count) := by
    simp
  rw [hlim0]
  refine tendsto_lintegral_of_dominated_convergence f
    (fun n => hf.indicator (hBm n)) (fun n => Filter.Eventually.of_forall
      (fun p => Set.indicator_le_self _ _ p)) hfin ?_
  -- pointwise convergence, slice by slice
  have hslice : ∀ m : ℤ, ∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)),
      Tendsto (fun n => (B n).indicator f (z, m)) atTop (𝓝 0) := by
    intro m
    set ρ : Measure (Fin 2 → ℝ) := volume.withDensity (fun z => f (z, m)) with hρ
    have hρfin : IsFiniteMeasure ρ := by
      constructor
      have h1 : ρ univ = lam (univ ×ˢ {m}) := by
        rw [hlam, withDensity_prod_singleton f hf MeasurableSet.univ m]
      rw [h1]
      calc lam (univ ×ˢ {m}) ≤ lam univ := measure_mono (subset_univ _)
        _ = ∫⁻ p, f p ∂(volume.prod Measure.count) := by
          rw [hlam, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ < ⊤ := lt_top_iff_ne_top.mpr hfin
    have hfm : Measurable (fun z : Fin 2 → ℝ => f (z, m)) :=
      hf.comp (measurable_id.prodMk measurable_const)
    let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Fin 2 → ℝ)) 1
    filter_upwards [v.ae_tendsto_rnDeriv ρ,
      Measure.rnDeriv_withDensity (volume : Measure (Fin 2 → ℝ)) hfm] with z hz hzr
    rw [hρ, hzr] at hz
    by_cases hbig : ENNReal.ofReal (2 * c) ≤ f (z, m)
    · -- the ratio converges to `f (z, m) > c`
      have hδ2 : Tendsto (fun n => δ n / 2) atTop (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n =>
          (by have := hδpos n; exact mem_Ioi.mpr (by positivity))⟩
        simpa using hδlim.div_const 2
      have hballs := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt
        (volume : Measure (Fin 2 → ℝ)) (K := 1) (l := atTop) (fun n => gridCenter (δ n) z)
        (fun n => δ n / 2) hδ2
        (Eventually.of_forall fun n => mem_closedBall_gridCenter (hδpos n) z)
      have hratio := hz.comp hballs
      have hlt : ENNReal.ofReal c < f (z, m) :=
        lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by linarith⟩) hbig
      have hev := (hratio.eventually (lt_mem_nhds hlt))
      have hzero : ∀ᶠ n in atTop, (B n).indicator f (z, m) = 0 := by
        filter_upwards [hev] with n hn
        apply Set.indicator_of_notMem
        intro hmem
        have hlow := hmem.1
        simp only [lowCells, mem_ofPred_eq] at hlow
        simp only [Function.comp] at hn
        rw [volume_closedBall_gridCenter (hδpos n)] at hn
        have hsq := measure_gridSquare_eq_ball ρ (withDensity_absolutelyContinuous _ _)
          (hδpos n) z
        rw [hlam, withDensity_prod_singleton f hf (measurableSet_gridSquare (δ n) z) m] at hlow
        rw [← hρ, hsq] at hlow
        have hδ2 : ENNReal.ofReal ((δ n) ^ 2) ≠ 0 := by
          have := hδpos n
          exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl hδ2) (Or.inl ENNReal.ofReal_ne_top)] at hn
        rw [← ENNReal.ofReal_mul hc.le] at hn
        exact absurd hlow (not_lt.mpr hn.le)
      exact tendsto_const_nhds.congr' (hzero.mono fun n hn => hn.symm)
    · have hzero : ∀ n, (B n).indicator f (z, m) = 0 := by
        intro n
        apply Set.indicator_of_notMem
        intro hmem
        exact hbig hmem.2
      simp only [hzero]
      exact tendsto_const_nhds
  -- assemble the product null set
  rw [ae_iff]
  choose N hNnull hNsub using fun m : ℤ =>
    (⟨_, ae_iff.mp (hslice m), subset_rfl⟩ :
      ∃ N : Set (Fin 2 → ℝ), volume N = 0 ∧
        {z | ¬ Tendsto (fun n => (B n).indicator f (z, m)) atTop (𝓝 0)} ⊆ N)
  apply measure_mono_null (t := ⋃ m : ℤ, toMeasurable volume (N m) ×ˢ {m})
  · intro p hp
    simp only [mem_ofPred_eq] at hp
    refine mem_iUnion.mpr ⟨p.2, ?_, rfl⟩
    exact subset_toMeasurable _ _ (hNsub p.2 hp)
  · apply measure_iUnion_null
    intro m
    rw [Measure.prod_prod, measure_toMeasurable, hNnull m, zero_mul]

end Submission.Obl.k4_scalar_initial_true_horizon
