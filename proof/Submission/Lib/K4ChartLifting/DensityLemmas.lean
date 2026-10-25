import Mathlib

/-!
# Density comparisons for restricted and labelled laws

`density_le_of_le`: a smaller law has a smaller density almost everywhere.
`density_vanishes_off_lists`: the observation law of a selection whose incidences all list
the label `c` has a density vanishing where `c` is not listed. `refinement_lists` (paper
Lemma 2.3, refinement part): with lists of at most `κ` labels, the total labelled mass where
a label's density falls below `ε g` is at most `ε κ ∫ g`. `dyWidth_mul`, `alignedDepth_bounds`:
the composed width `δ(N,r) δ(N,s)` is exactly `δ(N,ρ')` at the aligned depth
`ρ' ∈ (r + s - 2 log 2 / log N, r + s]`.
-/

open MeasureTheory

namespace Submission.Lib.K4ChartLifting

/-- A smaller law has a smaller density, almost everywhere. -/
theorem density_le_of_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) [SigmaFinite ρ]
    {h₁ h₂ : Y → ENNReal} (h₁m : Measurable h₁)
    (hle : ρ.withDensity h₁ ≤ ρ.withDensity h₂) : h₁ ≤ᵐ[ρ] h₂ := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite h₁m fun s hs _ => ?_
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
  exact hle s

/-- A law concentrated where the label `c` is listed has a density vanishing off the list. -/
theorem density_vanishes_off_lists {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure Y) (μ : Measure X) {obs : X → Y} (hobs : Measurable obs) (F : Set X)
    (c : ι) (lst : Y → Finset ι) (hlstm : MeasurableSet {y | c ∈ lst y})
    (hF : ∀ p ∈ F, c ∈ lst (obs p)) {h : Y → ENNReal} (hh : Measurable h)
    (hlaw : Measure.map obs (μ.restrict F) = ρ.withDensity h) :
    ∀ᵐ y ∂ρ, c ∉ lst y → h y = 0 := by
  have hS : MeasurableSet {y | c ∉ lst y} := hlstm.compl
  have hzero : ∫⁻ y in {y | c ∉ lst y}, h y ∂ρ = 0 := by
    rw [← withDensity_apply _ hS, ← hlaw, Measure.map_apply hobs hS,
      Measure.restrict_apply (hobs hS)]
    apply measure_mono_null _ measure_empty
    intro p ⟨hp1, hp2⟩
    exact absurd (hF p hp2) hp1
  rw [lintegral_eq_zero_iff hh, Filter.EventuallyEq, ae_restrict_iff' hS] at hzero
  filter_upwards [hzero] with y hy hc
  exact hy hc

/-- **Refinement by listed labels** (paper Lemma 2.3, refinement part): if each label's
density vanishes off its list, lists have at most `κ` members, and every label's density
is at most `g`, then the total labelled mass where a density falls below `ε g` is at most
`ε κ ∫ g`. -/
theorem refinement_lists {Y ι : Type*} [MeasurableSpace Y] [Fintype ι] (ρ : Measure Y)
    (g : Y → ENNReal) (h : ι → Y → ENNReal) (hh : ∀ c, Measurable (h c)) (hg : Measurable g)
    (lst : Y → Finset ι) (κ : ℕ) (hlst : ∀ y, (lst y).card ≤ κ)
    (hsupp : ∀ c, ∀ᵐ y ∂ρ, c ∉ lst y → h c y = 0) (ε : ENNReal) :
    ∑ c, ∫⁻ y in {y | h c y < ε * g y}, h c y ∂ρ ≤ ε * κ * ∫⁻ y, g y ∂ρ := by
  classical
  have hS : ∀ c, MeasurableSet {y | h c y < ε * g y} := fun c =>
    measurableSet_lt (hh c) (measurable_const.mul hg)
  calc ∑ c, ∫⁻ y in {y | h c y < ε * g y}, h c y ∂ρ
      = ∑ c, ∫⁻ y, Set.indicator {y | h c y < ε * g y} (h c) y ∂ρ := by
        apply Finset.sum_congr rfl; intro c _; rw [lintegral_indicator (hS c)]
    _ = ∫⁻ y, ∑ c, Set.indicator {y | h c y < ε * g y} (h c) y ∂ρ := by
        rw [lintegral_finsetSum _ (fun c _ => (hh c).indicator (hS c))]
    _ ≤ ∫⁻ y, ε * κ * g y ∂ρ := by
        apply lintegral_mono_ae
        have hall : ∀ᵐ y ∂ρ, ∀ c, c ∉ lst y → h c y = 0 := ae_all_iff.mpr hsupp
        filter_upwards [hall] with y hy
        calc ∑ c, Set.indicator {y | h c y < ε * g y} (h c) y
            ≤ ∑ c, (if c ∈ lst y then ε * g y else 0) := by
              apply Finset.sum_le_sum
              intro c _
              by_cases hc : c ∈ lst y
              · simp only [hc, ite_true]
                by_cases hm : y ∈ {y | h c y < ε * g y}
                · rw [Set.indicator_of_mem hm]; exact le_of_lt hm
                · rw [Set.indicator_of_notMem hm]; exact zero_le
              · simp only [hc, ite_false]
                by_cases hm : y ∈ {y | h c y < ε * g y}
                · rw [Set.indicator_of_mem hm, hy c hc]
                · rw [Set.indicator_of_notMem hm]
          _ = ∑ c ∈ lst y, ε * g y := by
              rw [← Finset.sum_filter]; congr 1; ext c; simp
          _ = (lst y).card * (ε * g y) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ κ * (ε * g y) := by
              gcongr; exact_mod_cast hlst y
          _ = ε * κ * g y := by ring
    _ = ε * κ * ∫⁻ y, g y ∂ρ := lintegral_const_mul _ hg

/-- The frozen dyadic width `δ(N, r) = 2 ^ (-⌊r log N / log 2⌋)`. -/
noncomputable def dyWidth (N r : ℝ) : ℝ := (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

/-- The aligned depth of a composed width. -/
noncomputable def alignedDepth (N r s : ℝ) : ℝ :=
  ((⌊r * Real.log N / Real.log 2⌋ + ⌊s * Real.log N / Real.log 2⌋ : ℤ) : ℝ) * Real.log 2 /
    Real.log N

/-- Composed dyadic widths are dyadic widths of the aligned depth, exactly. -/
theorem dyWidth_mul (N r s : ℝ) (hN : 1 < N) :
    dyWidth N r * dyWidth N s = dyWidth N (alignedDepth N r s) := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfl : ⌊alignedDepth N r s * Real.log N / Real.log 2⌋ =
      ⌊r * Real.log N / Real.log 2⌋ + ⌊s * Real.log N / Real.log 2⌋ := by
    have : alignedDepth N r s * Real.log N / Real.log 2 =
        ((⌊r * Real.log N / Real.log 2⌋ + ⌊s * Real.log N / Real.log 2⌋ : ℤ) : ℝ) := by
      unfold alignedDepth; field_simp
    rw [this, Int.floor_intCast]
  unfold dyWidth
  rw [hfl, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The aligned depth is within `2 log 2 / log N` below `r + s`. -/
theorem alignedDepth_bounds (N r s : ℝ) (hN : 1 < N) :
    r + s - 2 * Real.log 2 / Real.log N < alignedDepth N r s ∧ alignedDepth N r s ≤ r + s := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := Int.floor_le (r * Real.log N / Real.log 2)
  have h2 := Int.floor_le (s * Real.log N / Real.log 2)
  have h3 := Int.lt_floor_add_one (r * Real.log N / Real.log 2)
  have h4 := Int.lt_floor_add_one (s * Real.log N / Real.log 2)
  unfold alignedDepth
  push_cast
  constructor
  · rw [lt_div_iff₀ hlog]
    have : (r + s - 2 * Real.log 2 / Real.log N) * Real.log N =
        (r * Real.log N / Real.log 2 + s * Real.log N / Real.log 2 - 2) * Real.log 2 := by
      field_simp
    rw [this]
    exact mul_lt_mul_of_pos_right (by linarith) hlog2
  · rw [div_le_iff₀ hlog]
    have : (r + s) * Real.log N =
        (r * Real.log N / Real.log 2 + s * Real.log N / Real.log 2) * Real.log 2 := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hlog2.le

end Submission.Lib.K4ChartLifting
