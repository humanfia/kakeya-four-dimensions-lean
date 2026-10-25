import Mathlib

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- Uniform caps for fixed discrete labels also hold for a label chosen measurably
from the observed base. The base regions in the sum are disjoint. -/
theorem moving_label_cap {Ω Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Countable I] (μ : Measure Ω) (ν : Measure Y) (base : Ω → Y) (label : Ω → I)
    (K : ENNReal)
    (hcap : ∀ i E, MeasurableSet E →
      μ {p | base p ∈ E ∧ label p = i} ≤ K * ν E)
    (f : Y → I) (hf : ∀ i, MeasurableSet {y | f y = i})
    (E : Set Y) (hE : MeasurableSet E) :
    μ {p | base p ∈ E ∧ label p = f (base p)} ≤ K * ν E := by
  let B : I → Set Y := fun i => {y | y ∈ E ∧ f y = i}
  have hB : ∀ i, MeasurableSet (B i) := fun i => hE.inter (hf i)
  have hdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hU : (⋃ i, B i) = E := by
    ext y
    simp only [mem_iUnion, B, mem_ofPred_eq]
    exact ⟨fun ⟨_, hy, _⟩ => hy, fun hy => ⟨f y, hy, rfl⟩⟩
  calc
    _ ≤ μ (⋃ i, {p | base p ∈ B i ∧ label p = i}) := by
      apply measure_mono
      intro p hp
      exact mem_iUnion.mpr ⟨f (base p), ⟨hp.1, rfl⟩, hp.2⟩
    _ ≤ ∑' i, μ {p | base p ∈ B i ∧ label p = i} := measure_iUnion_le _
    _ ≤ ∑' i, K * ν (B i) := ENNReal.tsum_le_tsum (fun i => hcap i (B i) (hB i))
    _ = K * ν E := by rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hB, hU]

/-- A fixed finite collection of offsets from a measurable base label costs only
its cardinality in the marginal cap. -/
theorem moving_integer_offsets_cap {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Y) (base : Ω → Y) (label : Ω → ℤ)
    (K : ENNReal)
    (hcap : ∀ i E, MeasurableSet E →
      μ {p | base p ∈ E ∧ label p = i} ≤ K * ν E)
    (f : Y → ℤ) (hf : Measurable f)
    (F : Finset ℤ) (E : Set Y) (hE : MeasurableSet E) :
    μ {p | base p ∈ E ∧ label p - f (base p) ∈ F} ≤ (F.card : ENNReal) * K * ν E := by
  have hsub : {p | base p ∈ E ∧ label p - f (base p) ∈ F} ⊆
      ⋃ k ∈ F, {p | base p ∈ E ∧ label p = f (base p) + k} := by
    intro p hp
    simp only [mem_iUnion]
    exact ⟨label p - f (base p), hp.2, hp.1, by omega⟩
  calc
    _ ≤ μ (⋃ k ∈ F, {p | base p ∈ E ∧ label p = f (base p) + k}) := measure_mono hsub
    _ ≤ ∑ k ∈ F, μ {p | base p ∈ E ∧ label p = f (base p) + k} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ F, K * ν E := by
      apply Finset.sum_le_sum
      intro k hk
      exact moving_label_cap μ ν base label K hcap (fun y => f y + k)
        (fun j => (hf.add_const k) (measurableSet_singleton j)) E hE
    _ = _ := by simp [mul_assoc]

/-- Two floors differ by less than the distance between their arguments plus one. -/
theorem abs_floor_sub_lt (x y : ℝ) :
    |((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)| < |x - y| + 1 := by
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  push_cast
  rw [abs_lt]
  constructor <;> linarith [le_abs_self (x - y), neg_abs_le (x - y)]

/-- A moving real interval is covered by a uniformly bounded collection of offsets
from its center's integer bin. -/
theorem floor_offset_mem {a L x y : ℝ} (ha : 0 < a)
    (hfit : |x - y| ≤ L * a) :
    ⌊x / a⌋ - ⌊y / a⌋ ∈ Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉ := by
  have hxy : |x / a - y / a| ≤ L := by
    rw [← sub_div, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hfit
  have hfl := abs_floor_sub_lt (x / a) (y / a)
  have hc := Int.le_ceil (L + 1)
  have hh : |((⌊x / a⌋ - ⌊y / a⌋ : ℤ) : ℝ)| ≤ (⌈L + 1⌉ : ℤ) :=
    by linarith
  rw [abs_le] at hh
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

/-- The number of offsets needed by a radius `L` interval is at most `2 L + 5`. -/
theorem card_floor_offsets_le {L : ℝ} (hL : 0 ≤ L) :
    ((Finset.Icc (-⌈L + 1⌉ : ℤ) ⌈L + 1⌉).card : ℝ) ≤ 2 * L + 5 := by
  have hc : (0 : ℤ) ≤ ⌈L + 1⌉ := Int.ceil_nonneg (by linarith)
  rw [Int.card_Icc]
  have hnat : (0 : ℤ) ≤ ⌈L + 1⌉ + 1 - -⌈L + 1⌉ := by omega
  have hcast : (((⌈L + 1⌉ + 1 - -⌈L + 1⌉).toNat : ℕ) : ℝ) =
      (⌈L + 1⌉ + 1 - -⌈L + 1⌉ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hnat
  rw [hcast]
  push_cast
  linarith [Int.ceil_lt_add_one (L + 1)]


/-- A continuous-base cap on each scalar bin controls every moving interval of
radius `L` bins, independently of the range of the center function. -/
theorem moving_interval_cap {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Y) (base : Ω → Y) (x : Ω → ℝ)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (K : ENNReal)
    (hcap : ∀ i E, MeasurableSet E →
      μ {p | base p ∈ E ∧ ⌊x p / a⌋ = i} ≤ K * ν E)
    (f : Y → ℝ) (hf : Measurable f) (E : Set Y) (hE : MeasurableSet E) :
    μ {p | base p ∈ E ∧ |x p - f (base p)| ≤ L * a} ≤
      ENNReal.ofReal (2 * L + 5) * K * ν E := by
  let F : Finset ℤ := Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉
  have hcard : (F.card : ENNReal) ≤ ENNReal.ofReal (2 * L + 5) := by
    calc
      _ = ENNReal.ofReal (F.card : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (card_floor_offsets_le hL)
  calc
    _ ≤ μ {p | base p ∈ E ∧ ⌊x p / a⌋ - ⌊f (base p) / a⌋ ∈ F} := by
      apply measure_mono
      intro p hp
      exact ⟨hp.1, floor_offset_mem ha hp.2⟩
    _ ≤ (F.card : ENNReal) * K * ν E :=
      moving_integer_offsets_cap μ ν base (fun p => ⌊x p / a⌋) K hcap
        (fun y => ⌊f y / a⌋) (hf.div_const a).floor F E hE
    _ ≤ _ := by gcongr

end Submission.Obl.k4_fixed_budget_quadratic_recovery
