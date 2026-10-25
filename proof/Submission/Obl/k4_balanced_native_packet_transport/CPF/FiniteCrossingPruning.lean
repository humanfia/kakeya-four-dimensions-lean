/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/FiniteCrossingPruning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/FiniteCrossingPruning.lean. Earlier provenance is retained below. -/
import Mathlib

/-! Markov pruning of finite crossing lists under the original observation law. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

def finiteCrossingList {X ι : Type*} [Fintype ι] (S : ι → Set X) (x : X) : Finset ι :=
  Finset.univ.filter (fun i => x ∈ S i)

def finiteCrossingCount {X ι : Type*} [Fintype ι] (S : ι → Set X) (x : X) : ENNReal :=
  ((finiteCrossingList S x).card : ENNReal)

theorem finiteCrossingCount_eq_sum {X ι : Type*} [Fintype ι] (S : ι → Set X) (x : X) :
    finiteCrossingCount S x = ∑ i, (S i).indicator (fun _ => (1 : ENNReal)) x := by
  simp only [finiteCrossingCount, finiteCrossingList, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem finiteCrossingCount_gt_iff {X ι : Type*} [Fintype ι] (S : ι → Set X) (x : X)
    {H : ℝ} (hH : 0 ≤ H) :
    ENNReal.ofReal H < finiteCrossingCount S x ↔ H < ((finiteCrossingList S x).card : ℝ) := by
  rw [finiteCrossingCount, ← ENNReal.ofReal_natCast]
  constructor
  · intro h
    by_contra! hn
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hn)) h
  · intro h
    exact (ENNReal.ofReal_lt_ofReal_iff (hH.trans_lt h)).mpr h

theorem measurable_finiteCrossingCount {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) : Measurable (finiteCrossingCount S) := by
  simp_rw [funext (finiteCrossingCount_eq_sum S)]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hS i))

theorem lintegral_finiteCrossingCount {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) :
    (∫⁻ x, finiteCrossingCount S x ∂μ) = ∑ i, μ (S i) := by
  simp_rw [finiteCrossingCount_eq_sum]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hS i))]
  simp_rw [lintegral_indicator_const (hS _), one_mul]

theorem measure_long_crossing_list {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    {H : ENNReal} (hH : H ≠ 0) (hHtop : H ≠ ∞) :
    μ {x | H < finiteCrossingCount S x} ≤ (∑ i, μ (S i)) / H := by
  calc
    _ ≤ μ {x | H ≤ finiteCrossingCount S x} := measure_mono (fun x hx => (show H < finiteCrossingCount S x from hx).le)
    _ ≤ (∫⁻ x, finiteCrossingCount S x ∂μ) / H :=
      meas_ge_le_lintegral_div (measurable_finiteCrossingCount S hS).aemeasurable hH hHtop
    _ = _ := by rw [lintegral_finiteCrossingCount μ S hS]

/-- A density ceiling may be used analytically without inserting its test into the
retained event's Boolean format. -/
theorem withDensity_set_le_exception_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {g : X → ENNReal} (hg : Measurable g) (θ : ENNReal)
    (A : Set X) (hA : MeasurableSet A) :
    μ.withDensity g A ≤ μ.withDensity g {x | θ < g x} + θ * μ A := by
  let C := A ∩ {x | g x ≤ θ}
  have hC : MeasurableSet C := hA.inter (measurableSet_le hg measurable_const)
  have hsub : A ⊆ {x | θ < g x} ∪ C := by
    intro x hx
    by_cases h : θ < g x
    · exact Or.inl h
    · exact Or.inr ⟨hx, le_of_not_gt h⟩
  have hcap : μ.withDensity g C ≤ θ * μ A := by
    rw [withDensity_apply _ hC, ← lintegral_indicator hC]
    calc
      _ ≤ ∫⁻ x, A.indicator (fun _ => θ) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ C
        · rw [indicator_of_mem hx, indicator_of_mem hx.1]
          exact hx.2
        · rw [indicator_of_notMem hx]
          exact zero_le
      _ = _ := lintegral_indicator_const hA θ
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans (add_le_add le_rfl hcap)

/-- The lost original mass is the exceptional density mass plus the Markov cost.
Only the long-list predicate will need to be retained in polynomial format. -/
theorem observed_long_crossing_list_mass {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype ι]
    (ν : Measure Ω) (μ : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    {g : X → ENNReal} (hg : Measurable g) (hmap : ν.map obs = μ.withDensity g)
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (θ : ENNReal) {H : ENNReal} (hH : H ≠ 0) (hHtop : H ≠ ∞) :
    ν {p | H < finiteCrossingCount S (obs p)} ≤
      ν {p | θ < g (obs p)} + θ * ((∑ i, μ (S i)) / H) := by
  have hA : MeasurableSet {x | H < finiteCrossingCount S x} :=
    measurableSet_lt measurable_const (measurable_finiteCrossingCount S hS)
  have hbad : MeasurableSet {x | θ < g x} := measurableSet_lt measurable_const hg
  have hm (A : Set X) (hA : MeasurableSet A) : ν (obs ⁻¹' A) = μ.withDensity g A := by
    rw [← Measure.map_apply hobs hA, hmap]
  change ν (obs ⁻¹' {x | H < finiteCrossingCount S x}) ≤
    ν (obs ⁻¹' {x | θ < g x}) + _
  rw [hm _ hA, hm _ hbad]
  exact (withDensity_set_le_exception_add μ hg θ _ hA).trans
    (add_le_add le_rfl (mul_le_mul le_rfl
      (measure_long_crossing_list μ S hS hH hHtop) zero_le zero_le))

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
