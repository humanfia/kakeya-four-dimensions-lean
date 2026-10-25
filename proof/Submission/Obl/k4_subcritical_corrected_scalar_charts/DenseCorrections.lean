/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/DenseCorrections.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.FiniteCorrections
import Submission.Lib.K4ScalarCoreTools.Finalization.Pruning

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

/-- Prune by the original chart prior, choose all time corrections, and return
a quantitative dense restriction of the unchanged original incidence law. -/
theorem exists_dense_prior_relative_corrections {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (E : ι → Set (α × ℝ)) (hE : ∀ i, MeasurableSet (E i))
    (hsub : ∀ i, E i ⊆ A i ×ˢ Icc (0 : ℝ) 1)
    (hcover : ∀ᵐ p ∂ρ, ∃ i, p ∈ E i)
    (Hb : ι → α → Fin 6 → ℝ) (H0 : ι → Fin 6 → ℝ)
    (r : ℝ) (signal : ι → ℝ → ℝ) (hsignal_meas : ∀ i, Measurable (signal i))
    {K m S δ : ℝ} (hK : 0 < K) (hm : 0 < m) (hmK : m ≤ K)
    (hS : 0 ≤ S) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hmass : ENNReal.ofReal (2 * m) ≤ ρ univ)
    (hsignal : ∀ i, ∀ p ∈ E i, |signal i p.2| ≤ S)
    (hfit : ∀ i, ∀ p ∈ E i,
      |r * fiberDerivative (Hb i p.1 - H0 i) p.2 - signal i p.2| ≤ δ) :
    ∃ (β : ι → Fin 3 → ℝ) (F : Set (α × ℝ)),
      (∀ i e, |β i e| ≤ 17 * (96 * K / m) ^ 2 * (S + δ)) ∧
      MeasurableSet F ∧ ENNReal.ofReal (m ^ 3 / (8 * K ^ 2)) ≤ ρ F ∧
      ∀ p ∈ F, ∃ i, p ∈ E i ∧
        |signal i p.2 - fiberDerivative (fiberCorrection (β i)) p.2| ≤ δ := by
  classical
  have hcap (i : ι) : ρ (E i) ≤ ENNReal.ofReal K * ν (A i) := by
    calc
      _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (E i) := hdom (E i)
      _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (A i ×ˢ Icc (0 : ℝ) 1) :=
        measure_mono (hsub i)
      _ = _ := by simp [Measure.prod_prod]
  have hzero : ∀ᵐ p ∂ρ, ∀ i, ν (A i) = 0 → p ∉ E i := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : ν (A i) = 0
    · have he : ρ (E i) = 0 := le_antisymm (by simpa only [hi, mul_zero] using hcap i) bot_le
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp he] with p hp
      exact fun _ => hp
    · exact Filter.Eventually.of_forall fun p hp => False.elim (hi hp)
  let I := Finset.univ.filter fun i => ν (A i) ≠ 0
  have hbudget : ∑ i ∈ I, ν (A i) ≤ 1 := by
    calc
      _ = ν (⋃ i ∈ I, A i) := (measure_biUnion_finset
        (fun _ _ _ _ hne => hdisj hne) (fun i _ => hA i)).symm
      _ ≤ ν univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have htotal : ρ univ ≤ ρ (⋃ i ∈ I, E i) := by
    apply measure_mono_ae
    filter_upwards [hcover, hzero] with p hp hz
    intro _
    obtain ⟨i, hi⟩ := hp
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun h => hz i h hi⟩, hi⟩
  obtain ⟨H, hHI, hfloor, hloss⟩ :=
    Submission.Lib.K4ScalarCoreTools.Finalization.prune_small_labels ρ I E
      (fun i => ν (A i)) (τ := ENNReal.ofReal m) hbudget
  have hkeep : ENNReal.ofReal m ≤ ρ (⋃ i ∈ H, E i) := by
    apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
    have htwo : ENNReal.ofReal m + ENNReal.ofReal m ≤ ρ univ := by
      rw [← ENNReal.ofReal_add hm.le hm.le]
      convert hmass using 1 <;> congr 1 <;> ring
    exact htwo.trans (htotal.trans (by simpa only [mul_one] using hloss))
  have hpriorcap : ρ (⋃ i ∈ H, E i) ≤ ENNReal.ofReal K * ∑ i ∈ H, ν (A i) := by
    calc
      _ ≤ ∑ i ∈ H, ρ (E i) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ H, ENNReal.ofReal K * ν (A i) := Finset.sum_le_sum fun i _ => hcap i
      _ = _ := by rw [Finset.mul_sum]
  have heq : ENNReal.ofReal (∑ i ∈ H, (ν (A i)).toReal) = ∑ i ∈ H, ν (A i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hreal : m ≤ K * ∑ i ∈ H, (ν (A i)).toReal := by
    have hbound := hkeep.trans hpriorcap
    rw [← heq, ← ENNReal.ofReal_mul hK.le] at hbound
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [ENNReal.toReal_ofReal hm.le,
      ENNReal.toReal_ofReal (show 0 ≤ K * ∑ i ∈ H, (ν (A i)).toReal by positivity)] using hh
  obtain ⟨β, hβ, hmeas, hret⟩ := exists_finite_prior_relative_corrections ν ρ H A E
    (fun i hi => (Finset.mem_filter.mp (hHI hi)).2)
    (fun _ _ _ _ hne => hdisj hne) hE (fun i _ => hsub i) Hb H0 r signal
    hsignal_meas hK hm hmK hS hδ hdom hfloor (fun i _ => hsignal i) (fun i _ => hfit i)
  refine ⟨β, _, hβ, hmeas, ?_, ?_⟩
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hret
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * K ^ 2 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hreal (show 0 ≤ m ^ 2 by positivity)
    field_simp
    nlinarith
  · intro p hp
    obtain ⟨i, hi, hpE, hpfit⟩ := mem_iUnion₂.mp hp
    exact ⟨i, hpE, hpfit⟩

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
