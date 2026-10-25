/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/FiniteCorrections.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PriorRelativeCorrection

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

/-- Choose the time correction simultaneously on finitely many disjoint full
charts. Original prior factors add without a loss depending on the chart count. -/
theorem exists_finite_prior_relative_corrections {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (H : Finset ι) (A : ι → Set α) (E : ι → Set (α × ℝ))
    (hA₀ : ∀ i ∈ H, ν (A i) ≠ 0)
    (hdisj : (H : Set ι).PairwiseDisjoint A)
    (hE : ∀ i, MeasurableSet (E i))
    (hsub : ∀ i ∈ H, E i ⊆ A i ×ˢ Icc (0 : ℝ) 1)
    (Hb : ι → α → Fin 6 → ℝ) (H0 : ι → Fin 6 → ℝ)
    (r : ℝ) (signal : ι → ℝ → ℝ) (hsignal_meas : ∀ i, Measurable (signal i))
    {K m S δ : ℝ} (hK : 0 < K) (hm : 0 < m) (hmK : m ≤ K)
    (hS : 0 ≤ S) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hfloor : ∀ i ∈ H, ENNReal.ofReal m * ν (A i) ≤ ρ (E i))
    (hsignal : ∀ i ∈ H, ∀ p ∈ E i, |signal i p.2| ≤ S)
    (hfit : ∀ i ∈ H, ∀ p ∈ E i,
      |r * fiberDerivative (Hb i p.1 - H0 i) p.2 - signal i p.2| ≤ δ) :
    ∃ β : ι → Fin 3 → ℝ,
      (∀ i e, |β i e| ≤ 17 * (96 * K / m) ^ 2 * (S + δ)) ∧
      MeasurableSet (⋃ i ∈ H, {p : α × ℝ | p ∈ E i ∧
        |signal i p.2 - fiberDerivative (fiberCorrection (β i)) p.2| ≤ δ}) ∧
      ENNReal.ofReal ((∑ i ∈ H, (ν (A i)).toReal) * (m ^ 2 / (8 * K))) ≤
        ρ (⋃ i ∈ H, {p : α × ℝ | p ∈ E i ∧
          |signal i p.2 - fiberDerivative (fiberCorrection (β i)) p.2| ≤ δ}) := by
  classical
  let B := 17 * (96 * K / m) ^ 2 * (S + δ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hex (i : ι) : ∃ β : Fin 3 → ℝ,
      (∀ e, |β e| ≤ B) ∧ (i ∈ H →
        ENNReal.ofReal ((ν (A i)).toReal * (m ^ 2 / (8 * K))) ≤
          ρ {p : α × ℝ | p ∈ E i ∧
            |signal i p.2 - fiberDerivative (fiberCorrection β) p.2| ≤ δ}) := by
    by_cases hi : i ∈ H
    · obtain ⟨β, hβ, hmass⟩ := exists_prior_relative_directional_correction ν ρ (A i)
        (hA₀ i hi) (Hb i) (H0 i) r (signal i) (hsignal_meas i)
        hK hm hmK hS hδ hdom (hE i) (hfloor i hi) (hsub i hi)
        (hsignal i hi) (hfit i hi)
      exact ⟨β, hβ, fun _ => hmass⟩
    · exact ⟨0, (by intro e; simpa only [Pi.zero_apply, abs_zero] using hB),
        fun hi' => False.elim (hi hi')⟩
  choose β hβ hret using hex
  let F := fun i => {p : α × ℝ | p ∈ E i ∧
    |signal i p.2 - fiberDerivative (fiberCorrection (β i)) p.2| ≤ δ}
  have hF (i : ι) : MeasurableSet (F i) := by
    have hfiber : Measurable (fun p : α × ℝ => fiberDerivative (fiberCorrection (β i)) p.2) := by
      unfold fiberDerivative
      fun_prop
    exact (hE i).inter
      (measurableSet_le ((hsignal_meas i |>.comp measurable_snd).sub hfiber).abs measurable_const)
  have hd : (H : Set ι).PairwiseDisjoint F := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (hdisj hi hj hij) ((hsub i hi hpi.1).1) ((hsub j hj hpj.1).1)
  refine ⟨β, hβ, H.measurableSet_biUnion (fun i _ => hF i), ?_⟩
  change ENNReal.ofReal ((∑ i ∈ H, (ν (A i)).toReal) * (m ^ 2 / (8 * K))) ≤
    ρ (⋃ i ∈ H, F i)
  rw [Finset.sum_mul]
  calc
    _ = ∑ i ∈ H, ENNReal.ofReal ((ν (A i)).toReal * (m ^ 2 / (8 * K))) :=
      ENNReal.ofReal_sum_of_nonneg (by intro i hi; positivity)
    _ ≤ ∑ i ∈ H, ρ (F i) := Finset.sum_le_sum fun i hi => hret i hi
    _ = _ := (measure_biUnion_finset hd (fun i _ => hF i)).symm

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
