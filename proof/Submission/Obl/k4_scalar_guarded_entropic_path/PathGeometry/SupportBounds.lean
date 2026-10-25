import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathSupport

/-! The common-law pullbacks keep the exact original time and
coefficient support bounds at every genuine parent. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def boundedIncidences (K₀ : ℝ) : Set State :=
  {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ e, |z.1.2 e| ≤ K₀}

theorem measurableSet_boundedIncidences (K₀ : ℝ) : MeasurableSet (boundedIncidences K₀) := by
  have hc : MeasurableSet {z : State | ∀ e, |z.1.2 e| ≤ K₀} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => measurableSet_le (by fun_prop) measurable_const
  exact (measurableSet_Icc.preimage measurable_snd).inter hc

theorem mu_bounded_ae {p : Code} (hp : Exact p) (k : ℕ) (g : Fin (W p k)) :
    ∀ᵐ z ∂mu p k g, z ∈ boundedIncidences (K p k) := by
  have ha := (hp.2.1 k).2.2.2.1 g
  letI : IsProbabilityMeasure (ν p k g) := ha.1
  have hm : MeasurableSet {z : State | ∀ e, |z.1.2 e| ≤ K p k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => measurableSet_le (by fun_prop) measurable_const
  have hcoef : ∀ᵐ z ∂(ν p k g).prod (volume : Measure ℝ), ∀ e, |z.1.2 e| ≤ K p k := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [ha.2.2.1] with l hl
    exact Eventually.of_forall fun _ => hl
  filter_upwards [ae_restrict_of_ae hcoef, ae_restrict_mem ha.2.2.2.1] with z hc hz
  exact ⟨(ha.2.2.2.2.1 hz).2, hc⟩

theorem worldMixture_bounded_ae {p : Code} (hp : Exact p) (k : ℕ) :
    ∀ᵐ z ∂worldMixture p k, z.2 ∈ boundedIncidences (K p k) := by
  have hm : MeasurableSet {z : Fin (W p k) × State | z.2 ∈ boundedIncidences (K p k)} :=
    (measurableSet_boundedIncidences _).preimage measurable_snd
  rw [worldMixture, ← Measure.sum_fintype]
  apply Measure.ae_sum_iff.mpr
  intro g
  apply Measure.smul_absolutelyContinuous.ae_le
  apply (ae_map_iff measurable_prodMk_left.aemeasurable hm).mpr
  exact mu_bounded_ae hp k g

theorem RefinementChain.pullback_bounded_ae {p z : Code}
    (chain : RefinementChain p z) (hp : Exact p) (k : ℕ)
    (ρ : Measure (Fin (W z k) × State)) (hρ : ρ ≪ worldMixture z k) :
    ∀ᵐ u ∂ρ, (chain.pullback k u).2 ∈ boundedIncidences (K p (chain.sample k)) :=
  hρ.ae_le (chain.pullback_ae k (worldMixture_bounded_ae hp (chain.sample k)))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
