import Submission.Obl.k4_crop_base_finite_tail.Transfer

namespace Submission.Obl.k4_crop_base_finite_tail

open MeasureTheory Set Filter
open scoped ENNReal

/-- Restricting a state law decreases its observation density, for arbitrary
measurable representatives, also after evaluating on the restricted states. -/
lemma restricted_observation_density_le {X Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Z]
    (ref : Measure Z) [SigmaFinite ref] (μ : Measure X)
    (Q : X → Z) (hQ : Measurable Q) (S : Set X)
    (D H : Z → ℝ≥0∞) (hD : Measurable D) (hH : Measurable H)
    (hDlaw : (μ.restrict S).map Q = ref.withDensity D)
    (hHlaw : μ.map Q = ref.withDensity H) :
    ∀ᵐ x ∂μ.restrict S, D (Q x) ≤ H (Q x) := by
  have href : ∀ᵐ z ∂ref, D z ≤ H z := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hD
    intro U hU _
    rw [← withDensity_apply _ hU, ← withDensity_apply _ hU, ← hDlaw, ← hHlaw]
    exact Measure.le_iff'.mp (Measure.map_mono Measure.restrict_le_self hQ) U
  have hmap : ∀ᵐ z ∂(μ.restrict S).map Q, D z ≤ H z := by
    rw [hDlaw]
    exact (withDensity_absolutelyContinuous ref D) href
  exact (ae_map_iff hQ.aemeasurable (measurableSet_le hD hH)).mp hmap

/-- Finite disjoint state restrictions and boundedly overlapping observation
supports give a uniform density-tail estimate. -/
theorem finite_density_tail {X Z Γ : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [Fintype Γ]
    (ref : Measure Z) [SigmaFinite ref] (μ : Measure X)
    (Q : X → Z) (hQ : Measurable Q)
    (H : Z → ℝ≥0∞) (hH : Measurable H) (hHlaw : μ.map Q = ref.withDensity H)
    (S : Γ → Set X) (hS : ∀ γ, MeasurableSet (S γ))
    (hdisj : Pairwise fun γ γ' => Disjoint (S γ) (S γ'))
    (D : Γ → Z → ℝ≥0∞) (hD : ∀ γ, Measurable (D γ))
    (hDlaw : ∀ γ, (μ.restrict (S γ)).map Q = ref.withDensity (D γ))
    (C : Γ → Set Z) (hC : ∀ γ, MeasurableSet (C γ))
    (hsupp : ∀ γ, ∀ᵐ x ∂μ.restrict (S γ), Q x ∈ C γ)
    (K : ℝ≥0∞) (hK : ∀ z, ∑ γ, (C γ).indicator (fun _ => (1 : ℝ≥0∞)) z ≤ K)
    (lo hi upper δ : ℝ≥0∞) (hupper : hi ≤ upper) :
    (∑ γ, μ (S γ ∩ {x | D γ (Q x) < δ * lo ∨ upper < D γ (Q x)})) ≤
      μ {x | H (Q x) < lo ∨ hi < H (Q x)} + K * δ * μ univ := by
  classical
  let B : Set X := {x | H (Q x) < lo ∨ hi < H (Q x)}
  let R : Γ → Set X := fun γ => {x | D γ (Q x) < δ * H (Q x)}
  let T : Γ → Set X := fun γ => {x | D γ (Q x) < δ * lo ∨ upper < D γ (Q x)}
  have hB : MeasurableSet B :=
    (measurableSet_lt (hH.comp hQ) measurable_const).union
      (measurableSet_lt measurable_const (hH.comp hQ))
  have hR (γ : Γ) : MeasurableSet (R γ) :=
    measurableSet_lt ((hD γ).comp hQ) (measurable_const.mul (hH.comp hQ))
  have hT (γ : Γ) : MeasurableSet (T γ) :=
    (measurableSet_lt ((hD γ).comp hQ) measurable_const).union
      (measurableSet_lt measurable_const ((hD γ).comp hQ))
  have hterm (γ : Γ) : μ (S γ ∩ T γ) ≤ μ (S γ ∩ B) + μ (S γ ∩ R γ) := by
    have hle := restricted_observation_density_le ref μ Q hQ (S γ)
      (D γ) H (hD γ) hH (hDlaw γ) hHlaw
    have hinc : T γ ≤ᵐ[μ.restrict (S γ)] B ∪ R γ := by
      filter_upwards [hle] with x hx hxt
      by_cases hb : x ∈ B
      · exact Or.inl hb
      · apply Or.inr
        have hlo : lo ≤ H (Q x) := le_of_not_gt fun h => hb (Or.inl h)
        rcases hxt with htlo | hthi
        · exact htlo.trans_le (mul_le_mul_right hlo δ)
        · exact (hb (Or.inr (hupper.trans_lt (hthi.trans_le hx)))).elim
    have hm := (measure_mono_ae hinc).trans (measure_union_le B (R γ))
    simpa only [Measure.restrict_apply (hT γ), Measure.restrict_apply hB,
      Measure.restrict_apply (hR γ), inter_comm] using hm
  have hsource : (∑ γ, μ (S γ ∩ B)) ≤ μ B := by
    calc
      (∑ γ, μ (S γ ∩ B)) = μ (⋃ γ ∈ (Finset.univ : Finset Γ), S γ ∩ B) := by
        rw [measure_biUnion_finset]
        · intro i _ j _ hij
          exact (hdisj hij).mono inter_subset_left inter_subset_left
        · exact fun γ _ => (hS γ).inter hB
      _ ≤ μ B := measure_mono (by
        simp only [Finset.mem_univ, iUnion_true]
        exact iUnion_subset fun _ => inter_subset_right)
  calc
    (∑ γ, μ (S γ ∩ T γ)) ≤ ∑ γ, (μ (S γ ∩ B) + μ (S γ ∩ R γ)) :=
      Finset.sum_le_sum fun γ _ => hterm γ
    _ = (∑ γ, μ (S γ ∩ B)) + ∑ γ, μ (S γ ∩ R γ) := Finset.sum_add_distrib
    _ ≤ μ B + K * δ * μ univ := add_le_add hsource
      (sum_lower_ratio_le ref μ hQ hH hHlaw S D hD hDlaw C hC hsupp K hK δ)

end Submission.Obl.k4_crop_base_finite_tail
