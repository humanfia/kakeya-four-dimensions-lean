import Submission.Obl.k4_scalar_grid_density_extension.GridRelation
import Submission.Obl.k4_crop_base_finite_tail.FiniteTail
import Submission.Obl.k4_adapted_affine_cube_cover.Assembly

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

/-- Slice identities obtained from a density of a countably labelled observation. -/
lemma label_density_slice {X Z I : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (ref : Measure Z) [SFinite ref] (μ : Measure X)
    (ψ : X → Z) (hψ : Measurable ψ) (s : X → I) (hs : Measurable s)
    (H : Z × I → ENNReal) (hH : Measurable H)
    (hlaw : μ.map (fun x => (ψ x, s x)) = (ref.prod Measure.count).withDensity H)
    (i : I) (U : Set Z) (hU : MeasurableSet U) :
    μ {x | s x = i ∧ ψ x ∈ U} = ∫⁻ z in U, H (z, i) ∂ref := by
  rw [← k4_crop_base_finite_tail.withDensity_prod_singleton ref hH hU i,
    ← hlaw, Measure.map_apply (hψ.prodMk hs) (hU.prod (measurableSet_singleton i))]
  congr 1
  ext x
  simp [and_comm]

open Classical in
/-- Arbitrary compatible label systems transfer upper tails under disjoint restrictions.
The multiplicity counts source labels for a fixed target label. -/
theorem restricted_label_upper_tail {X Z I J Γ : Type*}
    [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] [Fintype Γ]
    (ref : Measure Z) [SigmaFinite ref] (μ : Measure X)
    (ψ : X → Z) (hψ : Measurable ψ) (s : X → I) (hs : Measurable s)
    (t : Γ → X → J) (ht : ∀ γ, Measurable (t γ))
    (S : Γ → Set X) (hS : ∀ γ, MeasurableSet (S γ))
    (hdisj : Pairwise fun γ γ' => Disjoint (S γ) (S γ'))
    (H : Z × I → ENNReal) (hH : Measurable H)
    (hfull : μ.map (fun x => (ψ x, s x)) = (ref.prod Measure.count).withDensity H)
    (Hpart : Γ → Z × I → ENNReal) (hHpart : ∀ γ, Measurable (Hpart γ))
    (hpart : ∀ γ, (μ.restrict (S γ)).map (fun x => (ψ x, s x)) =
      (ref.prod Measure.count).withDensity (Hpart γ))
    (G : Γ → Z × J → ENNReal) (hG : ∀ γ, Measurable (G γ))
    (htarget : ∀ γ, (μ.restrict (S γ)).map (fun x => (ψ x, t γ x)) =
      (ref.prod Measure.count).withDensity (G γ))
    (R : Γ → I → J → Prop)
    (hR : ∀ γ, ∀ᵐ x ∂μ.restrict (S γ), R γ (s x) (t γ x))
    (D : ENNReal) (hD : ∀ γ j, ∑' i, (if R γ i j then (1 : ENNReal) else 0) ≤ D)
    (δ hi : ENNReal) :
    (∑ γ, (μ.restrict (S γ)) {x | hi < δ * G γ (ψ x, t γ x)}) ≤
      μ {x | hi < H (ψ x, s x)} + δ * D * μ univ := by
  classical
  let B : Set X := {x | hi < H (ψ x, s x)}
  let L : Γ → Set X := fun γ => {x | Hpart γ (ψ x, s x) < δ * G γ (ψ x, t γ x)}
  have hlow (γ : Γ) : (μ.restrict (S γ)) (L γ) ≤ δ * D * (μ.restrict (S γ)) univ := by
    apply k4_scalar_grid_density_extension.relation_low_density_mass
      (μ.restrict (S γ)) ref ψ s (t γ)
      (fun j => measurableSet_eq_fun (ht γ) measurable_const)
      (fun z i => Hpart γ (z, i)) (fun z j => G γ (z, j))
      (fun i => (hHpart γ).comp (measurable_id.prodMk measurable_const))
      (fun j => (hG γ).comp (measurable_id.prodMk measurable_const))
      (label_density_slice ref (μ.restrict (S γ)) ψ hψ s hs (Hpart γ) (hHpart γ) (hpart γ))
      (label_density_slice ref (μ.restrict (S γ)) ψ hψ (t γ) (ht γ) (G γ) (hG γ) (htarget γ))
      (R γ) (hR γ) D (hD γ) δ
  have hterm (γ : Γ) :
      (μ.restrict (S γ)) {x | hi < δ * G γ (ψ x, t γ x)} ≤
        (μ.restrict (S γ)) B + δ * D * (μ.restrict (S γ)) univ := by
    have hmono := k4_crop_base_finite_tail.restricted_observation_density_le
      (ref.prod Measure.count) μ (fun x => (ψ x, s x)) (hψ.prodMk hs)
      (S γ) (Hpart γ) H (hHpart γ) hH (hpart γ) hfull
    have hsub : {x | hi < δ * G γ (ψ x, t γ x)} ≤ᵐ[μ.restrict (S γ)] B ∪ L γ := by
      filter_upwards [hmono] with x hx hbad
      by_cases hb : x ∈ B
      · exact Or.inl hb
      · exact Or.inr ((hx.trans (not_lt.mp hb)).trans_lt hbad)
    exact ((measure_mono_ae hsub).trans (measure_union_le _ _)).trans
      (add_le_add le_rfl (hlow γ))
  have hsum (U : Set X) : (∑ γ, (μ.restrict (S γ)) U) ≤ μ U := by
    have hm := k4_adapted_affine_cube_cover.sum_restrict_le_of_disjoint μ S univ
      hS hdisj (fun _ => subset_univ _)
    simpa only [Measure.restrict_univ, Measure.finsetSum_apply] using (Measure.le_iff'.mp hm U)
  calc
    _ ≤ ∑ γ, ((μ.restrict (S γ)) B + δ * D * (μ.restrict (S γ)) univ) :=
      Finset.sum_le_sum fun γ _ => hterm γ
    _ = (∑ γ, (μ.restrict (S γ)) B) + δ * D * ∑ γ, (μ.restrict (S γ)) univ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ μ B + δ * D * μ univ := add_le_add (hsum B) (mul_le_mul' le_rfl (hsum univ))

end Submission.Obl.k4_scalar_crop_profile_transport
