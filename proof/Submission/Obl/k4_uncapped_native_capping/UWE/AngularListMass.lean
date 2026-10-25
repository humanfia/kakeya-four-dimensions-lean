/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/AngularListMass.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/AngularListMass.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeBaseCeiling

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- A sampled joint-density ceiling bounds the unchanged submeasure by the
original pure observation law times counting measure. -/
theorem relative_joint_ceiling {Ω Y I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (τ : Measure Y)
    (O : Ω → Y) (hO : Measurable O) (A : Ω → I) (hA : Measurable A)
    (g : Y → ENNReal) (hg : Measurable g)
    (G : Y × I → ENNReal) (hG : Measurable G)
    (hpure : μ.map O = τ.withDensity g)
    (hjoint : μ.map (fun p => (O p, A p)) = (τ.prod Measure.count).withDensity G)
    (c : ENNReal) (hcap : ∀ᵐ p ∂ρ, G (O p, A p) ≤ c * g (O p)) :
    ρ.map (fun p => (O p, A p)) ≤ c • (μ.map O).prod Measure.count := by
  let J : Ω → Y × I := fun p => (O p, A p)
  have hJ : Measurable J := hO.prodMk hA
  let H : Set (Y × I) := {z | G z ≤ c * g z.1}
  have hH : MeasurableSet H := measurableSet_le hG (measurable_const.mul (hg.comp measurable_fst))
  have hsupport : ∀ᵐ z ∂ρ.map J, z ∈ H := by
    change ∀ᵐ z ∂ρ.map J, G z ≤ c * g z.1
    exact (ae_map_iff hJ.aemeasurable hH).2 hcap
  calc
    _ = (ρ.map J).restrict H := (Measure.restrict_eq_self_of_ae_mem hsupport).symm
    _ ≤ ((τ.prod Measure.count).withDensity G).restrict H := by
      rw [← hjoint]
      exact Measure.restrict_mono Subset.rfl (Measure.map_mono hρ hJ)
    _ = (τ.prod Measure.count).withDensity (H.indicator G) := by
      rw [restrict_withDensity hH, withDensity_indicator hH]
    _ ≤ (τ.prod Measure.count).withDensity (fun z => c * g z.1) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall (fun z => by
        by_cases hz : z ∈ H
        · rw [indicator_of_mem hz]; exact hz
        · simp only [indicator_of_notMem hz]; exact zero_le)
    _ = c • (μ.map O).prod Measure.count := by
      rw [hpure, prod_withDensity_left hg]
      exact withDensity_smul c (show Measurable (fun z : Y × I => g z.1) from hg.comp measurable_fst)

/-- At most `D` permitted angular labels above each terminal observation cost
only `D` times the original pure mass of the observation window. -/
theorem angular_list_mass_le {Ω Y I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (τ : Measure Y)
    (O : Ω → Y) (hO : Measurable O) (A : Ω → I) (hA : Measurable A)
    (g : Y → ENNReal) (hg : Measurable g)
    (G : Y × I → ENNReal) (hG : Measurable G)
    (hpure : μ.map O = τ.withDensity g)
    (hjoint : μ.map (fun p => (O p, A p)) = (τ.prod Measure.count).withDensity G)
    (c D : ENNReal) (H : Set Y) (hH : MeasurableSet H)
    (V : Y → Finset I) (hV : ∀ i, MeasurableSet {o | i ∈ V o})
    (hcard : ∀ o, ((V o).card : ENNReal) ≤ D)
    (hgood : ∀ᵐ p ∂ρ, O p ∈ H ∧ A p ∈ V (O p) ∧ G (O p, A p) ≤ c * g (O p)) :
    ρ univ ≤ c * D * μ (O ⁻¹' H) := by
  classical
  let U : Set (Y × I) := {z | z.1 ∈ H ∧ z.2 ∈ V z.1}
  have hU : MeasurableSet U := by
    have heq : U = ⋃ i : I, {z : Y × I | z.1 ∈ H ∧ i ∈ V z.1 ∧ z.2 = i} := by
      ext z
      simp [U]
    rw [heq]
    exact MeasurableSet.iUnion (fun i => (hH.preimage measurable_fst).inter
      (((hV i).preimage measurable_fst).inter
        ((measurableSet_singleton i).preimage measurable_snd)))
  have hmass : (ρ.map (fun p => (O p, A p))) U = ρ univ := by
    rw [Measure.map_apply (hO.prodMk hA) hU]
    apply measure_congr
    filter_upwards [hgood] with p hp
    apply propext
    change (O p ∈ H ∧ A p ∈ V (O p)) ↔ True
    exact iff_true_intro ⟨hp.1, hp.2.1⟩
  have hdom := relative_joint_ceiling μ ρ hρ τ O hO A hA g hg G hG hpure hjoint c
    (hgood.mono (fun p hp => hp.2.2))
  have href : ((μ.map O).prod Measure.count) U ≤ D * (μ.map O) H := by
    apply Submission.Obl.k4_scalar_angular_pair_agreement.prod_mass_le_fiber_bound
      (μ.map O) Measure.count H U D hU
    · exact fun z hz => hz.1
    · intro o ho
      have heq : {i : I | (o, i) ∈ U} = (V o : Set I) := by ext i; simp [U, ho]
      rw [heq, Measure.count_apply_finset]
      exact hcard o
  calc
    _ = (ρ.map (fun p => (O p, A p))) U := hmass.symm
    _ ≤ (c • (μ.map O).prod Measure.count) U := hdom U
    _ = c * ((μ.map O).prod Measure.count) U := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ c * (D * (μ.map O) H) := by gcongr
    _ = _ := by rw [Measure.map_apply hO hH]; ring

/-- The pure denominator is integrated through its exact coarse observation.
The number of terminal hidden labels does not enter the estimate. -/
theorem angular_list_coarse_window_mass_le {Ω Y I X J : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (τ : Measure Y)
    (O : Ω → Y) (hO : Measurable O) (A : Ω → I) (hA : Measurable A)
    (g : Y → ENNReal) (hg : Measurable g)
    (G : Y × I → ENNReal) (hG : Measurable G)
    (hpure : μ.map O = τ.withDensity g)
    (hjoint : μ.map (fun p => (O p, A p)) = (τ.prod Measure.count).withDensity G)
    (σ : Measure X) (q : Y → X × J) (hq : Measurable q)
    (g₀ : X × J → ENNReal) (hg₀ : Measurable g₀)
    (hcoarse : μ.map (q ∘ O) = (σ.prod Measure.count).withDensity g₀)
    (H₀ : Set (X × J)) (hH₀ : MeasurableSet H₀)
    (S : Set X) (hS : MeasurableSet S) (c D M C : ENNReal)
    (hcount : ∀ x, Measure.count {j : J | (x, j) ∈ H₀} ≤ C)
    (V : Y → Finset I) (hV : ∀ i, MeasurableSet {o | i ∈ V o})
    (hcard : ∀ o, ((V o).card : ENNReal) ≤ D)
    (hgood : ∀ᵐ p ∂ρ, (q (O p)).1 ∈ S ∧ q (O p) ∈ H₀ ∧
      g₀ (q (O p)) ≤ M ∧ A p ∈ V (O p) ∧ G (O p, A p) ≤ c * g (O p)) :
    ρ univ ≤ c * D * M * C * σ S := by
  let U : Set (X × J) := (S ×ˢ univ) ∩ H₀
  have hU : MeasurableSet U := (hS.prod MeasurableSet.univ).inter hH₀
  let H : Set Y := {o | q o ∈ U ∧ g₀ (q o) ≤ M}
  have hH : MeasurableSet H := (hU.preimage hq).inter
    (measurableSet_le (hg₀.comp hq) measurable_const)
  have href : (σ.prod Measure.count) U ≤ C * σ S := by
    apply Submission.Obl.k4_scalar_angular_pair_agreement.prod_mass_le_fiber_bound
      σ Measure.count S U C hU
    · exact fun z hz => hz.1.1
    · intro x hx
      exact (measure_mono (show {j : J | (x, j) ∈ U} ⊆ {j : J | (x, j) ∈ H₀}
        from fun _ hj => hj.2)).trans (hcount x)
  have hmass : μ (O ⁻¹' H) ≤ M * (C * σ S) := by
    exact Submission.Obl.k4_scalar_angular_pair_agreement.capped_observation_mass_le
      μ (σ.prod Measure.count) (q ∘ O) (hq.comp hO) g₀ hg₀ hcoarse U hU M (C * σ S) href
  have hretained : ρ univ ≤ c * D * μ (O ⁻¹' H) := by
    apply angular_list_mass_le μ ρ hρ τ O hO A hA g hg G hG hpure hjoint c D H hH V hV hcard
    filter_upwards [hgood] with p hp
    exact ⟨⟨⟨⟨hp.1, mem_univ _⟩, hp.2.1⟩, hp.2.2.1⟩, hp.2.2.2⟩
  calc
    _ ≤ c * D * μ (O ⁻¹' H) := hretained
    _ ≤ c * D * (M * (C * σ S)) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_uncapped_native_capping.UWE
