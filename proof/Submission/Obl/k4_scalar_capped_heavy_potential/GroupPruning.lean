import Mathlib
import Submission.Lib.K4ReferencePruning

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open MeasureTheory Set
open Submission.Lib.K4ReferencePruning

noncomputable section

/-- A state's old mass is charged once for each possible intercept group. -/
def groupReferenceWeight {Ω Q C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (F : Q → Finset C) (q : Q × C) : ENNReal := by
  classical
  exact if q.2 ∈ F q.1 then μ (state ⁻¹' {q.1}) else 0

/-- Delete light portions of an intercept group at each original fine state. -/
def groupStateKeep {Ω Q C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (group : Ω → C) (F : Q → Finset C)
    (δ : ENNReal) : Set Ω :=
  referenceKeep μ (fun p => (state p, group p)) (groupReferenceWeight μ state F) δ

/-- The retained original law of one intercept group. -/
def retainedGroup {Ω Q C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (group : Ω → C) (F : Q → Finset C)
    (δ : ENNReal) (c : C) : Measure Ω :=
  (μ.restrict (groupStateKeep μ state group F δ)).restrict (group ⁻¹' {c})

theorem group_reference_weight_sum_le {Ω Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Countable Q] [Countable C]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (F : Q → Finset C) (J : ENNReal) (hF : ∀ q, (F q).card ≤ J) :
    (∑' qc : Q × C, groupReferenceWeight μ state F qc) ≤ J * μ univ := by
  classical
  have hsum : (∑' q, μ (state ⁻¹' {q})) = μ univ := by
    rw [← measure_iUnion]
    · congr 1
      ext p
      simp
    · intro q q' hqq'
      exact disjoint_left.mpr fun p hp hp' => hqq' (hp.symm.trans hp')
    · intro q
      exact hs (measurableSet_singleton q)
  rw [ENNReal.tsum_prod']
  calc
    (∑' q, ∑' c, groupReferenceWeight μ state F (q, c)) =
        ∑' q, (F q).card * μ (state ⁻¹' {q}) := by
      apply tsum_congr
      intro q
      have hh : (∑' c, groupReferenceWeight μ state F (q, c)) =
          ∑ c ∈ F q, groupReferenceWeight μ state F (q, c) := by
        apply tsum_eq_sum
        intro c hc
        simp [groupReferenceWeight, hc]
      rw [hh]
      simp [groupReferenceWeight]
    _ ≤ ∑' q, J * μ (state ⁻¹' {q}) :=
      ENNReal.tsum_le_tsum fun q => mul_le_mul' (hF q) le_rfl
    _ = J * μ univ := by rw [ENNReal.tsum_mul_left, hsum]

/-- Statewise light-group deletion costs the cutoff times the number of
possible groups, relative to the unchanged original incidence mass. -/
theorem group_state_pruning_mass_budget {Ω Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Countable Q] [Countable C]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (group : Ω → C) (hg : Measurable group) (F : Q → Finset C)
    (δ J : ENNReal) (hF : ∀ q, (F q).card ≤ J) :
    μ univ ≤ (μ.restrict (groupStateKeep μ state group F δ)) univ + δ * J * μ univ := by
  have h := reference_pruning_mass_budget μ (fun p => (state p, group p))
    (hs.prodMk hg) (groupReferenceWeight μ state F) δ
  have hbound := add_le_add
    (le_refl ((μ.restrict (groupStateKeep μ state group F δ)) univ))
    (mul_le_mul' (le_refl δ) (group_reference_weight_sum_le μ state hs F J hF))
  simpa only [groupStateKeep, mul_assoc] using h.trans hbound

/-- After deleting statewise light groups, every original palette cap
becomes a relative cap inside each retained group. This applies separately
to every original velocity width, with the same retained law. -/
theorem retained_group_event_cap {Ω Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (group : Ω → C) (hg : Measurable group) (F : Q → Finset C)
    (δ K b : ENNReal) (hδ₀ : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hsupport : ∀ q c, c ∉ F q → μ {p | state p = q ∧ group p = c} = 0)
    (A : Set Ω) (q : Q) (c : C)
    (hcap : μ {p | state p = q ∧ p ∈ A} ≤ K * μ (state ⁻¹' {q}) * b) :
    (retainedGroup μ state group F δ c) {p | state p = q ∧ p ∈ A} ≤
      (K / δ) * (retainedGroup μ state group F δ c) (state ⁻¹' {q}) * b := by
  classical
  let code : Ω → Q × C := fun p => (state p, group p)
  let ν := μ.restrict (groupStateKeep μ state group F δ)
  let σ := retainedGroup μ state group F δ c
  have hσμ : σ ≤ μ := (Measure.restrict_le_self).trans Measure.restrict_le_self
  have hmass : σ (state ⁻¹' {q}) =
      if δ * groupReferenceWeight μ state F (q, c) ≤ μ (code ⁻¹' {(q, c)})
      then μ (code ⁻¹' {(q, c)}) else 0 := by
    have hr := reference_kept_state_mass μ code (hs.prodMk hg)
      (groupReferenceWeight μ state F) δ (q, c)
    have hid : (state ⁻¹' {q}) ∩ (group ⁻¹' {c}) = code ⁻¹' {(q, c)} := by
      ext p
      simp [code, Prod.ext_iff]
    dsimp only [σ, retainedGroup]
    rw [Measure.restrict_apply (hs (measurableSet_singleton q)), hid]
    exact hr
  have hzero (hz : σ (state ⁻¹' {q}) = 0) :
      σ {p | state p = q ∧ p ∈ A} ≤ (K / δ) * σ (state ⁻¹' {q}) * b := by
    calc
      _ ≤ σ (state ⁻¹' {q}) := measure_mono fun p hp => hp.1
      _ = 0 := hz
      _ ≤ _ := zero_le
  by_cases hc : c ∈ F q
  · by_cases hk : δ * groupReferenceWeight μ state F (q, c) ≤ μ (code ⁻¹' {(q, c)})
    · have hmass' : σ (state ⁻¹' {q}) = μ (code ⁻¹' {(q, c)}) := by simpa [hk] using hmass
      have hfloor : δ * μ (state ⁻¹' {q}) ≤ σ (state ⁻¹' {q}) := by
        rw [hmass']
        simpa only [groupReferenceWeight, hc, ite_true] using hk
      have hinv : μ (state ⁻¹' {q}) ≤ δ⁻¹ * σ (state ⁻¹' {q}) := by
        calc
          _ = δ⁻¹ * (δ * μ (state ⁻¹' {q})) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hδ₀ hδtop, one_mul]
          _ ≤ _ := mul_le_mul' le_rfl hfloor
      calc
        _ ≤ μ {p | state p = q ∧ p ∈ A} := hσμ _
        _ ≤ K * μ (state ⁻¹' {q}) * b := hcap
        _ ≤ K * (δ⁻¹ * σ (state ⁻¹' {q})) * b := by gcongr
        _ = _ := by rw [div_eq_mul_inv]; ring
    · exact hzero (by simpa only [hk, ite_false] using hmass)
  · have hz : μ (code ⁻¹' {(q, c)}) = 0 := by
      rw [show code ⁻¹' {(q, c)} = {p | state p = q ∧ group p = c} by
        ext p
        simp [code, Prod.ext_iff]]
      exact hsupport q c hc
    apply hzero
    rw [hmass, hz]
    split_ifs <;> rfl


/-- The retained groups still partition the unchanged state-pruned
incidence law, provided the original law meets the finite group window. -/
theorem retained_group_mass_partition {Ω Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSingletonClass C]
    (μ : Measure Ω) (state : Ω → Q) (group : Ω → C) (hg : Measurable group)
    (lists : Q → Finset C) (δ : ENNReal) (F : Finset C)
    (hglobal : ∀ᵐ p ∂μ, group p ∈ F) :
    (∑ c ∈ F, retainedGroup μ state group lists δ c univ) =
      (μ.restrict (groupStateKeep μ state group lists δ)) univ := by
  simp only [retainedGroup, Measure.restrict_apply_univ]
  rw [sum_measure_preimage_singleton F (fun c _ => hg (measurableSet_singleton c))]
  have hs : ∀ᵐ p ∂μ.restrict (groupStateKeep μ state group lists δ), group p ∈ F :=
    ae_mono Measure.restrict_le_self hglobal
  rw [← Measure.restrict_apply_univ (μ := μ) (groupStateKeep μ state group lists δ)]
  apply measure_congr
  filter_upwards [hs] with p hp
  simp only [mem_preimage, Finset.mem_coe, hp, mem_univ]

/-- One intercept label per trajectory partitions the original prior;
its sum can never exceed the original packet prior. -/
theorem group_prior_mass_budget {α C : Type*}
    [MeasurableSpace α] [MeasurableSpace C] [MeasurableSingletonClass C]
    (ν : Measure α) (A : Set α) (group : α → C) (hg : Measurable group) (F : Finset C) :
    (∑ c ∈ F, (ν.restrict A) (group ⁻¹' {c})) ≤ ν A := by
  rw [sum_measure_preimage_singleton F (fun c _ => hg (measurableSet_singleton c))]
  exact (measure_mono (Set.subset_univ _)).trans_eq (Measure.restrict_apply_univ _)


/-- Incidence domination on a trajectory-supported measure uses the
original restricted prior, with no normalization factor. -/
theorem prior_restriction_domination {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ)) (H : ENNReal)
    (A : Set α) (hA : MeasurableSet A)
    (hdom : μ ≤ H • ν.prod volume) (hsupport : ∀ᵐ p ∂μ, p.1 ∈ A) :
    μ ≤ H • (ν.restrict A).prod volume := by
  have hm : μ.restrict (A ×ˢ (univ : Set ℝ)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (hsupport.mono (by intro p hp; exact ⟨hp, mem_univ _⟩))
  calc
    μ = μ.restrict (A ×ˢ (univ : Set ℝ)) := hm.symm
    _ ≤ (H • ν.prod volume).restrict (A ×ˢ univ) := Measure.restrict_mono le_rfl hdom
    _ = H • (ν.restrict A).prod volume := by
      rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]

/-- A selected group's density ceiling is against that group's original
trajectory prior. This is the input to the planar Kakeya area estimate. -/
theorem retained_group_prior_domination {α Q : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ)) (H : ENNReal)
    (state : α × ℝ → Q) (group : α → ℤ) (hg : Measurable group)
    (lists : Q → Finset ℤ) (δ : ENNReal) (c : ℤ)
    (hdom : μ ≤ H • ν.prod volume) :
    retainedGroup μ state (fun p => group p.1) lists δ c ≤
      H • (ν.restrict (group ⁻¹' {c})).prod volume := by
  apply prior_restriction_domination ν _ H _ (hg (measurableSet_singleton c))
    ((Measure.restrict_le_self.trans Measure.restrict_le_self).trans hdom)
  exact ae_restrict_mem ((hg.comp measurable_fst) (measurableSet_singleton c))


/-- A bounded original density on a bounded time interval makes the
incidence law finite, before any conditional or real-mass operations. -/
theorem finite_incidence_of_time_support {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    (H : ENNReal) (hH : H ≠ ⊤) (a b : ℝ)
    (hdom : μ ≤ H • ν.prod volume) (hsupport : ∀ᵐ p ∂μ, p.2 ∈ Icc a b) :
    IsFiniteMeasure μ := by
  constructor
  calc
    μ univ = μ (univ ×ˢ Icc a b) := by
      apply measure_congr
      filter_upwards [hsupport] with p hp
      simp only [mem_univ, mem_prod, hp, and_self]
    _ ≤ (H • ν.prod volume) (univ ×ˢ Icc a b) := hdom _
    _ = H * (ν univ * volume (Icc a b)) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod]
    _ < ⊤ := by rw [Real.volume_Icc]; finiteness

end
end Submission.Obl.k4_scalar_capped_heavy_potential
