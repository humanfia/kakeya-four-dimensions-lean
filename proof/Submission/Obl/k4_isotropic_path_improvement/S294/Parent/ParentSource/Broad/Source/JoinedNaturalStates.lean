-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.JoinedNaturalStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/JoinedNaturalStates.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory

noncomputable section

/-- Encode both actual state labels GLOBALLY. The readout is the same
original row table on every incidence, while its used natural labels
are finite whenever the physical labels are finite and each physical
label has its actual finite row menu. No source or measure is changed. -/
theorem exists_joined_natural_states
    {Ω I J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    (physical : Ω → I) (hphysical : Measurable physical)
    (rowState : Ω → J) (hrowState : Measurable rowState)
    (S : Set Ω) (hfinite : (physical '' S).Finite)
    (menu : I → Finset J) (hmenu : ∀ z∈S, rowState z∈menu (physical z))
    (row : J → Fin 3 → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ j a, |row j a| ≤ bound) :
    ∃ (state : Ω → ℕ) (value : ℕ → Fin 3 → ℝ),
      Measurable state ∧ (state '' S).Finite ∧
      (∀ x y, state x=state y ↔ physical x=physical y ∧ rowState x=rowState y) ∧
      (∀ z, value (state z)=row (rowState z)) ∧
      ∀ n a, |value n a| ≤ bound := by
  classical
  let : Encodable (I×J) := Encodable.ofCountable (I×J)
  let state := fun z : Ω => Encodable.encode (physical z,rowState z)
  let value : ℕ → Fin 3 → ℝ := fun n =>
    match Encodable.decode (α:=I×J) n with
    | none => 0
    | some pair => row pair.2
  have hstate : Measurable state :=
    (measurable_of_countable (Encodable.encode : I×J → ℕ)).comp (hphysical.prodMk hrowState)
  let used : Finset ℕ := hfinite.toFinset.biUnion fun i =>
    (menu i).image fun j => Encodable.encode (i,j)
  have hused : state '' S⊆(used : Set ℕ) := by
    rintro n ⟨z,hz,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨physical z,hfinite.mem_toFinset.mpr ⟨z,hz,rfl⟩,
      Finset.mem_image.mpr ⟨rowState z,hmenu z hz,rfl⟩⟩
  refine ⟨state,value,hstate,used.finite_toSet.subset hused,?_,?_,?_⟩
  · intro x y
    change Encodable.encode (physical x,rowState x)=Encodable.encode (physical y,rowState y) ↔ _
    rw [Encodable.encode_injective.eq_iff,Prod.mk.injEq]
  · intro z
    simp only [value,state,Encodable.encodek]
  · intro n a
    cases hd : Encodable.decode (α:=I×J) n with
    | none => simpa only [value,hd,Pi.zero_apply,abs_zero] using hbound
    | some pair => simpa only [value,hd] using hrow pair.2 a

/-- A global faithful coding of the joined labels preserves every
conditional ratio exactly. This includes natural labels outside the
actual image, whose fibers are empty. -/
theorem joined_state_ratios_to_natural_codes
    {Ω I J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → ℕ) (physical : Ω → I) (row : Ω → J)
    (hstate : ∀ x y, state x=state y ↔ physical x=physical y ∧ row x=row y)
    (keep B : Set Ω) (cap : ENNReal)
    (hcap : ∀ i j, μ ((keep∩{z | physical z=i ∧ row z=j})∩B) ≤
      cap*μ (keep∩{z | physical z=i ∧ row z=j})) :
    ∀ n, μ ((keep∩state ⁻¹' {n})∩B) ≤ cap*μ (keep∩state ⁻¹' {n}) := by
  intro n
  by_cases hn : ∃ x : Ω, state x=n
  · obtain ⟨x,hx⟩ := hn
    have heq : state ⁻¹' {n}={z | physical z=physical x ∧ row z=row x} := by
      ext z
      change (state z=n) ↔ _
      rw [←hx]
      exact hstate z x
    rw [heq]
    exact hcap (physical x) (row x)
  · have heq : state ⁻¹' {n}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hn ⟨x,hx⟩
    simp only [heq,inter_empty,empty_inter,measure_empty,mul_zero,le_refl]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
