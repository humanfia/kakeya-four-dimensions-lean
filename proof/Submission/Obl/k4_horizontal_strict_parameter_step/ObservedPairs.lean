/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ObservedPairs.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Lib.K4MeshListRecovery.MeasurableLists
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- A measurable member can be chosen from any nonempty finite cover.
The choice depends only on the finite measurable incidence record. -/
theorem measurable_finite_member {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ f : Ω → ι, Measurable f ∧ ∀ p, (∃ i, p ∈ A i) → p ∈ A (f p) := by
  classical
  obtain ⟨f, hf, hmax⟩ := Submission.Lib.K4MeshListRecovery.exists_measurable_finite_argmax
    (fun i => (A i).indicator (1 : Ω → ℝ))
    (fun i => measurable_const.indicator (hA i))
  refine ⟨f, measurable_to_countable (fun p => hf (f p)), ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := hp
  have hh := hmax p i
  by_contra hn
  norm_num only [indicator_of_mem hi, indicator_of_notMem hn, Pi.one_apply] at hh

/-- Every finite mark has an original support representative. The two decoded
labels name whole assignments, rather than newly normalized pair components. -/
structure ObservedPairs {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (S : Set Ω) (A : Fin m → Set Ω) (B : Fin n → Set Ω) where
  count : ℕ
  positive : 0 < count
  mark : Ω → Fin count
  mark_measurable : Measurable mark
  old : Fin count → Fin m
  native : Fin count → Fin n
  representative : Fin count → Ω
  representative_support : ∀ i, representative i ∈ S
  representative_old : ∀ i, representative i ∈ A (old i)
  representative_native : ∀ i, representative i ∈ B (native i)
  decode_old : ∀ p ∈ S, p ∈ A (old (mark p))
  decode_native : ∀ p ∈ S, p ∈ B (native (mark p))

/-- Restricting a finite code to the actual support removes unused pair records
and leaves an actual original witness for every resulting mark. -/
theorem exists_observed_pairs {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (S : Set Ω) (hS : MeasurableSet S) (hSne : S.Nonempty)
    (A : Fin m → Set Ω) (B : Fin n → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcovA : ∀ p ∈ S, ∃ i, p ∈ A i) (hcovB : ∀ p ∈ S, ∃ i, p ∈ B i) :
    Nonempty (ObservedPairs S A B) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hSne
  haveI : Nonempty (Fin m) := ⟨Classical.choose (hcovA p₀ hp₀)⟩
  haveI : Nonempty (Fin n) := ⟨Classical.choose (hcovB p₀ hp₀)⟩
  obtain ⟨f, hf, hfa⟩ := measurable_finite_member A hA
  obtain ⟨g, hg, hgb⟩ := measurable_finite_member B hB
  obtain ⟨r, hr, X, decode, hX, hdecode, hrepr⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_on
      S hS ⟨p₀, hp₀⟩ (fun p => (f p, g p)) (hf.prodMk hg) (Set.toFinite _)
  let rep : Fin r → Ω := fun i => Classical.choose (hrepr i)
  have hrep (i : Fin r) : rep i ∈ S ∧ (f (rep i), g (rep i)) = decode i :=
    Classical.choose_spec (hrepr i)
  refine ⟨{
    count := r
    positive := hr
    mark := X
    mark_measurable := hX
    old := fun i => (decode i).1
    native := fun i => (decode i).2
    representative := rep
    representative_support := fun i => (hrep i).1
    representative_old := ?_
    representative_native := ?_
    decode_old := ?_
    decode_native := ?_ }⟩
  · intro i
    have hh := hfa (rep i) (hcovA _ (hrep i).1)
    simpa only [← congrArg Prod.fst (hrep i).2] using hh
  · intro i
    have hh := hgb (rep i) (hcovB _ (hrep i).1)
    simpa only [← congrArg Prod.snd (hrep i).2] using hh
  · intro p hp
    simpa only [congrArg Prod.fst (hdecode p hp)] using hfa p (hcovA p hp)
  · intro p hp
    simpa only [congrArg Prod.snd (hdecode p hp)] using hgb p (hcovB p hp)

namespace ObservedPairs

variable {Ω Γ J : Type*} [MeasurableSpace Ω] [DecidableEq Γ] [DecidableEq J]
  {m n : ℕ} {S : Set Ω} {A : Fin m → Set Ω} {B : Fin n → Set Ω}
  (T : ObservedPairs S A B) (group : Fin m → Γ) (block : Fin n → J)

def sourceKey (i : Fin T.count) : Fin m × J := (T.old i, block (T.native i))
def witnessKey (i : Fin T.count) : Fin n × Γ := (T.native i, group (T.old i))

def sourceMenu : Finset (Fin m × J) := Finset.univ.image (T.sourceKey block)
def witnessMenu : Finset (Fin n × Γ) := Finset.univ.image (T.witnessKey group)

/-- The comparison indices contain only domains that occur in the original
support. Several pair marks may share one source or witness domain. -/
abbrev Index := (T.sourceMenu block) ⊕ (T.witnessMenu group)

def source (i : Fin T.count) : T.Index group block :=
  Sum.inl ⟨T.sourceKey block i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

def witness (i : Fin T.count) : T.Index group block :=
  Sum.inr ⟨T.witnessKey group i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

def colour : T.Index group block → Γ × J
  | Sum.inl i => (group i.val.1, i.val.2)
  | Sum.inr i => (i.val.2, block i.val.1)

theorem colour_source_eq_witness (i : Fin T.count) :
    T.colour group block (T.source group block i) =
      T.colour group block (T.witness group block i) := rfl

/-- A witness-domain index comes with a genuine contact in its old group. -/
theorem witness_representative (i : T.witnessMenu group) :
    ∃ p ∈ S, p ∈ B i.val.1 ∧ ∃ h : Fin m, group h = i.val.2 ∧ p ∈ A h := by
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp i.property
  refine ⟨T.representative r, T.representative_support r, ?_, T.old r, ?_,
    T.representative_old r⟩
  · simpa only [← congrArg Prod.fst hr, witnessKey] using T.representative_native r
  · exact congrArg Prod.snd hr

end ObservedPairs

end

end Submission.Obl.k4_horizontal_strict_parameter_step
