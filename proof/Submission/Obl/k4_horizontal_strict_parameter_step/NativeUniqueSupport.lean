/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeUniqueSupport.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeObservedPredictors

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

/-- Pointwise original support for a coarse comparison. The unique closed
coarse time block ensures that a finer nested ancestor is the observed true
parent. Later density preparations keep this event pointwise. -/
structure NativeComparisonSupport {α : Type} [MeasurableSpace α]
    (cfg : NativeModel α) (k : ℕ) (s : ℝ) (σ : Measure (α × ℝ))
    {m : ℕ} (AH : Fin m → Set α) where
  event : Set (α × ℝ)
  measurable : MeasurableSet event
  conull : ∀ᵐ p ∂σ, p ∈ event
  unit : ∀ p ∈ event, p.2 ∈ Icc (0 : ℝ) 1
  coefficients : ∀ p ∈ event, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k
  contact : ∀ p ∈ event, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)
  unique_block : ∀ p ∈ event, ∀ j j' : Fin (2 ^ cfg.T k s),
    p.2 ∈ Data.I (cfg.T k s) j → p.2 ∈ Data.I (cfg.T k s) j' → j = j'
  table : ObservedPairs event (fun i => AH i ×ˢ (univ : Set ℝ))
    (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i))

namespace NativeComparisonSupport

/-- Nesting identifies the genuine ancestor with the coarse native label
already observed at this point. All certificates hold pointwise on the stored
support, so this remains true after later chart restrictions. -/
theorem nested_parent_eq {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
    {k : ℕ} {s t : ℝ} {σ : Measure (α × ℝ)} {m : ℕ} {AH : Fin m → Set α}
    (S : NativeComparisonSupport cfg k s σ AH)
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k t)
    (p : α × ℝ) (hp : p ∈ S.event)
    (i : Fin (cfg.n k t)) (j : Fin (cfg.n k s))
    (hA : cfg.A k t i ⊆ cfg.A k s j)
    (hI : Data.I (cfg.T k t) (cfg.j k t i) ⊆ Data.I (cfg.T k s) (cfg.j k s j))
    (hchild : p ∈ cfg.B k t i ×ˢ Data.I (cfg.T k t) (cfg.j k t i)) :
    j = S.table.native (S.table.mark p) := by
  have hn := S.table.decode_native p hp
  have hblock := S.unique_block p hp _ _ (hI hchild.2) hn.2
  by_contra hne
  exact Set.disjoint_left.mp (parent.disjoint j _ hne hblock)
    (hA (child.fitted_subset i hchild.1)) (parent.fitted_subset _ hn.1)

/-- Re-observing an actual representative gives the same colour. Old
assignments are disjoint and the stored coarse block is unique pointwise. -/
theorem representative_colour {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
    {k : ℕ} {s ε D a : ℝ} {σ : Measure (α × ℝ)} {m : ℕ} {AH : Fin m → Set α}
    {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (r : Fin S.table.count) :
    S.table.colour group (cfg.j k s)
        (S.table.source group (cfg.j k s) (S.table.mark (S.table.representative r))) =
      S.table.colour group (cfg.j k s) (S.table.source group (cfg.j k s) r) := by
  let p := S.table.representative r
  have hp := S.table.representative_support r
  have hold : S.table.old (S.table.mark p) = S.table.old r := by
    by_contra hn
    exact Set.disjoint_left.mp (H.2.1 _ _ hn)
      (S.table.decode_old p hp).1 (S.table.representative_old r).1
  have hblock := S.unique_block p hp _ _ (S.table.decode_native p hp).2
    (S.table.representative_native r).2
  change (group (S.table.old (S.table.mark p)), cfg.j k s (S.table.native (S.table.mark p))) =
    (group (S.table.old r), cfg.j k s (S.table.native r))
  rw [hold, hblock]

/-- Every actual comparison index has an original point with its colour. This
permits pointwise menu bounds to give unconditional sheet derivative bounds. -/
theorem index_has_colour_point {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
    {k : ℕ} {s ε D a : ℝ} {σ : Measure (α × ℝ)} {m : ℕ} {AH : Fin m → Set α}
    {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (i : S.table.Index group (cfg.j k s)) :
    ∃ p ∈ S.event, S.table.colour group (cfg.j k s) i =
      S.table.colour group (cfg.j k s) (S.table.source group (cfg.j k s) (S.table.mark p)) := by
  obtain ⟨r, hi | hi⟩ := S.table.index_observed group (cfg.j k s) i
  · refine ⟨S.table.representative r, S.table.representative_support r, ?_⟩
    rw [hi]
    exact (S.representative_colour H r).symm
  · refine ⟨S.table.representative r, S.table.representative_support r, ?_⟩
    rw [hi]
    exact (S.table.colour_source_eq_witness group (cfg.j k s) r).symm.trans
      (S.representative_colour H r).symm

end NativeComparisonSupport

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- All original coarse comparison certificates can be made pointwise on one
measurable conull event before the actual finite observed table is constructed. -/
theorem exists_comparison_support {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hbasic : cfg.Basic) (hK : 0 ≤ cfg.K k)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k) (hσ0 : σ univ ≠ 0)
    {ε D a₀ : ℝ} {m : ℕ} {AH : Fin m → Set α} {qH : Fin m → Fin 3 → ℤ}
    {hH : Fin m → Fin 6 → ℝ}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a₀ m AH qH hH) :
    Nonempty (NativeComparisonSupport cfg k s σ AH) := by
  classical
  obtain ⟨G₀, hG₀, hG₀ae, hG₀prop, ⟨T₀⟩⟩ :=
    cfg.observed_pair_support a hbasic hK σ hσ hσ0 H
  let Q : Set (α × ℝ) := {p | ∀ j j' : Fin (2 ^ cfg.T k s),
    p.2 ∈ Data.I (cfg.T k s) j → p.2 ∈ Data.I (cfg.T k s) j' → j = j'}
  have hQae : ∀ᵐ p ∂σ, p ∈ Q :=
    ae_unique_dyadic_block (cfg.ν k) σ (ENNReal.ofReal (cfg.K k))
      (hσ.trans (hbasic k).2.2.2.1) (cfg.T k s)
  have hQnm : NullMeasurableSet Q σ :=
    NullMeasurableSet.of_compl (NullMeasurableSet.of_null (ae_iff.mp hQae))
  obtain ⟨U, hUQ, hU, hUeq⟩ := hQnm.exists_measurable_subset_ae_eq
  have hUae : ∀ᵐ p ∂σ, p ∈ U := by
    filter_upwards [hQae, hUeq] with p hp hu
    exact hu.mpr hp
  let G := G₀ ∩ U
  have hG : MeasurableSet G := hG₀.inter hU
  have hGae : ∀ᵐ p ∂σ, p ∈ G := hG₀ae.and hUae
  have hGne : G.Nonempty := by
    by_contra hn
    have he : G = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hσ0
    have hz := ae_iff.mp hGae
    simpa only [he, mem_empty_iff_false, not_false_eq_true, Set.ofPred_true] using hz
  obtain ⟨T⟩ := exists_observed_pairs G hG hGne
    (fun i => AH i ×ˢ (univ : Set ℝ))
    (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i))
    (fun i => (H.1 i).prod MeasurableSet.univ)
    (fun i => (a.fitted_measurable i).prod measurableSet_Icc)
    (fun p hp => ⟨T₀.old (T₀.mark p), T₀.decode_old p hp.1⟩)
    (fun p hp => ⟨T₀.native (T₀.mark p), T₀.decode_native p hp.1⟩)
  exact ⟨{
    event := G
    measurable := hG
    conull := hGae
    unit := fun p hp => (hG₀prop p hp.1).1
    coefficients := fun p hp => (hG₀prop p hp.1).2.1
    contact := fun p hp => (hG₀prop p hp.1).2.2
    unique_block := fun p hp => hUQ hp.2
    table := T }⟩

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
