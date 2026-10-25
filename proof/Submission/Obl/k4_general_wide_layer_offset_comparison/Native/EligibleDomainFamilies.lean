-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/EligibleDomainFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/EligibleDomainFamilies.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.StoredWitnessPreparation

/-! Restrict each domain to its geometrically eligible original labels. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section

/-- Restrict a family to an explicit eligible-label menu. Every actual current
assignment decodes to the same old label, and the new count is the menu's card. -/
theorem OriginalSheetFamily.subfamily {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {D : ℕ} {a : ℝ} {K : NNReal}
    {base : Ω → EuclideanSpace ℝ (Fin 3)} {signal : Ω → ℝ}
    (F : OriginalSheetFamily μ D a K base signal) (hμ : μ univ ≠ 0)
    (S : Finset (Fin F.n)) (heligible : ∀ᵐ p ∂μ, F.index p ∈ S) :
    ∃ (F' : OriginalSheetFamily μ D a K base signal) (idx : Fin F'.n → Fin F.n),
      F'.n = S.card ∧ Function.Injective idx ∧ (∀ i, idx i ∈ S) ∧
      (∀ i, F'.f i = F.f (idx i)) ∧ (∀ i, F'.witness i = F.witness (idx i)) ∧
      ∀ᵐ p ∂μ, idx (F'.index p) = F.index p := by
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let idx : Fin (Fintype.card S) → Fin F.n := fun i => (e.symm i).val
  have hinj : Function.Injective idx := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ F.witness (idx i) := by
    filter_upwards [F.assigned, heligible] with p hp he
    refine ⟨e ⟨F.index p, he⟩, ?_⟩
    simpa only [idx, Equiv.symm_apply_apply] using hp
  obtain ⟨current, hmeas, hcurrent⟩ := reindex_assigned_family μ hμ F.witness F.disjoint_witness
    F.index F.measurable_index F.assigned idx hinj hcover
  let F' : OriginalSheetFamily μ D a K base signal :=
    { n := Fintype.card S
      index := current
      measurable_index := hmeas
      witness := fun i => F.witness (idx i)
      measurable_witness := fun i => F.measurable_witness _
      disjoint_witness := fun i j hij => F.disjoint_witness (fun h => hij (hinj h))
      assigned := hcurrent.mono fun p hp => hp.2
      source_norm := fun i p hp => F.source_norm _ p hp
      f := fun i => F.f (idx i)
      sheet := fun i => F.sheet _
      lipschitz := fun i => F.lipschitz _
      fit := fun i p hp => F.fit _ p hp }
  exact ⟨F', idx, by simp [F'], hinj, (fun i => (e.symm i).property),
    (fun _ => rfl), (fun _ => rfl), hcurrent.mono fun p hp => hp.1⟩

def eligibleDomainLabels {ι κ Q : Type*} [Fintype ι]
    (menus : ι → Finset Q) (decode : κ → Q) (d : κ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => decode d ∈ menus i)

/-- The complete reference sum of domain/label incidences is bounded by the old
label menus, provided each literal domain code is enumerated once. -/
theorem eligible_domain_reference_sum {ι κ Q : Type*} [Fintype ι] [Fintype κ]
    (menus : ι → Finset Q) (decode : κ → Q) (hdecode : Function.Injective decode)
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (∑ d, ((eligibleDomainLabels menus decode d).card : ℝ) * w (decode d)) ≤
      ∑ i, ∑ q ∈ menus i, w q := by
  calc
    _ = ∑ d, ∑ i ∈ eligibleDomainLabels menus decode d, w (decode d) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ d, ∑ i, if decode d ∈ menus i then w (decode d) else 0 := by
      simp only [eligibleDomainLabels, Finset.sum_filter]
    _ = ∑ i, ∑ d, if decode d ∈ menus i then w (decode d) else 0 := Finset.sum_comm
    _ ≤ ∑ i, ∑ q ∈ menus i, w q := by
      apply Finset.sum_le_sum
      intro i hi
      let G : Finset κ := Finset.univ.filter (fun d => decode d ∈ menus i)
      have hsub : G.image decode ⊆ menus i := by
        intro q hq
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hd).2
      calc
        _ = ∑ d ∈ G, w (decode d) := by simp only [G, Finset.sum_filter]
        _ = ∑ q ∈ G.image decode, w q :=
          (Finset.sum_image (fun d hd d' hd' h => hdecode h)).symm
        _ ≤ ∑ q ∈ menus i, w q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw q)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
