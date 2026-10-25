/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Renewal/Descendants.lean, whose original source was o222, session x0776,
   commit 6141c0189519ee10a8a74b6f7f39756f61c1639b, Descendants.lean.
   Here the null intersections of dyadic blocks use RowField's interval geometry. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowReadyOf

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- An incidence law dominated by product measure does not see the shared
endpoints of distinct blocks at a fixed dyadic level. -/
theorem ae_unique_block {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)}
    {K : ℝ≥0∞} (hdom : μ ≤ K • ν.prod volume) (T : ℕ) :
    ∀ᵐ z ∂μ, ∀ j j' : Fin (2 ^ T), j ≠ j' →
      ¬ (z.2 ∈ interval T j ∧ z.2 ∈ interval T j') := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro j'
  by_cases hj : j = j'
  · exact Filter.Eventually.of_forall fun z h => (h hj).elim
  have hvol : volume (interval T j ∩ interval T j') = 0 :=
    (interval_inter_subsingleton T hj).measure_zero volume
  have hnull : μ (univ ×ˢ (interval T j ∩ interval T j')) = 0 := by
    apply le_antisymm _ zero_le
    calc μ (univ ×ˢ (interval T j ∩ interval T j'))
        ≤ (K • ν.prod volume) (univ ×ˢ (interval T j ∩ interval T j')) := hdom _
      _ = 0 := by rw [Measure.smul_apply, Measure.prod_prod, hvol, mul_zero, smul_zero]
  have hae : ∀ᵐ z ∂μ, z ∉ univ ×ˢ (interval T j ∩ interval T j') := by
    rw [ae_iff]
    have hset : {z : α × ℝ | ¬ z ∉ univ ×ˢ (interval T j ∩ interval T j')} =
        univ ×ˢ (interval T j ∩ interval T j') := by
      ext z
      simp
    rw [hset]
    exact hnull
  exact hae.mono fun z hz _ hmem => hz ⟨mem_univ _, hmem⟩

/-- After nesting, all deeper labels covering a parent's incidences belong to
that parent, outside the null dyadic endpoints. -/
theorem ae_deepGood_cover (p : Parameters) (a : PreparedModel α) (k : ℕ)
    (hcommon : a.Common p) {r r' R : ℝ}
    (hparent : a.AtlasAt p R k r) (hdeep : a.AtlasAt p R k r')
    (hnest : ∀ i : Fin (a.n k r'), ∃ Q : Fin (a.n k r),
      a.A k r' i ⊆ a.A k r Q ∧ a.block k r' i ⊆ a.block k r Q)
    (Q : Fin (a.n k r)) :
    ∀ᵐ z ∂a.rho k, z.1 ∈ a.B k r Q → z.2 ∈ a.block k r Q →
      ∃ i, deepGood a k r r' Q i ∧ z.1 ∈ a.B k r' i ∧ z.2 ∈ a.block k r' i := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hρμ : a.rho k ≤ a.mu k := (hcommon k).2.2.2.2.1
  have hu := ae_unique_block ((hcommon k).2.2.2.1) (a.T k r)
  have hc := hdeep.2.2.2.2.2.1
  filter_upwards [ae_mono hρμ hu, ae_mono hρμ hc] with z huz hcz hzB hzI
  obtain ⟨i, hiB, hiI⟩ := hcz
  obtain ⟨Q', hAsub, hIsub⟩ := hnest i
  by_cases hQ : Q' = Q
  · subst Q'
    exact ⟨i, ⟨hAsub, hIsub⟩, hiB, hiI⟩
  · exfalso
    by_cases hj : a.j k r Q' = a.j k r Q
    · exact (Set.disjoint_left.mp (hparent.2.2.2.1 Q' Q hQ hj))
        (hAsub ((hdeep.2.2.1 i).2.2 hiB)) ((hparent.2.2.1 Q).2.2 hzB)
    · exact huz (a.j k r Q') (a.j k r Q) hj ⟨hIsub hiI, hzI⟩

end Submission.Obl.k4_narrow_projected_row_parents
