/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/AffinePalette.lean. Original attribution comments are retained below. -/
import Submission.Lib.K4ContactNormalization.AffineTimeTransfer
import Submission.Obl.k4_quadratic_atlas_normalization.Endpoints

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open scoped ENNReal

noncomputable section

/-- Success of one affine palette entry on a complete trajectory block. -/
def affineBlockFit {α : Type*} (b : α → Fin 6 → ℝ) (L : Fin 4 → ℝ)
    (s e E : ℝ) : Set α :=
  {l | ∀ t ∈ Icc s e, |eval (point (b l) t) (affineBase L) - point (b l) t 3| ≤ E}

/-- Whole-block success is a pair of endpoint tests, with no quantifier over
an uncountable time interval in the measurable selection. -/
theorem affineBlockFit_iff_endpoints {α : Type*} (b : α → Fin 6 → ℝ)
    (L : Fin 4 → ℝ) {s e E : ℝ} (hse : s ≤ e) (l : α) :
    l ∈ affineBlockFit b L s e E ↔
      |eval (point (b l) s) (affineBase L) - point (b l) s 3| ≤ E ∧
      |eval (point (b l) e) (affineBase L) - point (b l) e 3| ≤ E := by
  constructor
  · intro h
    exact ⟨h s ⟨le_rfl, hse⟩, h e ⟨hse, le_rfl⟩⟩
  · intro h t ht
    simp only [affine_hidden_residual] at h ⊢
    exact (Submission.Obl.k4_quadratic_atlas_normalization.abs_affine_le_endpoint_max
      _ _ s e t ht).trans (max_le h.1 h.2)

theorem measurableSet_affineBlockFit {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (L : Fin 4 → ℝ)
    {s e E : ℝ} (hse : s ≤ e) : MeasurableSet (affineBlockFit b L s e E) := by
  have heq : affineBlockFit b L s e E =
      {l | |eval (point (b l) s) (affineBase L) - point (b l) s 3| ≤ E} ∩
      {l | |eval (point (b l) e) (affineBase L) - point (b l) e 3| ≤ E} := by
    ext l
    exact affineBlockFit_iff_endpoints b L hse l
  rw [heq]
  simp only [affine_hidden_residual]
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) measurable_const

/-- The first successful entry gives disjoint measurable trajectory pieces
inside the original true label. -/
def affinePalettePiece {α : Type*} {M : ℕ} (b : α → Fin 6 → ℝ)
    (B : Set α) (L : Fin M → Fin 4 → ℝ) (s e E : ℝ) (u : Fin M) : Set α :=
  disjointed (fun v => B ∩ affineBlockFit b (L v) s e E) u

theorem affinePalettePiece_subset {α : Type*} {M : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin M → Fin 4 → ℝ)
    (s e E : ℝ) (u : Fin M) :
    affinePalettePiece b B L s e E u ⊆ B ∩ affineBlockFit b (L u) s e E :=
  disjointed_subset _ _

theorem measurableSet_affinePalettePiece {α : Type*} [MeasurableSpace α] {M : ℕ}
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (B : Set α) (hB : MeasurableSet B)
    (L : Fin M → Fin 4 → ℝ) {s e E : ℝ} (hse : s ≤ e) (u : Fin M) :
    MeasurableSet (affinePalettePiece b B L s e E u) := by
  unfold affinePalettePiece
  rw [disjointed_eq_inter_compl]
  exact (hB.inter (measurableSet_affineBlockFit b hb (L u) hse)).inter
    (MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      (hB.inter (measurableSet_affineBlockFit b hb (L v) hse)).compl)

theorem pairwiseDisjoint_affinePalettePiece {α : Type*} {M : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin M → Fin 4 → ℝ) (s e E : ℝ) :
    Pairwise (fun u v => Disjoint (affinePalettePiece b B L s e E u)
      (affinePalettePiece b B L s e E v)) := disjoint_disjointed _

theorem iUnion_affinePalettePiece {α : Type*} {M : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin M → Fin 4 → ℝ) (s e E : ℝ) :
    (⋃ u, affinePalettePiece b B L s e E u) =
      {l | l ∈ B ∧ ∃ u, l ∈ affineBlockFit b (L u) s e E} := by
  unfold affinePalettePiece
  rw [iUnion_disjointed]
  ext l
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_and_left]

/-- Successful entries split the original label's prior mass without ever
replacing its reference weight by the mass of a successful entry. -/
theorem sum_affinePalettePiece_le {α : Type*} [MeasurableSpace α] {M : ℕ}
    (ν : Measure α) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (B : Set α) (hB : MeasurableSet B) (L : Fin M → Fin 4 → ℝ)
    {s e E : ℝ} (hse : s ≤ e) :
    (∑ u, ν (affinePalettePiece b B L s e E u)) ≤ ν B := by
  have heq : ν (⋃ u, affinePalettePiece b B L s e E u) =
      ∑ u, ν (affinePalettePiece b B L s e E u) := by
    simpa only [tsum_fintype] using measure_iUnion
      (pairwiseDisjoint_affinePalettePiece b B L s e E)
      (measurableSet_affinePalettePiece b hb B hB L hse)
  rw [← heq]
  exact measure_mono (by
    intro l hl
    obtain ⟨u, hu⟩ := mem_iUnion.mp hl
    exact (affinePalettePiece_subset b B L s e E u hu).1)

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
