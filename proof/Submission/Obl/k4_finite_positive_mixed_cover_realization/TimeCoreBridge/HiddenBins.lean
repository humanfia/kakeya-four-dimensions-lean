-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/HiddenBins.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b,
-- Submission/Obl/k4_greedy_cover_graph_atlas/HiddenBins.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/HiddenBins.lean.

import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- Closed hidden bins meeting the regular sublevel set of a univariate quadratic.
Closed bins make the base support measurable and cost at most a factor of two. -/
def regularClosedBins (q : Polynomial ℝ) (ε β δ : ℝ) : Set ℤ :=
  {b | ∃ w ∈ Icc (δ * (b : ℝ)) (δ * ((b : ℝ) + 1)),
    |q.eval w| ≤ ε ∧ β ≤ |q.derivative.eval w|}

/-- The regular quadratic fiber meets only a bounded number of closed hidden bins. -/
theorem regularClosedBins_finite_card (q : Polynomial ℝ) (hq : q.natDegree ≤ 2)
    {ε β δ : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hδ : 0 < δ) :
    (regularClosedBins q ε β δ).Finite ∧
      ((regularClosedBins q ε β δ).ncard : ℝ) ≤ 16 * (1 + ε / (β * δ)) := by
  let S : Set ℤ := (fun w : ℝ => ⌊w / δ⌋) ''
    {w : ℝ | |q.eval w| ≤ ε ∧ β ≤ |q.derivative.eval w|}
  have hS : S.Finite ∧ (S.ncard : ℝ) ≤ 8 * (1 + ε / (β * δ)) := by
    simpa only [sub_zero] using
      Submission.Lib.K4QuadraticSublevel.grid_bins_quadratic_sublevel q hq hε hβ hδ 0
  have hsub : regularClosedBins q ε β δ ⊆ S ∪ (fun b : ℤ => b - 1) '' S := by
    rintro b ⟨w, hw, hreg⟩
    have hlow : b ≤ ⌊w / δ⌋ := Int.le_floor.mpr ((le_div_iff₀ hδ).mpr (by nlinarith [hw.1]))
    have hhi : ⌊w / δ⌋ ≤ b + 1 := by
      have hh : w / δ ≤ (b : ℝ) + 1 := (div_le_iff₀ hδ).mpr (by nlinarith [hw.2])
      simpa using Int.floor_mono hh
    have hmem : ⌊w / δ⌋ ∈ S := ⟨w, hreg, rfl⟩
    rcases (show ⌊w / δ⌋ = b ∨ ⌊w / δ⌋ = b + 1 by omega) with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr ⟨⌊w / δ⌋, hmem, by dsimp; omega⟩
  have hfin := hS.1.union (hS.1.image (fun b : ℤ => b - 1))
  refine ⟨hfin.subset hsub, ?_⟩
  have hc₁ := ncard_le_ncard hsub hfin
  have hc₂ := ncard_union_le S ((fun b : ℤ => b - 1) '' S)
  have hc₃ := ncard_image_le (f := fun b : ℤ => b - 1) hS.1
  have hc : (regularClosedBins q ε β δ).ncard ≤ 2 * S.ncard := by omega
  have hc' : ((regularClosedBins q ε β δ).ncard : ℝ) ≤ 2 * (S.ncard : ℝ) := by
    exact_mod_cast hc
  nlinarith [hS.2]

section Measurability

variable {X : Type*} [TopologicalSpace X]

/-- The observable base and hidden-bin support, with a closed-bin witness. -/
def closedBinSupport (value slope : X → ℝ → ℝ) (ε β δ : ℝ) : Set (X × ℤ) :=
  {p | ∃ w ∈ Icc (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1)),
    |value p.1 w| ≤ ε ∧ β ≤ |slope p.1 w|}

/-- Projection over the compact closed bin gives a closed set in the exact base. -/
theorem isClosed_closedBinSupport_section {value slope : X → ℝ → ℝ}
    (hv : Continuous (Function.uncurry value)) (hs : Continuous (Function.uncurry slope))
    (ε β δ : ℝ) (b : ℤ) :
    IsClosed {u : X | (u, b) ∈ closedBinSupport value slope ε β δ} := by
  let I : Set ℝ := Icc (δ * (b : ℝ)) (δ * ((b : ℝ) + 1))
  have : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let C : Set (X × I) := {p | |value p.1 p.2.val| ≤ ε ∧ β ≤ |slope p.1 p.2.val|}
  have hproj : Continuous (fun p : X × I => (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hC : IsClosed C :=
    (isClosed_le (hv.comp hproj).abs continuous_const).inter
      (isClosed_le continuous_const (hs.comp hproj).abs)
  convert isClosedMap_fst_of_compactSpace C hC using 1
  ext u
  simp only [closedBinSupport, mem_ofPred_eq, mem_image, Prod.exists, exists_prop,
    C, I, Subtype.exists, mem_Icc]
  aesop

theorem measurableSet_closedBinSupport [MeasurableSpace X] [BorelSpace X]
    {value slope : X → ℝ → ℝ}
    (hv : Continuous (Function.uncurry value)) (hs : Continuous (Function.uncurry slope))
    (ε β δ : ℝ) : MeasurableSet (closedBinSupport value slope ε β δ) := by
  have hU : MeasurableSet (⋃ b : ℤ,
      {u : X | (u, b) ∈ closedBinSupport value slope ε β δ} ×ˢ ({b} : Set ℤ)) :=
    MeasurableSet.iUnion fun b =>
      (isClosed_closedBinSupport_section hv hs ε β δ b).measurableSet.prod
        (measurableSet_singleton b)
  convert hU using 1
  ext p
  simp only [mem_iUnion, mem_prod, mem_singleton_iff, mem_ofPred_eq]
  aesop

end Measurability

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
