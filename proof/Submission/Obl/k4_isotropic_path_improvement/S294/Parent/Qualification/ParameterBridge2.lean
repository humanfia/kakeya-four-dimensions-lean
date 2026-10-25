-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterBridge2, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterBridge2.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterBridge2.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterBridge2.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4c91e1da. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2Lower
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterPalette2

/-!
# From the floors of `parameter_floor_cleanup` to the floors of the palette

`parameter_floor_cleanup` bounds below the prior mass of the scalar-coefficient block inside the
affine-bin world of a line; for lines of `S` (coefficients bounded by `K`, so that clipping does
nothing) this is exactly the full seven-coefficient block `blockPrior` used by
`surviving_block_count` and `derivative_list_of_floors`.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory Set
open Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

theorem scalar_code_eq {K p : ℝ} {c : Fin 7 → ℝ} (hc : |c 0| ≤ K ∧ |c 1| ≤ K ∧ |c 2| ≤ K) :
    coefficientCode p (scalarCoeffPoint K c) = fun j : Fin 3 => ⌊![c 0, c 1, c 2] j / p⌋ := by
  funext j
  simp only [coefficientCode, scalarCoeffPoint_apply]
  fin_cases j
  · simp [clip_eq hc.1]
  · simp [clip_eq hc.2.1]
  · simp [clip_eq hc.2.2]

/-- For lines of `S`, the scalar block inside the affine-bin world is the seven-coefficient
block. -/
theorem world_block_eq {Λ : Type*} {S : Set Λ} {cf : Λ → Fin 7 → ℝ} {K p : ℝ}
    (hcoeff : ∀ l ∈ S, |cf l 0| ≤ K ∧ |cf l 1| ≤ K ∧ |cf l 2| ≤ K) {l : Λ} (hl : l ∈ S) :
    {l' | coefficientCode p (scalarCoeffPoint K (cf l')) =
        coefficientCode p (scalarCoeffPoint K (cf l))} ∩
      affineWorld S cf p (ybin p (cf l)) (vbin p (cf l)) =
      {l' | l' ∈ S ∧ blockCode p (cf l') = blockCode p (cf l)} := by
  ext l'
  simp only [mem_inter_iff, mem_ofPred_eq, affineWorld]
  constructor
  · rintro ⟨hcode, hl'S, hy, hv⟩
    refine ⟨hl'S, ?_⟩
    rw [scalar_code_eq (hcoeff l' hl'S), scalar_code_eq (hcoeff l hl)] at hcode
    funext i
    simp only [blockCode]
    fin_cases i
    · simpa using congrFun hcode 0
    · simpa using congrFun hcode 1
    · simpa using congrFun hcode 2
    · simpa [ybin] using congrFun hy 0
    · simpa [vbin] using congrFun hv 0
    · simpa [ybin] using congrFun hy 1
    · simpa [vbin] using congrFun hv 1
  · rintro ⟨hl'S, hblock⟩
    refine ⟨?_, hl'S, ?_, ?_⟩
    · rw [scalar_code_eq (hcoeff l' hl'S), scalar_code_eq (hcoeff l hl)]
      funext j
      fin_cases j
      · simpa [blockCode] using congrFun hblock 0
      · simpa [blockCode] using congrFun hblock 1
      · simpa [blockCode] using congrFun hblock 2
    · funext i
      fin_cases i
      · simpa [ybin, blockCode] using congrFun hblock 3
      · simpa [ybin, blockCode] using congrFun hblock 5
    · funext i
      fin_cases i
      · simpa [vbin, blockCode] using congrFun hblock 4
      · simpa [vbin, blockCode] using congrFun hblock 6

/-- The floors of `parameter_floor_cleanup`, in the form of the palette's `hfloor`. -/
theorem blockPrior_floor_of_world {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}
    {S : Set Λ} {cf : Λ → Fin 7 → ℝ} {K p f : ℝ} {π : (Fin 2 → ℤ) → ENNReal}
    (hcoeff : ∀ l ∈ S, |cf l 0| ≤ K ∧ |cf l 1| ≤ K ∧ |cf l 2| ≤ K) {l : Λ} (hl : l ∈ S)
    (hfl : π (vbin p (cf l)) * ENNReal.ofReal f ≤
      ν ({l' | coefficientCode p (scalarCoeffPoint K (cf l')) =
          coefficientCode p (scalarCoeffPoint K (cf l))} ∩
        affineWorld S cf p (ybin p (cf l)) (vbin p (cf l)))) :
    ENNReal.ofReal f * π (blockVbin (blockCode p (cf l))) ≤
      blockPrior ν cf S p (blockCode p (cf l)) := by
  rw [world_block_eq hcoeff hl] at hfl
  rw [← vbin_eq_blockVbin, mul_comm]
  exact hfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
