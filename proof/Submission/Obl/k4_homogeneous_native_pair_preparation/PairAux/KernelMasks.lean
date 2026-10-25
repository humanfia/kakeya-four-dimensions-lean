-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepCoverageMasks.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelDerivative

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set
namespace Data

def coverageEndpointBad (D : Data) (b : Fin D.C) : Set PairPoint :=
  D.coverageRawPairs b ∩ {p | p.2.2 =
    ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)}

variable {D : Data} {E : Fin D.W → Set Incidence}

theorem coverageEndpointBad_null (D : Data) (ν : Measure Trajectory) (b : Fin D.C) :
    (ν.prod (volume.prod volume)) (D.coverageEndpointBad b) = 0 := by
  apply measure_mono_null inter_subset_right
  have heq (t : ℝ) : {p : PairPoint | p.2.2 = t} = univ ×ˢ (univ ×ˢ ({t} : Set ℝ)) := by
    ext p
    simp
  rw [heq, Measure.prod_prod, Measure.prod_prod, Real.volume_singleton, mul_zero, mul_zero]

theorem Hyp.coverage_witness_coarse (h : D.Hyp E)
    (b b' : Fin D.C) {p : Incidence} (hp : p ∈ D.Sb b')
    (ht : p.2 ∈ D.blk (coarseIdx (D.j b)))
    (hlt : p.2 < ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)) :
    coarseIdx (D.j b') = coarseIdx (D.j b) := by
  have h1 := h.coverage_Sb_coarse b' hp
  have h2 : p.2 ∈ Ico (((coarseIdx (D.j b) : ℕ) : ℝ) / (2 : ℝ) ^ D.T)
      ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T) := ⟨ht.1, hlt⟩
  have h1' : p.2 ∈ Submission.Obl.k4_scalar_pair_atlas_assembly.halfI D.T
      (coarseIdx (D.j b')) := by
    simpa only [Submission.Obl.k4_scalar_pair_atlas_assembly.halfI,
      Submission.Obl.k4_scalar_pair_atlas_assembly.width, div_eq_mul_inv] using h1
  have h2' : p.2 ∈ Submission.Obl.k4_scalar_pair_atlas_assembly.halfI D.T
      (coarseIdx (D.j b)) := by
    simpa only [Submission.Obl.k4_scalar_pair_atlas_assembly.halfI,
      Submission.Obl.k4_scalar_pair_atlas_assembly.width, div_eq_mul_inv] using h2
  by_contra hne
  exact disjoint_left.mp (Submission.Obl.k4_scalar_pair_atlas_assembly.halfI_disjoint D.T hne)
    h1' h2'

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
