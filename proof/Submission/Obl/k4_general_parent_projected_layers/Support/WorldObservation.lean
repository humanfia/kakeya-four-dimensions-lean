/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/WorldObservation.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.NativeScalar
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldRepresentatives
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Scalar observables agree exactly with the unchanged native signal in each world. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set MvPolynomial
open Submission.Obl.k4_uncapped_native_capping (scalarX scalarY)

noncomputable section

def worldScalarCoefficients {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (b : α → Fin 6 → ℝ) (K chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) : α → Fin 5 → ℝ :=
  nativeScalarCoefficients P b g (projectedWorldRepresentatives K chi g u 2)
    (projectedWorldRepresentatives K chi g u 3) (projectedWorldCrop C b chi g u)

theorem world_scalar_observation {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : α → Fin 6 → ℝ) {K chi g : ℝ}
    (hc : 0 < chi) (hg : 0 < g) (C : Set α)
    (hbound : ∀ l ∈ C, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (u : Fin 4 → ℤ) {l : α} (hl : l ∈ projectedWorldCrop C b chi g u) (sigma t : ℝ) :
    b l ∈ majorGroup chi (projectedWorldRepresentatives K chi g u 1)
        (projectedWorldRepresentatives K chi g u 0) ∧
      ⌊b l 3 / chi⌋ = u 0 ∧
      (![⌊t / sigma⌋, ⌊scalarY (worldScalarCoefficients P b K chi g C u l) t / sigma⌋] : Fin 2 → ℤ) =
        projectedCell sigma g (projectedWorldRepresentatives K chi g u 2)
          (projectedWorldRepresentatives K chi g u 3) (b l) t ∧
      scalarX (worldScalarCoefficients P b K chi g C u l) t = eval (trajectory (b l) t) P := by
  have hrep := projectedWorldRepresentatives_gap hc hg (b l) (hbound l hl.1) hl.2
  refine ⟨hrep.1, ?_, ?_, ?_⟩
  · simpa [projectedWorldTag] using congrFun hl.2 0
  · unfold worldScalarCoefficients
    rw [nativeScalarCoefficients_y P b g _ _ hl]
    rfl
  · exact nativeScalarCoefficients_x P hP b g _ _ hl t

end

end Submission.Obl.k4_general_parent_projected_layers
