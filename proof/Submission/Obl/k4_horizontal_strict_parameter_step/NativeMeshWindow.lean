/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMeshWindow.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.JitterGeometry
import Submission.Lib.K4ContinuousPlanks.Discretization

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4AffineMeshCaps

/-- The original coefficient and unit-time bounds control the physical base,
independently of the number of old or true assignments. -/
theorem physicalBase_bounded {b : Fin 6 → ℝ} {t K : ℝ} (hK : 1 ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : ∀ e, |b e| ≤ 2 * K) :
    ∀ e, |physicalBase b t e| ≤ 4 * K := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hcoord (i j : Fin 6) : |b i + t * b j| ≤ 4 * K := by
    calc
      _ ≤ |b i| + |t * b j| := abs_add_le _ _
      _ ≤ 2 * K + 1 * (2 * K) := by
        rw [abs_mul]
        exact add_le_add (hb i) (mul_le_mul ht1 (hb j) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  intro e
  fin_cases e
  · exact ht1.trans (by linarith)
  · exact hcoord 0 3
  · exact hcoord 1 4

/-- A single finite physical mesh window contains every original support point.
Its cardinality is used only for finiteness and never enters the matching cost. -/
theorem exists_physical_mesh_window {α : Type*} (b : α → Fin 6 → ℝ)
    (G : Set (α × ℝ)) {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ G, ∀ e, |b p.1 e| ≤ 2 * K) :
    ∃ F : Finset (Fin 3 → ℤ), ∀ p ∈ G, baseMesh δ (physicalBase (b p.1) p.2) ∈ F := by
  classical
  have hfinite := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun p : G => physicalBase (b p.val.1) p.val.2) (4 * K)
    (fun p e => physicalBase_bounded hK (htime p p.property) (hcoeff p p.property) e) hδ
  refine ⟨hfinite.toFinset, fun p hp => hfinite.mem_toFinset.mpr ?_⟩
  exact ⟨⟨p, hp⟩, rfl⟩

end Submission.Obl.k4_horizontal_strict_parameter_step
