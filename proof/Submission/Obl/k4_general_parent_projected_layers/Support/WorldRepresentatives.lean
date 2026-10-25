/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/WorldRepresentatives.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedWorlds
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap
import Submission.Lib.K4QuadraticSheets.JetBins
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Bounded representatives in the original, unchanged coefficient bins. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

local instance worldRepresentativesPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def boundedBinRepresentative (K delta : ℝ) (j : ℤ) : ℝ :=
  if h : ∃ x : ℝ, |x| ≤ K ∧ ⌊x / delta⌋ = j then Classical.choose h else 0

theorem boundedBinRepresentative_bound {K delta : ℝ} (hK : 0 ≤ K) (j : ℤ) :
    |boundedBinRepresentative K delta j| ≤ K := by
  classical
  unfold boundedBinRepresentative
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simpa only [abs_zero] using hK

theorem boundedBinRepresentative_gap {K delta x : ℝ} (hd : 0 < delta)
    (hx : |x| ≤ K) {j : ℤ} (hj : ⌊x / delta⌋ = j) :
    |x - boundedBinRepresentative K delta j| ≤ delta := by
  classical
  have h : ∃ y : ℝ, |y| ≤ K ∧ ⌊y / delta⌋ = j := ⟨x, hx, hj⟩
  rw [boundedBinRepresentative, dif_pos h]
  exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hd
    (hj.trans (Classical.choose_spec h).2.symm)).le

def projectedWorldRepresentatives (K chi g : ℝ) (q : Fin 4 → ℤ) : Fin 4 → ℝ :=
  ![boundedBinRepresentative K chi (q 0), boundedBinRepresentative K chi (q 1),
    boundedBinRepresentative K g (q 2), boundedBinRepresentative K g (q 3)]

theorem projectedWorldRepresentatives_bound {K chi g : ℝ} (hK : 0 ≤ K)
    (q : Fin 4 → ℤ) (i : Fin 4) : |projectedWorldRepresentatives K chi g q i| ≤ K := by
  fin_cases i <;> exact boundedBinRepresentative_bound hK _

theorem projectedWorldRepresentatives_gap {K chi g : ℝ} (hc : 0 < chi) (hg : 0 < g)
    (b : Fin 6 → ℝ) (hb : |b 0| + |b 1| + |b 3| + |b 4| ≤ K)
    {q : Fin 4 → ℤ} (hq : projectedWorldTag chi g b = q) :
    b ∈ majorGroup chi (projectedWorldRepresentatives K chi g q 1)
        (projectedWorldRepresentatives K chi g q 0) ∧
      |b 1 - projectedWorldRepresentatives K chi g q 2| ≤ g ∧
      |b 4 - projectedWorldRepresentatives K chi g q 3| ≤ g := by
  have h0 : |b 0| ≤ K := by linarith [abs_nonneg (b 1), abs_nonneg (b 3), abs_nonneg (b 4)]
  have h1 : |b 1| ≤ K := by linarith [abs_nonneg (b 0), abs_nonneg (b 3), abs_nonneg (b 4)]
  have h3 : |b 3| ≤ K := by linarith [abs_nonneg (b 0), abs_nonneg (b 1), abs_nonneg (b 4)]
  have h4 : |b 4| ≤ K := by linarith [abs_nonneg (b 0), abs_nonneg (b 1), abs_nonneg (b 3)]
  have hq0 : ⌊b 3 / chi⌋ = q 0 := by simpa [projectedWorldTag] using congrFun hq 0
  have hq1 : ⌊b 0 / chi⌋ = q 1 := by simpa [projectedWorldTag] using congrFun hq 1
  have hq2 : ⌊b 1 / g⌋ = q 2 := by simpa [projectedWorldTag] using congrFun hq 2
  have hq3 : ⌊b 4 / g⌋ = q 3 := by simpa [projectedWorldTag] using congrFun hq 3
  exact ⟨⟨boundedBinRepresentative_gap hc h0 hq1,
    boundedBinRepresentative_gap hc h3 hq0⟩,
    boundedBinRepresentative_gap hg h1 hq2, boundedBinRepresentative_gap hg h4 hq3⟩

end

end Submission.Obl.k4_general_parent_projected_layers
