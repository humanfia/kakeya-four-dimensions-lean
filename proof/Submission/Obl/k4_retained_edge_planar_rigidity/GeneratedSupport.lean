import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.FlatCoeff
import Submission.Obl.k4_retained_edge_planar_rigidity.ScalarGrowth

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

/-- The coefficient tuples used by the flat law have precisely the support bound needed by the
collision argument, uniformly over tuples including those of zero probability. -/
theorem generated_support_bound
    {ι : Type*} [Fintype ι] {h K L R : ℝ} {a : ℕ}
    {E F : Finset (ℝ × ℝ)} {ℛ : Finset ℝ}
    (D : ClosureData h K L a E F ℛ) (t : ι → ℝ) (ht : ∀ j, t j ∈ ℛ)
    (hR : 1 ≤ R) (m k n : ℕ) (γ : Fin m × Bool → Fin k → Fin n → ι) :
    ((cells h (∑ i, ((genVal t R n k (γ (i, true))) • E +
      (genVal t R n k (γ (i, false))) • F))).card : ℝ) ≤
        ClosureData.closureConst K a m k n * L := by
  exact D.generated_card_le m k n hR
    (fun i l j => t (γ (i, true) l j)) (fun i l j => t (γ (i, false) l j))
    (fun _ _ _ => ht _) (fun _ _ _ => ht _)

end Submission.Obl.k4_retained_edge_planar_rigidity
