import Submission.Obl.k4_matched_pair_representative_realization.Kernel

/- Adapted within this LOT tree from o190/x0630, adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/Kernel.lean. The parent kernel definitions are imported. -/

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

/-- One large-resolution instance of the supplied sublevel estimate. -/
def SublevelAt (Cs : ℕ) (CD N a : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin 3) ℝ) (α : EuclideanSpace ℝ (Fin 3)),
    P.totalDegree ≤ 2 → (∀ d, |P.coeff d| ≤ N ^ a) → ‖α‖ ≤ 1 / 8 →
    (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) P| →
    MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ 1 / 8 ∧
      |MvPolynomial.eval (fun i => z i) P| < N ^ (-(CD * a))} ≤
        ENNReal.ofReal (N ^ (-(3 * a)))


end Submission.Obl.k4_matched_pair_representative_realization.Selection
