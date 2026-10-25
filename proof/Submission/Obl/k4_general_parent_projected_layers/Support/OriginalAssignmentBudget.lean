/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/OriginalAssignmentBudget.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_horizon_chart_assembly.Aggregation
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! The original full-assignment budgets used in projected support counting. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem original_assignment_budget (p : Parameters) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) :
    ∑ i : Fin (a.n k s), a.q k s * (a.nu k (a.A k s i)).toReal ≤ 1 := by
  haveI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hmeas (i : Fin (a.n k s)) : MeasurableSet (a.A k s i) := hatlas.2.2.1 i |>.1
  have hdisj := hatlas.2.2.2.1
  have hbudget : ∑ i : Fin (a.n k s), (a.nu k (a.A k s i)).toReal ≤
      (2 : ℝ) ^ a.T k s := by
    simpa [measureReal_def] using Submission.Obl.k4_horizon_chart_assembly.sum_original_group_budget
      (Γ := Unit) (fun _ => a.nu k) (fun _ => ()) (a.j k s) (a.A k s)
      hmeas (fun i i' hne hgamma hj => hdisj i i' hne hj)
  rw [← Finset.mul_sum]
  calc
    _ ≤ a.q k s * (2 : ℝ) ^ a.T k s :=
      mul_le_mul_of_nonneg_left hbudget (by unfold q; positivity)
    _ = 1 := by simp [q]

/-- Counting terminal support charges each label by its full original prior,
including its own time length. -/
theorem original_label_volume_budget (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) :
    (a.n k s : ℝ) * (a.q k s ^ 3 * narrow p k s) ≤
      p.K k / (width p k s) ^ p.d := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  haveI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hq : 0 ≤ a.q k s := by unfold q; positivity
  have ha : 0 < (width p k s) ^ p.d := by
    exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  let floor : ℝ := (width p k s) ^ p.d * a.q k s ^ 2 * narrow p k s / p.K k
  have hfloor0 : 0 ≤ floor := by dsimp [floor]; positivity
  have hfloor (i : Fin (a.n k s)) : floor ≤ (a.nu k (a.A k s i)).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top (a.nu k) (a.A k s i))
      ((hatlas.2.2.2.2.1 i).1)
    change (ENNReal.ofReal floor).toReal ≤ _ at h
    rw [ENNReal.toReal_ofReal hfloor0] at h
    exact h
  have hmass : (a.n k s : ℝ) * (a.q k s * floor) ≤ 1 := by
    calc
      _ = ∑ _i : Fin (a.n k s), a.q k s * floor := by simp
      _ ≤ ∑ i : Fin (a.n k s), a.q k s * (a.nu k (a.A k s i)).toReal :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hfloor i) hq)
      _ ≤ 1 := a.original_assignment_budget p hcommon hatlas
  apply (le_div_iff₀ ha).mpr
  calc
    _ = p.K k * ((a.n k s : ℝ) * (a.q k s * floor)) := by dsimp [floor]; field_simp
    _ ≤ p.K k * 1 := mul_le_mul_of_nonneg_left hmass hK.le
    _ = p.K k := mul_one _

end PreparedModel

end Submission.Obl.k4_general_parent_projected_layers
