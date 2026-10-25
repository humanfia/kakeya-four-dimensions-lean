/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 89648dfeac59b903d3d93ae0dca8d07a6202ebdf, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeSelectedRows.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonContext
import Submission.Obl.k4_horizontal_strict_parameter_step.NormalizedResidual
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.BlockRow

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

def nativePhysical (h : Fin c.m) (i : Fin (cfg.n k s)) : Fin 6 → ℝ :=
  affinePredictor (c.L i) (cfg.N k ^ (-cfg.e₀) * (c.group h 0 : ℝ))

def selectedRow (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (h : Fin c.m) (j : Fin (2 ^ cfg.T k s)) (t : ℝ) : Fin 2 → ℝ :=
  match choice h j with
  | none => 0
  | some i => normalizedRow (c.nativePhysical h i) (c.hH h) c.D c.a t

def selectedF (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (h : Fin c.m) : ℝ → Fin 2 → ℝ := closedBlockRow (c.selectedRow choice h)

theorem measurable_selectedRow
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (h : Fin c.m) (j : Fin (2 ^ cfg.T k s)) : Measurable (c.selectedRow choice h j) := by
  change Measurable (fun t => c.selectedRow choice h j t)
  cases hj : choice h j with
  | none => simpa only [selectedRow, hj] using (measurable_const : Measurable (fun _ : ℝ => (0 : Fin 2 → ℝ)))
  | some i =>
    simp only [selectedRow, hj]
    unfold normalizedRow
    fun_prop

theorem measurable_selectedF
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (h : Fin c.m) : Measurable (c.selectedF choice h) :=
  measurable_closedBlockRow _ (c.measurable_selectedRow choice h)

/-- On the stored pointwise unique coarse support, the assembled row equals
exactly the selected native row, including every retained boundary point. -/
theorem selectedF_eq
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (p : α × ℝ) (hp : p ∈ c.support.event) (h : Fin c.m) (i : Fin (cfg.n k s))
    (ht : p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i))
    (hchoice : choice h (cfg.j k s i) = some i) :
    c.selectedF choice h p.2 = normalizedRow (c.nativePhysical h i) (c.hH h) c.D c.a p.2 := by
  have hrow := closedBlockRow_eq (c.selectedRow choice h) p.2 (cfg.j k s i)
    (by simpa only [Data.I, Nat.cast_pow, Nat.cast_ofNat] using ht)
    (by
      intro j hj
      apply c.support.unique_block p hp j (cfg.j k s i) ?_ ht
      simpa only [Data.I, Nat.cast_pow, Nat.cast_ofNat] using hj)
  change closedBlockRow (c.selectedRow choice h) p.2 = _
  rw [hrow]
  simp only [selectedRow, hchoice]

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
