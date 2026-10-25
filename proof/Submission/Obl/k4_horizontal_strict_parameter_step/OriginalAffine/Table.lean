import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeGeometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

/-- The affine table is certified on each full original fitted assignment. -/
structure NativeAffineTable {α : Type} [MeasurableSpace α]
    (cfg : NativeModel α) (k : ℕ) (s : ℝ) where
  entry : Fin (cfg.n k s) → Fin 4 → ℝ
  slopes : ∀ i (e : Fin 3), |entry i e.succ| ≤ 8 * cfg.K k ^ 4
  fit : ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
    |cfg.b k l 2 + t * cfg.b k l 5 -
      (entry i 0 + entry i 1 * t + entry i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
        entry i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s)

namespace NativeAffineTable

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α} {k : ℕ} {s : ℝ}

theorem original_fit (L : NativeAffineTable cfg k s) (i : Fin (cfg.n k s))
    (l : α) (hl : l ∈ cfg.B k s i) (t : ℝ)
    (ht : t ∈ Data.I (cfg.T k s) (cfg.j k s i)) :
    |(cfg.x k l t) 3 - (L.entry i 0 + ∑ e : Fin 3,
      L.entry i e.succ * cfg.originalBasePoint k (l, t) e)| ≤
        cfg.K k * cfg.N k ^ (-s) := by
  simpa [NativeModel.originalBasePoint, Data.x, Fin.sum_univ_succ, add_assoc]
    using L.fit i l hl t ht

end NativeAffineTable

namespace NativeModel

theorem exists_affine_table {α : Type} [MeasurableSpace α] (cfg : NativeModel α)
    {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k) (hκ : 0 ≤ cfg.κ)
    (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s) :
    Nonempty (NativeAffineTable cfg k s) := by
  obtain ⟨L, hL, hfit⟩ := cfg.affine_table a hN hK hκ hκ1 hs
  exact ⟨⟨L, hL, hfit⟩⟩

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
