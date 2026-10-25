/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeGeometry.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWitnesses

/-! Original true-box geometry, adapted from this LOT tree o202, session x0698,
commit af82e6f9c71df56ed963f4a992dea84d0d6d83b5,
Submission/Obl/k4_horizontal_subcritical_rate_candidates/G1/TrueNativeCaps.lean.
Only the assignment-level hypotheses are retained; no critical Valid is assumed. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

noncomputable def originalBasePoint (k : ℕ) (p : α × ℝ) : Fin 3 → ℝ :=
  ![p.2, (cfg.x k p.1 p.2) 1, (cfg.x k p.1 p.2) 2]

noncomputable def originalTimeCenter (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * cfg.timeLength k s

noncomputable def originalTrueBox (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set (Fin 3 → ℝ) :=
  {v | |v 0 - cfg.originalTimeCenter k s i| ≤ cfg.timeLength k s / 2 ∧
    |v 1 - cfg.c k s i 0 - v 0 * cfg.c k s i 1| ≤ cfg.K k * cfg.timeLength k s ∧
    |v 2 - cfg.c k s i 2 - v 0 * cfg.c k s i 3 - cfg.c k s i 4 * v 1| ≤
      cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s)}

/-- The whole original fitted witness lies in its unchanged true box. -/
theorem original_witness_mem_trueBox {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (i : Fin (cfg.n k s)) (p : α × ℝ)
    (hp : p ∈ cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)) :
    cfg.originalBasePoint k p ∈ cfg.originalTrueBox k s i := by
  have ht := hp.2
  change (cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s ≤ p.2 ∧
    p.2 ≤ ((cfg.j k s i : ℕ) + (1 : ℝ)) / (2 : ℝ) ^ cfg.T k s at ht
  simp only [div_eq_mul_inv] at ht
  change (cfg.j k s i : ℕ) * cfg.timeLength k s ≤ p.2 ∧
    p.2 ≤ ((cfg.j k s i : ℕ) + (1 : ℝ)) * cfg.timeLength k s at ht
  have hg := a.geometry i p.1 (a.fitted_subset i hp.1) p.2 hp.2
  refine ⟨?_, hg.1, hg.2.1⟩
  change |p.2 - (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s| ≤
    cfg.timeLength k s / 2
  rw [abs_le]
  constructor <;> nlinarith [ht.1, ht.2]

/-- Recenter the genuine true box without changing its transverse side. -/
theorem original_trueBox_centered {k : ℕ} {s : ℝ} (i : Fin (cfg.n k s))
    (v : Fin 3 → ℝ) (hv : v ∈ cfg.originalTrueBox k s i) :
    let t₀ := cfg.originalTimeCenter k s i
    let z₀ := cfg.c k s i 0 + t₀ * cfg.c k s i 1
    let y₀ := cfg.c k s i 2 + t₀ * cfg.c k s i 3 + cfg.c k s i 4 * z₀
    |v 0 - t₀| ≤ cfg.timeLength k s / 2 ∧
    |v 1 - z₀ - cfg.c k s i 1 * (v 0 - t₀)| ≤ cfg.K k * cfg.timeLength k s ∧
    |v 2 - y₀ - cfg.c k s i 3 * (v 0 - t₀) - cfg.c k s i 4 * (v 1 - z₀)| ≤
      cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) := by
  refine ⟨hv.1, ?_, ?_⟩
  · convert hv.2.1 using 1
    congr 1
    ring
  · convert hv.2.2 using 1
    congr 1
    ring

/-- Every point of the whole true box remains in the original unit time interval. -/
theorem original_trueBox_time_unit {k : ℕ} {s : ℝ} (i : Fin (cfg.n k s))
    (v : Fin 3 → ℝ) (hv : v ∈ cfg.originalTrueBox k s i) : v 0 ∈ Icc (0 : ℝ) 1 := by
  have ht := abs_le.mp hv.1
  have hvI : v 0 ∈ Data.I (cfg.T k s) (cfg.j k s i) := by
    simp only [Data.I, mem_Icc, div_eq_mul_inv]
    change ((cfg.j k s i : ℕ) : ℝ) * cfg.timeLength k s ≤ v 0 ∧
      v 0 ≤ (((cfg.j k s i : ℕ) : ℝ) + 1) * cfg.timeLength k s
    dsimp [originalTimeCenter] at ht
    constructor <;> nlinarith [ht.1, ht.2]
  exact Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) hvI

/-- The original pure cap factors as hidden-scale mass times base-cell volume. -/
theorem original_hidden_cell_cap {k : ℕ} {r s : ℝ} (hN : 0 < cfg.N k)
    (hcap : ∀ (p : Fin 3 → ℤ) (j : ℤ),
      cfg.μ k {ω | cfg.z k (cfg.N k) r ω = p ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / (cfg.N k ^ (-s))⌋ = j} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s)))
    (p : Fin 3 → ℤ) (j : ℤ) :
    cfg.μ k {ω | (fun e => ⌊cfg.originalBasePoint k ω e / cfg.N k ^ (-r)⌋) = p ∧
      ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d * (cfg.N k ^ (-r)) ^ 3) := by
  have heq : cfg.N k ^ (-3 * r - cfg.d * s) =
      (cfg.N k ^ (-s)) ^ cfg.d * (cfg.N k ^ (-r)) ^ 3 := by
    rw [← Real.rpow_mul hN.le, ← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  convert hcap p j using 1
  · rfl
  · rw [heq]
    congr 1
    ring

/-- Whole original child witnesses in one dyadic time block are disjoint,
including after intersecting them with a fixed ancestor fit set. -/
theorem original_witness_family_disjoint {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (S : Finset (Fin (cfg.n k s))) (P : Set α)
    (hblock : ∀ i ∈ S, ∀ j ∈ S, cfg.j k s i = cfg.j k s j) :
    (S : Set (Fin (cfg.n k s))).PairwiseDisjoint
      (fun i => (cfg.B k s i ∩ P) ×ˢ Data.I (cfg.T k s) (cfg.j k s i)) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  rintro p ⟨hpi, hpt⟩ ⟨hpj, hpt'⟩
  exact Set.disjoint_left.mp (a.disjoint i j hne (hblock i hi j hj))
    (a.fitted_subset i hpi.1) (a.fitted_subset j hpj.1)

end NativeModel
end Submission.Obl.k4_horizontal_strict_parameter_step
