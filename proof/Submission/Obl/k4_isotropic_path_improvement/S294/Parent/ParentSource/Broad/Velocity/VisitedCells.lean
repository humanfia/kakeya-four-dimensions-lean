-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.VisitedCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/VisitedCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/VisitedCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.NativeCurveCells
import Submission.Lib.K4ListedExceptions.FrameCodes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Set
open SourceGeometry
open Submission.Lib.K4ListedExceptions

noncomputable section

/-- A bounded coordinate range supplies a finite table containing exactly
the cells actually visited on the unit time interval. -/
theorem exists_curve_cell_table {n : ℕ} (F : ℝ → Fin n → ℝ) {q R : ℝ}
    (hq : 0 < q) (hR : 0 ≤ R)
    (hspan : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, |F t j - F 0 j| ≤ R) :
    ∃ S : Finset (Fin n → ℤ), ∀ c,
      c ∈ S ↔ ∃ t ∈ Icc (0 : ℝ) 1, (fun j => (⌊F t j / q⌋ : ℤ)) = c := by
  classical
  let C := ⌈R / q⌉₊
  let box := integerCodeBox C (fun j => ⌊F 0 j / q⌋)
  let S := box.filter (fun c => ∃ t ∈ Icc (0 : ℝ) 1,
    (fun j => (⌊F t j / q⌋ : ℤ)) = c)
  refine ⟨S, fun c => ⟨fun hc => (Finset.mem_filter.mp hc).2, ?_⟩⟩
  rintro ⟨t, ht, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, t, ht, rfl⟩
  apply floor_code_mem_integerCodeBox C (F t) (F 0) (fun _ => q) (fun _ => hq)
  intro j
  exact (hspan t ht j).trans ((div_le_iff₀ hq).mp (Nat.le_ceil (R / q)))

/-- Actual native quadratic trajectories have only order `1 / q` visited
coarse cells, with a polynomial cost in their whole-time bound. -/
theorem exists_native_curve_cell_menu (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (p v : Fin 4 → ℝ) {K q : ℝ}
    (hK : 0 ≤ K) (hq : 0 < q)
    (hv : ∀ j : Fin 3, |v j.castSucc| ≤ K)
    (hwhole : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (fun j => p j + t * v j) P| ≤ K) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) ≤ (2 / q + 3) * (114 * K + 5) ^ 4 ∧
      ∀ c, c ∈ S ↔ ∃ t ∈ Icc (0 : ℝ) 1,
        (fun j => (⌊nativePhysicalCurve P p v t j / q⌋ : ℤ)) = c := by
  classical
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hbase (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin 3) :
      |(p j.castSucc + t * v j.castSucc) - (p j.castSucc + 0 * v j.castSucc)| ≤ 2 * K := by
    rw [show (p j.castSucc + t * v j.castSucc) - (p j.castSucc + 0 * v j.castSucc) =
      t * v j.castSucc by ring, abs_mul, abs_of_nonneg ht.1]
    calc
      _ ≤ t * K := mul_le_mul_of_nonneg_left (hv j) ht.1
      _ ≤ 1 * K := mul_le_mul_of_nonneg_right ht.2 hK
      _ ≤ 2 * K := by nlinarith
  have hspan : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j,
      |nativePhysicalCurve P p v t j - nativePhysicalCurve P p v 0 j| ≤ 2 * K := by
    intro t ht j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · change |MvPolynomial.eval (fun j => p j + t * v j) P -
          MvPolynomial.eval (fun j => p j + 0 * v j) P| ≤ 2 * K
      exact (abs_sub _ _).trans (by linarith [hwhole t ht, hwhole 0 hzero])
    · have hj := hbase t ht j
      fin_cases j <;> simpa [nativePhysicalCurve, liftedVector] using hj
  obtain ⟨S, hS⟩ := exists_curve_cell_table
    (fun t j => nativePhysicalCurve P p v t j) hq (by positivity : 0 ≤ 2 * K) hspan
  let witness (c : Fin 4 → ℤ) : ℝ := if hc : c ∈ S then (hS c |>.mp hc).choose else 0
  have hw (c : Fin 4 → ℤ) (hc : c ∈ S) :
      witness c ∈ Icc (0 : ℝ) 1 ∧
        (fun j => (⌊nativePhysicalCurve P p v (witness c) j / q⌋ : ℤ)) = c := by
    simpa only [witness, dif_pos hc] using (hS c |>.mp hc).choose_spec
  refine ⟨S, ?_, hS⟩
  exact native_curve_cell_count P hP p v K q hK hq hv hwhole S witness
    (fun c hc => (hw c hc).1) (fun c hc j => congrFun (hw c hc).2 j)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
