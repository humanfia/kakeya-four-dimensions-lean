/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyFloorBudget.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyFloorBudget.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp

/-! The exact simultaneous deletion budget for finite time hierarchies. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalar_hierarchy_floor_budget {n : ℕ} (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i)
    {K : ℝ} (hK : 0 < K) :
    (∑ ij : (Σ i : Fin n, Fin (J i)), ENNReal.ofReal ((1 / (J ij.1 : ℝ)) / K)) =
      ENNReal.ofReal ((n : ℝ) / K) := by
  have hreal : (∑ ij : (Σ i : Fin n, Fin (J i)), (1 / (J ij.1 : ℝ)) / K) = (n : ℝ) / K := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he (i : Fin n) : (J i : ℝ) * (1 / (J i : ℝ) / K) = 1 / K := by
      have hJi : (J i : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (hJ i))
      field_simp
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  calc
    _ = ENNReal.ofReal (∑ ij : (Σ i : Fin n, Fin (J i)), (1 / (J ij.1 : ℝ)) / K) :=
      (ENNReal.ofReal_sum_of_nonneg (fun ij _ => by positivity)).symm
    _ = _ := congrArg ENNReal.ofReal hreal

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
