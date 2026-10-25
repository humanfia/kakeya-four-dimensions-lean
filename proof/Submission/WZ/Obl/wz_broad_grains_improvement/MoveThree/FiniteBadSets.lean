-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FiniteBadSets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FiniteBadSets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (half_mass_after_loss)

/-- Either one of finitely many bad sets has a definite fraction of the
mass, or their common complement retains half of it. -/
theorem finite_bad_set_dichotomy (ν : Measure V) (hfin : ν univ ≠ ⊤)
    {k : ℕ} (hk : 0 < k) (B : Fin k → Set V) (hB : ∀ j, MeasurableSet (B j)) :
    (∃ j, O (1 / (2 * (k : ℝ))) * ν univ ≤ ν (B j)) ∨
      (1 / 2 : ENNReal) * ν univ ≤ ν (⋃ j, B j)ᶜ := by
  classical
  by_cases h : ∃ j, O (1 / (2 * (k : ℝ))) * ν univ ≤ ν (B j)
  · exact Or.inl h
  right
  have hbad j : ν (B j) ≤ O (1 / (2 * (k : ℝ))) * ν univ :=
    le_of_not_ge (fun hj => h ⟨j, hj⟩)
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hcoef : (k : ENNReal) * O (1 / (2 * (k : ℝ))) = (1 / 2 : ENNReal) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    have he : (k : ℝ) * (1 / (2 * (k : ℝ))) = 1 / 2 := by field_simp
    rw [he, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hloss : ν (⋃ j, B j) ≤ (1 / 2 : ENNReal) * ν univ := by
    calc
      _ ≤ ∑ j, ν (B j) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin k, O (1 / (2 * (k : ℝ))) * ν univ := Finset.sum_le_sum fun j _ => hbad j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, hcoef]
  have hsplit : ν univ ≤ ν (⋃ j, B j)ᶜ + ν (⋃ j, B j) := by
    have he := measure_inter_add_sdiff (μ := ν) univ (MeasurableSet.iUnion hB)
    have heq : (univ \ (⋃ j, B j)) = (⋃ j, B j)ᶜ := by ext p; simp
    simpa only [univ_inter, heq, add_comm] using he.symm.le
  exact half_mass_after_loss hfin hsplit hloss

/-- The same finite exceptional-set argument with an arbitrary loss budget. -/
theorem finite_bad_set_loss (ν : Measure V) {k : ℕ} (hk : 0 < k)
    (B : Fin k → Set V) (t : ℝ) :
    (∃ j, O (t / (k : ℝ)) * ν univ ≤ ν (B j)) ∨
      ν (⋃ j, B j) ≤ O t * ν univ := by
  classical
  by_cases h : ∃ j, O (t / (k : ℝ)) * ν univ ≤ ν (B j)
  · exact Or.inl h
  right
  have hbad j : ν (B j) ≤ O (t / (k : ℝ)) * ν univ :=
    le_of_not_ge (fun hj => h ⟨j, hj⟩)
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hcoef : (k : ENNReal) * O (t / (k : ℝ)) = O t := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    congr 1
    field_simp
  calc
    _ ≤ ∑ j, ν (B j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, O (t / (k : ℝ)) * ν univ := Finset.sum_le_sum fun j _ => hbad j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← mul_assoc, hcoef]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
