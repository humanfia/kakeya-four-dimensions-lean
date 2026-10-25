-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.WindowGridNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/WindowGridNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/WindowGridNumerics.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/WindowGridNumerics.lean.
-- Existing source attributions are preserved below.

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A fixed middle-quarter entropy grid with a genuine later window.
These choices precede the source problem, its path and every residual. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem exists_native_window_grid {gain mesh : ℝ} (hgain : 0 < gain)
    (hgainUpper : gain ≤ 1 / 32) (hmesh : 0 < mesh) :
    ∃ (m C : ℕ) (A : Finset ℕ),
      0 < m ∧ Even m ∧ 2 ≤ m ∧ 1 / (m : ℝ) ≤ gain ∧ 1 / (m : ℝ) ≤ mesh ∧
      1 ≤ C ∧ 2 * gain ≤ (C : ℝ) / m ∧ (C : ℝ) / m ≤ 3 * gain ∧
      (m : ℝ) / 4 ≤ (A.card : ℝ) ∧
      (∀ i ∈ A, i < m ∧ i + C < m ∧
        1 / 4 ≤ ((i : ℝ) + 1) / m ∧ ((i : ℝ) + 1) / m ≤ 1 / 2) ∧
      ∀ u : ℝ, 0 < u →
        2 * (C : ℝ) * (4 * u + 4 * u) <
          (A.card : ℝ) * ((65536 * gain * u) * (1 / 128)) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hgain hmesh)
  let q := n + 1
  let m := 4 * q
  let C := ⌈2 * (m : ℝ) * gain⌉₊
  let A := Finset.Ico (q - 1) (2 * q)
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hm : 0 < m := by dsimp [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hmq : (m : ℝ) = 4 * (q : ℝ) := by dsimp [m]; push_cast; rfl
  have hsmall : 1 / (m : ℝ) ≤ min gain mesh := by
    apply le_trans (one_div_le_one_div_of_le hqpos (by rw [hmq]; linarith))
    simpa only [q, Nat.cast_add, Nat.cast_one] using hn.le
  have hmgain : 1 ≤ (m : ℝ) * gain := by
    have h := (div_le_iff₀ hmpos).mp (hsmall.trans (min_le_left _ _))
    nlinarith
  have hCpos : 1 ≤ C := Nat.one_le_ceil_iff.mpr (by positivity)
  have hClower : 2 * (m : ℝ) * gain ≤ (C : ℝ) := Nat.le_ceil _
  have hCupper : (C : ℝ) ≤ 3 * (m : ℝ) * gain := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * (m : ℝ) * gain by positivity)
    change (C : ℝ) < 2 * (m : ℝ) * gain + 1 at h
    nlinarith
  have hCq : C ≤ q := by
    have h : (C : ℝ) ≤ (q : ℝ) := by
      rw [hmq] at hCupper
      nlinarith
    exact_mod_cast h
  have hcard : q ≤ A.card := by
    dsimp only [A]
    rw [Nat.card_Ico]
    omega
  have hcardReal : (m : ℝ) / 4 ≤ (A.card : ℝ) := by
    rw [hmq]
    have h : (q : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
    linarith
  refine ⟨m, C, A, hm, ⟨2 * q, by dsimp [m]; omega⟩, by dsimp [m]; omega,
    hsmall.trans (min_le_left _ _), hsmall.trans (min_le_right _ _), hCpos,
    (le_div_iff₀ hmpos).mpr (by nlinarith), (div_le_iff₀ hmpos).mpr (by nlinarith),
    hcardReal, ?_, ?_⟩
  · intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    have hilow : (q : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast (show q ≤ i + 1 by omega)
    have hihigh : (i : ℝ) + 1 ≤ 2 * (q : ℝ) := by
      exact_mod_cast (show i + 1 ≤ 2 * q by omega)
    refine ⟨by dsimp [m]; omega, by dsimp [m]; omega, ?_, ?_⟩
    · apply (le_div_iff₀ hmpos).mpr
      rw [hmq]
      linarith
    · apply (div_le_iff₀ hmpos).mpr
      rw [hmq]
      linarith
  · intro u hu
    calc
      _ ≤ 48 * (m : ℝ) * gain * u := by
        nlinarith [mul_le_mul_of_nonneg_right hCupper hu.le]
      _ < ((m : ℝ) / 4) * ((65536 * gain * u) * (1 / 128)) := by
        nlinarith [mul_pos (mul_pos hmpos hgain) hu]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardReal (by positivity)

theorem native_window_exponent_gap {S gain u : ℝ} (hS : 0 < S)
    (hu : 0 < u) (hgain : gain ≤ S / 67108864) :
    4 * (65536 * gain * u) < S * u / 64 := by
  have h := mul_le_mul_of_nonneg_right hgain hu.le
  nlinarith [mul_pos hS hu]

theorem native_angular_exponent_budget {S u τ : ℝ} (hS : 0 < S)
    (hu : 0 < u) (hτ : τ ≤ S * u / 4096) :
    -S * (u / 16) + 2 * τ ≤ -(S * u / 64) := by
  nlinarith [mul_pos hS hu]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
