/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDyadicBridge.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDyadicBridge.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! A fixed finite bridge between any two comparable dyadic heights. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable def scalarDyadicBridge (top start j : ℕ) : ℕ :=
  min top ⌈(33 / 32 : ℝ) ^ j * start⌉₊

theorem scalarDyadicBridge_zero {top start : ℕ} (h : start ≤ top) :
    scalarDyadicBridge top start 0 = start := by
  simp only [scalarDyadicBridge, pow_zero, one_mul, Nat.ceil_natCast, min_eq_right h]

theorem scalarDyadicBridge_le_top (top start j : ℕ) : scalarDyadicBridge top start j ≤ top :=
  min_le_left _ _

theorem scalarDyadicBridge_monotone (top start : ℕ) : Monotone (scalarDyadicBridge top start) := by
  intro i j hij
  exact min_le_min le_rfl (Nat.ceil_mono (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 33 / 32) hij) (Nat.cast_nonneg start)))

theorem scalarDyadicBridge_step (top start j : ℕ) :
    (scalarDyadicBridge top start (j + 1) : ℝ) ≤ (33 / 32 : ℝ) * scalarDyadicBridge top start j + 1 := by
  by_cases htop : top ≤ ⌈(33 / 32 : ℝ) ^ j * start⌉₊
  · have hprev : scalarDyadicBridge top start j = top := min_eq_left htop
    have hnext : (scalarDyadicBridge top start (j + 1) : ℝ) ≤ top := by
      exact_mod_cast scalarDyadicBridge_le_top top start (j + 1)
    rw [hprev]
    nlinarith [Nat.cast_nonneg (α := ℝ) top]
  · have hprev : scalarDyadicBridge top start j = ⌈(33 / 32 : ℝ) ^ j * start⌉₊ :=
      min_eq_right (by omega)
    have hnext : (scalarDyadicBridge top start (j + 1) : ℝ) ≤
        (⌈(33 / 32 : ℝ) ^ (j + 1) * start⌉₊ : ℝ) := by
      exact_mod_cast (min_le_right top ⌈(33 / 32 : ℝ) ^ (j + 1) * start⌉₊)
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (33 / 32 : ℝ) ^ (j + 1) * start by positivity)
    have hstart := mul_le_mul_of_nonneg_left (Nat.le_ceil ((33 / 32 : ℝ) ^ j * start))
      (by norm_num : (0 : ℝ) ≤ 33 / 32)
    have he : (33 / 32 : ℝ) ^ (j + 1) * start = (33 / 32 : ℝ) * ((33 / 32 : ℝ) ^ j * start) := by
      rw [pow_succ]
      ring
    rw [hprev]
    exact hnext.trans (hceil.le.trans (by rw [he]; linarith only [hstart]))

theorem scalarDyadicBridge_eq_top {top start j : ℕ}
    (h : (top : ℝ) ≤ (33 / 32 : ℝ) ^ j * start) : scalarDyadicBridge top start j = top := by
  exact min_eq_left (by exact_mod_cast h.trans (Nat.le_ceil _))

theorem exists_scalar_dyadic_bridge_length (R : ℝ) :
    ∃ m : ℕ, ∀ top start : ℕ, (top : ℝ) ≤ R * start → scalarDyadicBridge top start m = top := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 33 / 32)
  exact ⟨m, fun top start h => scalarDyadicBridge_eq_top
    (h.trans (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg start)))⟩

noncomputable def scalarDyadicLength (T : ℕ) : ℝ := (2 : ℝ) ^ (-(T : ℝ))

theorem scalarDyadicLength_eq (T : ℕ) : scalarDyadicLength T = 1 / ((2 ^ T : ℕ) : ℝ) := by
  simp only [scalarDyadicLength, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
    Nat.cast_pow, Nat.cast_ofNat, one_div]

theorem scalarDyadicLength_pos (T : ℕ) : 0 < scalarDyadicLength T :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem scalarDyadicLength_le_one (T : ℕ) : scalarDyadicLength T ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg T))

theorem scalarDyadicLength_antitone : Antitone scalarDyadicLength := by
  intro i j hij
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by exact_mod_cast (show -(j : ℤ) ≤ -(i : ℤ) from neg_le_neg (by exact_mod_cast hij)))

theorem scalarDyadicLength_lower_of_height_growth {a b : ℕ}
    (h : (b : ℝ) ≤ (33 / 32 : ℝ) * a + 1) :
    (scalarDyadicLength a) ^ (33 / 32 : ℝ) / 2 ≤ scalarDyadicLength b := by
  calc
    _ = (2 : ℝ) ^ (-(a : ℝ) * (33 / 32 : ℝ)) / 2 := by
      rw [scalarDyadicLength, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (2 : ℝ) ^ (-(a : ℝ) * (33 / 32 : ℝ) - 1) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (-(a : ℝ) * (33 / 32 : ℝ)) 1).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
