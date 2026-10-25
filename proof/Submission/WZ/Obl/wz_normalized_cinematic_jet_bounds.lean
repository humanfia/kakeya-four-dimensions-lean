-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_normalized_cinematic_jet_bounds.Calculus
import Submission.WZ.Obl.wz_normalized_cinematic_jet_bounds.Algebra
set_option linter.unusedVariables false

/-!
Uniform comparison between coefficient distance and the first three jets of the
normalized curve family, using elementary calculus and coefficient recovery.
-/

open WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds in
theorem WangZahlLot.wz_normalized_cinematic_jet_bounds : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) → |f 0| ≤ 1 → (fun G : EuclideanSpace ℝ (Fin 3) → ℝ → ℝ => (∀ q : EuclideanSpace ℝ (Fin 3), ContDiff ℝ 2 (G q)) ∧ ∀ (q r : EuclideanSpace ℝ (Fin 3)) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist q r ≤ 30 * (|G q z - G r z| + |deriv (G q) z - deriv (G r) z| + |deriv (deriv (G q)) z - deriv (deriv (G r)) z|) ∧ (|G q z - G r z| + |deriv (G q) z - deriv (G r) z| + |deriv (deriv (G q)) z - deriv (deriv (G r)) z|) ≤ 19 * dist q r) (fun q z => q 0 + q 1 * f z + q 2 * z * f z) := by
  intro f hf hb h0
  refine ⟨curve_contDiff hf, ?_⟩
  intro q r z hz
  change dist q r ≤ 30 * (|curve f q z - curve f r z| +
      |deriv (curve f q) z - deriv (curve f r) z| +
      |deriv (deriv (curve f q)) z - deriv (deriv (curve f r)) z|) ∧
    (|curve f q z - curve f r z| + |deriv (curve f q) z - deriv (curve f r) z| +
      |deriv (deriv (curve f q)) z - deriv (deriv (curve f r)) z|) ≤ 19 * dist q r
  have hA : curve f q z - curve f r z =
      (q 0 - r 0) + ((q 1 - r 1) + (q 2 - r 2) * z) * f z := by
    unfold curve
    ring
  have hB : deriv (curve f q) z - deriv (curve f r) z =
      ((q 1 - r 1) + (q 2 - r 2) * z) * deriv f z + (q 2 - r 2) * f z := by
    rw [curve_deriv hf, curve_deriv hf]
    ring
  have hC : deriv (deriv (curve f q)) z - deriv (deriv (curve f r)) z =
      ((q 1 - r 1) + (q 2 - r 2) * z) * deriv (deriv f) z +
        2 * (q 2 - r 2) * deriv f z := by
    rw [curve_deriv_two hf, curve_deriv_two hf]
    ring
  rw [hA, hB, hC]
  have hv := value_bound hf (fun x hx => (hb x hx).2.1) h0 hz
  have hz' : |z| ≤ 1 := abs_le.mpr hz
  have hcoord (i : Fin 3) : |q i - r i| ≤ dist q r := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (q - r) i
  constructor
  · have hn : dist q r ≤ |q 0 - r 0| + |q 1 - r 1| + |q 2 - r 2| := by
      simpa [dist_eq_norm] using norm_le_abs_sum (q - r)
    exact hn.trans (coefficients_le_jet (q 0 - r 0) (q 1 - r 1) (q 2 - r 2)
      z (f z) (deriv f z) (deriv (deriv f) z) hz' hv (hb z hz).1 (hb z hz).2.2)
  · exact jet_le_bound (q 0 - r 0) (q 1 - r 1) (q 2 - r 2)
      z (f z) (deriv f z) (deriv (deriv f) z) (dist q r) hz' hv
      (hb z hz).2.1 (hb z hz).2.2 (hcoord 0) (hcoord 1) (hcoord 2)
