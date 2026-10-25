-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds.Calculus.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds

noncomputable def curve (f : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin 3)) (z : ℝ) : ℝ :=
  q 0 + q 1 * f z + q 2 * z * f z

lemma curve_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (q : EuclideanSpace ℝ (Fin 3)) : ContDiff ℝ 2 (curve f q) := by
  unfold curve
  exact (contDiff_const.add (contDiff_const.mul hf)).add
    ((contDiff_const.mul contDiff_id).mul hf)

lemma curve_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (q : EuclideanSpace ℝ (Fin 3)) (z : ℝ) :
    deriv (curve f q) z = (q 1 + q 2 * z) * deriv f z + q 2 * f z := by
  have hd := (hf.differentiable (by norm_num) z).hasDerivAt
  have h := ((hasDerivAt_const z (q 0)).add (hd.const_mul (q 1))).add
    (((hasDerivAt_id z).const_mul (q 2)).mul hd)
  convert h.deriv using 1
  · rfl
  · dsimp
    ring

lemma curve_deriv_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (q : EuclideanSpace ℝ (Fin 3)) (z : ℝ) :
    deriv (deriv (curve f q)) z =
      (q 1 + q 2 * z) * deriv (deriv f) z + 2 * q 2 * deriv f z := by
  have hd := (hf.differentiable (by norm_num) z).hasDerivAt
  have hdd := (hf.differentiable_deriv_two z).hasDerivAt
  have h := (((hasDerivAt_const z (q 1)).add
    ((hasDerivAt_id z).const_mul (q 2))).mul hdd).add (hd.const_mul (q 2))
  rw [show deriv (curve f q) =
    (fun x => (q 1 + q 2 * x) * deriv f x + q 2 * f x) from
      funext (curve_deriv hf q)]
  convert h.deriv using 1
  · rfl
  · dsimp
    ring

lemma value_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hd : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |deriv f z| ≤ 2)
    (h0 : |f 0| ≤ 1) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |f z| ≤ 3 := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hd x hx)
    (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num) hz
  simp only [Real.norm_eq_abs, sub_zero] at h
  have hz' : |z| ≤ 1 := abs_le.mpr hz
  have htri := abs_add_le (f z - f 0) (f 0)
  rw [sub_add_cancel] at htri
  linarith

end WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds
