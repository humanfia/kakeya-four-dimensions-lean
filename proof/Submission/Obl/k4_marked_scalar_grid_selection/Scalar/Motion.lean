/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/Motion.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Atoms
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation
import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.LineGeometry

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open Set

private theorem norm_three_le {a : EuclideanSpace ℝ (Fin 3)} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ i, |a i| ≤ K) : ‖a‖ ≤ 3 * K := by
  simpa only [WithLp.toLp_ofLp] using
    (Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.norm_toLp_three_le
      (z := WithLp.ofLp a) hK ha)

/-- Polynomial trajectory evaluation is stable over one marked time cell and
under the common coefficient noise. -/
theorem quadratic_atom_motion (b u : Fin 3 → ℝ) {K σ t t₀ : ℝ}
    (hK : 0 ≤ K) (hσ : 0 ≤ σ) (hb : ∀ i, |b i| ≤ K) (hu : ∀ i, |u i| ≤ σ)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hstep : |t - t₀| ≤ σ) :
    |((b 0 + u 0) + t * (b 1 + u 1) + t ^ 2 * (b 2 + u 2)) -
      (b 0 + t₀ * b 1 + t₀ ^ 2 * b 2)| ≤ 9 * (K + 1) * σ := by
  let a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 b
  let a' : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (b + u)
  have hb' : ‖a‖ ≤ 3 * K := norm_three_le hK hb
  have hu' : ‖a' - a‖ ≤ 3 * σ := by
    apply norm_three_le hσ
    intro i
    simpa [a, a', PiLp.sub_apply, Pi.add_apply] using hu i
  have hd := Submission.Obl.k4_scalar_coefficient_clustering.quadratic_difference_le
    (a := a') (b := a) ht
  have ht' := Submission.Obl.k4_scalar_coefficient_clustering.quadratic_time_lipschitz
    hb' ht ht₀
  have htri := abs_sub_le
    (Submission.Obl.k4_scalar_coefficient_clustering.quadratic a' t)
    (Submission.Obl.k4_scalar_coefficient_clustering.quadratic a t)
    (Submission.Obl.k4_scalar_coefficient_clustering.quadratic a t₀)
  have hs := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 3 * (3 * K) by positivity)
  simp only [Submission.Obl.k4_scalar_coefficient_clustering.quadratic, a, a',
    Pi.add_apply] at hd ht' htri
  nlinarith

/-- The left endpoint of a marked cell is at distance at most the noise width
from every time in that cell. -/
theorem cell_time_control {J : ℕ} (hJ : 0 < J) {σ : ℝ}
    (hmesh : 1 ≤ (J : ℝ) * σ) (z : Fin J) {t : ℝ} (ht : t ∈ cell J z) :
    t ∈ Icc (0 : ℝ) 1 ∧ ((z : ℝ) / J) ∈ Icc (0 : ℝ) 1 ∧
      |t - (z : ℝ) / J| ≤ σ := by
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  have ht01 := cell_subset hJ z ht
  have hz0 : 0 ≤ (z : ℝ) / (J : ℝ) := div_nonneg (by positivity) hJr.le
  have hz1 : (z : ℝ) / (J : ℝ) ≤ 1 := by
    apply (div_le_one hJr).mpr
    exact_mod_cast z.isLt.le
  refine ⟨⟨ht01.1, ht01.2.le⟩, ⟨hz0, hz1⟩, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have hstep : 1 / (J : ℝ) ≤ σ := (div_le_iff₀ hJr).mpr (by nlinarith)
  have ht' := ht.2
  have heq : ((z : ℝ) + 1) / (J : ℝ) = (z : ℝ) / (J : ℝ) + 1 / (J : ℝ) := by ring
  rw [heq] at ht'
  linarith

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
