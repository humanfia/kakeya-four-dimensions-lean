import Submission.Obl.k4_narrow_projected_row_parents.ModelBridge
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMeshPowers

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Refining to the natural common major width by a subpower factor keeps
the width in a fixed power band, as needed by the uniform original caps. -/
theorem eventually_natural_major_lower (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) {s : ℝ} (hs : 0 ≤ s) (m : ℝ)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k) (hMsub : Model.Subpow p.N M) :
    ∀ᶠ k in atTop, ∀ R : ℝ, a.AtlasAt p R k s →
      p.N k ^ (-(max m ((p.kappa + p.ell + 1) * s + 1) + 2)) ≤
        min (p.N k ^ (-m)) (width p k s * a.q k s * narrow p k s) / (2 * M k) := by
  have hqg := a.eventually_q_narrow_lower p hp s (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hqg, hMsub 1 one_pos] with k hq hMk
  intro R hatlas
  have hN2 : 2 ≤ p.N k := hp.1 k
  have hN1 : 1 ≤ p.N k := by linarith
  have hN0 : 0 < p.N k := by linarith
  have hMp : 0 < M k := zero_lt_one.trans_le (hM k)
  rw [Real.rpow_one] at hMk
  let E : ℝ := (p.kappa + p.ell + 1) * s + 1
  let D : ℝ := max m E
  have harea : p.N k ^ (-E) ≤ width p k s * a.q k s * narrow p k s := by
    calc _ = p.N k ^ (-s) * p.N k ^ (-(p.kappa + p.ell) * s - 1) := by
           rw [← Real.rpow_add hN0]
           congr 1
           dsimp [E]
           ring
         _ ≤ p.N k ^ (-s) * (a.q k s * narrow p k s) :=
           mul_le_mul_of_nonneg_left (hq R s hatlas le_rfl) (Real.rpow_nonneg hN0.le _)
         _ = _ := by unfold width; ring
  have hsmall : p.N k ^ (-D) ≤ min (p.N k ^ (-m))
      (width p k s * a.q k s * narrow p k s) := by
    apply le_min
    · exact Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_left _ _))
    · exact (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_right _ _))).trans harea
  have hden : 2 * M k ≤ (p.N k) ^ 2 := by nlinarith
  calc p.N k ^ (-(max m ((p.kappa + p.ell + 1) * s + 1) + 2))
      = p.N k ^ (-D) / (p.N k) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_sub hN0]
          congr 1
          dsimp [D, E]
          ring
    _ ≤ p.N k ^ (-D) / (2 * M k) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hsmall (by positivity)

end Submission.Obl.k4_narrow_projected_row_parents
