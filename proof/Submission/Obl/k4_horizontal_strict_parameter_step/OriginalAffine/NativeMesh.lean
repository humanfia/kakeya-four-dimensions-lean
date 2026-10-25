/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeMesh.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.MeshChoice
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeComparison
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_derivative_evaluation_lists

/-- The deterministic physical mesh is two fixed ambient powers finer than
the child's hidden width. -/
lemma original_affine_mesh_identity {N s : ℝ} (hN : 0 < N) :
    N ^ (-(s + 2)) = N ^ (-s) / N ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_sub hN]
  congr 1
  norm_num
  ring

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- A fixed integer mesh and a fixed-power physical mesh resolve every true
child box, uniformly over its nonnegative depth.  Only the subcritical scale
inequality and the original atlas are used. -/
theorem original_affine_mesh_resolves {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s)
    (hlarge : 69120 * cfg.K k ^ 8 ≤ cfg.N k) :
    let H := ⌈cfg.N k⌉₊
    let η := cfg.N k ^ (-(s + 2))
    0 < H ∧ η ≤ cfg.timeLength k s / H ∧
    (2 * cfg.K k + 1) * η ≤
      2 * cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) / H ∧
    24 * cfg.K k ^ 4 * η ≤ cfg.N k ^ (-s) ∧ 69120 * cfg.K k ^ 8 ≤ (H : ℝ) := by
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hNp : 0 < cfg.N k := by linarith
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hg : 0 < cfg.N k ^ (-cfg.ℓ * s) := Real.rpow_pos_of_pos hNp _
  have hg1 : cfg.N k ^ (-cfg.ℓ * s) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    rw [hℓ]
    nlinarith [mul_nonneg hκ hs]
  have hcmp : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.timeLength k s := by
    rw [hℓ]
    exact (time_length_comparison hNp hKp a.time_lower a.time_upper).2
  have hsquare : cfg.N k ^ (-s) ≤ (cfg.N k ^ (-cfg.ℓ * s)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    rw [hℓ]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hκ1)]
  have hvolume : cfg.N k ^ (-s) ≤
      cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) := by
    exact hsquare.trans (by nlinarith [mul_le_mul_of_nonneg_right hcmp hg.le])
  have hbase : cfg.N k ^ (-s) ≤ cfg.K k * cfg.timeLength k s := by
    apply hvolume.trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hg1 (mul_nonneg hKp.le hq.le)
  have hH : 0 < ⌈cfg.N k⌉₊ := Nat.one_le_ceil_iff.mpr hNp
  have hHlo : cfg.N k ≤ (⌈cfg.N k⌉₊ : ℝ) := Nat.le_ceil _
  have hHhi : (⌈cfg.N k⌉₊ : ℝ) ≤ 2 * cfg.N k := by
    linarith [Nat.ceil_lt_add_one hNp.le]
  dsimp only
  refine ⟨hH, ?_⟩
  rw [original_affine_mesh_identity hNp]
  exact native_fine_mesh_choice hN hK (Real.rpow_pos_of_pos hNp _) hq
    hH hHlo hHhi hlarge hbase hvolume

/-- The one numerical large-scale requirement is eventually automatic for
the original subpower slack, independently of the child's depth. -/
theorem eventually_original_affine_mesh_large
    (hN : ∀ k, 1 ≤ cfg.N k) (hNt : Tendsto cfg.N atTop atTop)
    (hK : ∀ k, 1 ≤ cfg.K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε) :
    ∀ᶠ k in atTop, 69120 * cfg.K k ^ 8 ≤ cfg.N k := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 8 (a := 0) (b := 1) (by norm_num)
    (A := 69120) (by norm_num)
  filter_upwards [h] with k hk
  simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hk.le

end NativeModel
end Submission.Obl.k4_horizontal_strict_parameter_step
