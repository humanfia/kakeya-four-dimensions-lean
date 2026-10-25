-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.RecoverEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_tube_estimate.Interfaces
import Submission.WZ.Obl.wz_rescaled_tube_estimate.SlabTransport

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A centered segment contains the origin, so its thickening covers the ball
of the same radius. -/
theorem ball_subset_centered_tube (r : ℝ) (w : Space) :
    Metric.ball (0 : Space) r ⊆ Tube r (-(1 / 2 : ℝ) • w) w := by
  apply Metric.ball_subset_thickening
  rw [segment_eq_image']
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  module

/-- Every finite-radius capsule has finite volume. -/
theorem tube_volume_ne_top (r : ℝ) (x v : Space) : volume (Tube r x v) ≠ ⊤ := by
  have hs : IsCompact (segment ℝ x (x + v)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact hs.isBounded.thickening.measure_lt_top.ne

namespace Interfaces

/-- The local rescaling interface recovers the original unit-ball estimate.
Only a fixed enlargement of the below-slab reference body is needed. -/
theorem estimate_of_local_rescaling {σ ω : ℝ} (hR : R σ ω) : E σ ω := by
  let w : Space := EuclideanSpace.single 0 1
  have hw : ‖w‖ = 1 := by simp [w]
  let y : Space := -(1 / 2 : ℝ) • w
  let D : Set Space := Tube 2 (y - (1 / 2 : ℝ) • w) (2 • w)
  have hDshape : y - (1 / 2 : ℝ) • w = -(1 / 2 : ℝ) • (2 • w) := by dsimp [y]; module
  have hD : Metric.ball (0 : Space) 1 ⊆ D := by
    dsimp [D]
    rw [hDshape]
    exact (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)).trans
      (ball_subset_centered_tube 2 (2 • w))
  let C : ℝ := max 1 (volume D).toReal
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hDC : volume D ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (tube_volume_ne_top 2 _ _)]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hlocal⟩ := hR ε hε
  refine ⟨κ * C ^ (-σ), mul_pos hκ (Real.rpow_pos_of_pos hC _), η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hA
  have hδ1 : δ ≤ 1 := by linarith
  have hCl : 1 ≤ C * l := one_le_mul_of_one_le_of_one_le hC1 hl
  have hcover : ∀ i, T δ (x i) (v i) ⊆ T 1 y w :=
    fun i => (hA.2.1 i).2.1.trans (ball_subset_centered_tube 1 w)
  have hbelow : B δ 1 (C * l) n 1 x v Finset.univ
      (fun _ => y) (fun _ => w) (fun _ => 0) := by
    have hcount := reference_count_of_frostman hC.le hD hDC
      (fun i => (hA.2.1 i).2.1) hA.2.2.2.2.2
    intro k u t r hu hr
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simpa [B, q, o, μ, T, D] using hcount u t r hu hr
  have hout := hlocal δ 1 hδ hδ100 hδ1 le_rfl m (C * l) hm hCl n x v Y y w
    hA.1 hw (fun i => ⟨(hA.2.1 i).1, hcover i, (hA.2.1 i).2.2⟩)
    hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2.1 hbelow
  have heq : κ * δ ^ ε * (δ / 1) ^ ω * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * (C * l) * (n * δ / 1)) ^ (-σ) =
      (κ * C ^ (-σ)) * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ) := by
    rw [div_one, div_one,
      show m ^ (-(3 / 2 : ℝ)) * (C * l) * (n * δ) =
        C * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) by ring,
      Real.mul_rpow hC.le (by positivity), Real.rpow_add hδ]
    ring
  simpa only [heq] using hout

end Interfaces
end WangZahlLot.Obl.wz_rescaled_tube_estimate
