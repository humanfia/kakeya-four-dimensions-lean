-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.SlopeCharts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.BoundedSlope

/- Adapted from this workspace: o105/x0274 at 35a5b631a2b1dd244919169070ab09719347944a. -/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- Clamping gives a globally bounded Lipschitz extension of either slope chart. -/
theorem bounded_lipschitz_extension {g : ℝ → ℝ} {D : Set ℝ}
    (hg : LipschitzOnWith 1 g D) (hbound : ∀ z ∈ D, |g z| ≤ 1) :
    ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧ (∀ z, |h z| ≤ 1) ∧ EqOn g h D := by
  obtain ⟨h, hh, heq⟩ := hg.extend_real
  refine ⟨fun z => max (-1) (min 1 (h z)), (hh.const_min 1).const_max (-1), ?_, ?_⟩
  · intro z
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro z hz
    dsimp only
    rw [← heq hz]
    have hb := abs_le.mp (hbound z hz)
    rw [min_eq_right hb.2, max_eq_right hb.1]

/-- The two horizontal coordinate charts have uniformly bounded 1-Lipschitz slopes. -/
theorem exists_bounded_slope_charts {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    ∃ g h : ℝ → ℝ, LipschitzWith 1 g ∧ LipschitzWith 1 h ∧
      (∀ z, |g z| ≤ 1) ∧ (∀ z, |h z| ≤ 1) ∧
      (∀ z, |f z| ≤ 1 → g z = f z) ∧
      (∀ z, 1 ≤ |f z| → h z = (f z)⁻¹) := by
  obtain ⟨g, hg, hgb, hgeq⟩ := bounded_lipschitz_extension
    (D := {z | |f z| ≤ 1}) hf.lipschitzOnWith (fun _ hz => hz)
  obtain ⟨h, hh, hhb, hheq⟩ := bounded_lipschitz_extension
    (reciprocal_lipschitzOn hf (D := {z | 1 ≤ |f z|}) (fun _ hz => hz))
    (fun z hz => by
      rw [abs_inv, ← one_div]
      exact (div_le_one (zero_lt_one.trans_le hz)).mpr hz)
  exact ⟨g, h, hg, hh, hgb, hhb, fun z hz => (hgeq hz).symm,
    fun z hz => (hheq hz).symm⟩

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
