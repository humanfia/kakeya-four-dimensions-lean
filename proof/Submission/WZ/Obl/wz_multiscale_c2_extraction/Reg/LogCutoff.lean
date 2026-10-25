-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.LogCutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Filter Topology

/-- A positive power absorbs a logarithmic factor at small scales. -/
theorem exists_log_power_cutoff (A : ℝ) {B e : ℝ} (hB : 0 < B) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      A * (1 + Real.log (1 / δ)) * δ ^ e ≤ B := by
  have hp : Tendsto (fun δ : ℝ => δ ^ e) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne'] using
      (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero he
  have ht : Tendsto (fun δ : ℝ => A * (1 + Real.log (1 / δ)) * δ ^ e)
      (𝓝[>] 0) (𝓝 0) := by
    convert (hp.sub hl).const_mul A using 1
    · funext δ
      rw [one_div, Real.log_inv]
      ring
    · simp
  have hmem : {δ : ℝ | A * (1 + Real.log (1 / δ)) * δ ^ e < B} ∈ 𝓝[>] 0 :=
    ht (gt_mem_nhds hB)
  obtain ⟨d, hd, hcut⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hmem
  exact ⟨d, hd, fun δ hδ hδd => (hcut ⟨hδ, hδd⟩).le⟩

/-- A strict exponent gap absorbs constants and one logarithmic loss. -/
theorem exists_log_power_comparison (A : ℝ) {B e₁ e₂ : ℝ}
    (hB : 0 < B) (he : e₂ < e₁) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      A * (1 + Real.log (1 / δ)) * δ ^ e₁ ≤ B * δ ^ e₂ := by
  obtain ⟨d, hd, hcut⟩ := exists_log_power_cutoff A hB (sub_pos.mpr he)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have h := mul_le_mul_of_nonneg_right (hcut δ hδ hδd) (Real.rpow_nonneg hδ.le e₂)
  have hp : δ ^ (e₁ - e₂) * δ ^ e₂ = δ ^ e₁ := by
    rw [← Real.rpow_add hδ, sub_add_cancel]
  simpa only [mul_assoc, hp] using h

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
