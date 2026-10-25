-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.StrictBootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedBootstrap
import Submission.WZ.Obl.wz_rescaled_tube_estimate
import Submission.WZ.Obl.wz_endpoint_bootstrap.Estimates

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (VolumeBound)

/-- The accepted affine rescaling theorem supplies the fibre estimate from the endpoint. -/
theorem rescaled_estimate_of_endpoint {σ ω : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) : R σ ω :=
  WangZahlLot.wz_rescaled_tube_estimate σ ω hσ hσ1 hω hω1
    O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl B rfl E rfl R rfl hE

/-- Once the prism endpoint is established, only the Frostman all-scales input remains. -/
theorem uniform_gain_of_frostman_and_prisms {σ ω : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hFrostman : FrostmanAllScales)
    (hPrism : ∀ ζ : ℝ, 0 < ζ → ζ ≤ ω / 1000 → PrismImprovement σ ω ζ) :
    UniformGain σ ω :=
  uniform_gain_of_aligned_one_scale hσ hσ1 hω hω1 hE hFrostman
    (aligned_one_scale_of_prisms hσ hσ1 hω hω1 hE
      (rescaled_estimate_of_endpoint hσ hσ1 hω hω1 hE) hPrism)

/-- The uniform gain implies the normalized strict improvement used by the bootstrap. -/
theorem UniformGain.strict_improvement {σ ω : ℝ} (hω : 0 < ω)
    (hGain : UniformGain σ ω) :
    ∃ g : ℝ, 0 < g ∧ g ≤ ω ∧ WangZahlLot.Obl.wz_endpoint_bootstrap.Estimate σ (ω - g) := by
  obtain ⟨α, κ, η, hα, hκ, hη, HG⟩ := hGain
  let g := min α (ω / 2)
  have hg : 0 < g := lt_min hα (by positivity)
  have hgα : g ≤ α := min_le_left _ _
  refine ⟨g, hg, (min_le_right _ _).trans (by linarith), ?_⟩
  intro ε hε
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro d hd hd100 n x v Y hn hv hball hX hmeas hsub hdense hK hF
  have hA : A d η (d ^ (-η)) (d ^ (-η)) n x v Y :=
    ⟨hn, fun i => ⟨hv i, hball i, hmeas i, hsub i⟩, hX, hdense, hK, hF⟩
  have h := (HG d hd hd100 n x v Y hA).mono hd
    (hd100.trans (by norm_num)) hκ.le le_rfl (show g - ε ≤ α by linarith)
  simpa only [VolumeBound, show ω - (g - ε) = ω - g + ε by ring] using h

end WangZahlLot.Obl.wz_broad_grains_improvement
