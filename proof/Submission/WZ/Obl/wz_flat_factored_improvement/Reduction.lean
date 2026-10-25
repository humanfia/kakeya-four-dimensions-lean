-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Transport

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set
open scoped ENNReal

/-- Quantitative aspect-ratio improvement implies the precise uniform gain in o065.

The gain is chosen before epsilon. Retention is paid for by reducing the
factorization tolerance, independently of the scale and the family.
-/
theorem flatConclusion_of_aspectRatio {σ u : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hu : 0 < u) (H : AspectRatioEstimate σ u) :
    FlatConclusion σ u := by
  intro β hβ
  refine ⟨β * u / 2, by positivity, ?_⟩
  intro ε hε
  obtain ⟨A, hA, η₀, hη₀, d, hd, H⟩ := H ε hε
  let η := min η₀ (β * u / 4)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨A, hA, η, hη, d, hd, ?_⟩
  intro ν hν hνη δ hδ hδ100 hδd m hm n x v Y hAdm hY a b hδa hab hb2 hF hflat
  have hνη₀ : ν ≤ η₀ := hνη.trans (min_le_left _ _)
  have hνsmall : ν ≤ β * u / 4 := hνη.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hn : 0 < (n : ℝ) := by exact_mod_cast hAdm.1
  obtain ⟨k, g, hg, hk, hret, c, hc, hcm, hconv, hcover⟩ := hF
  have hAdm' := admissible_restrict hδ g hg hk hret hAdm hY hconv
  have hY' : IndividuallyDense ν δ (Y ∘ g) := fun i => hY (g i)
  have hl : 1 ≤ δ ^ (-2 * ν) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hbound := H ν hν hνη₀ δ hδ hδ100 hδd c (δ ^ (-2 * ν)) hc hl
    k (x ∘ g) (v ∘ g) (Y ∘ g) hAdm' hY' a b hδa hab hb2 hcover
  calc
    ENNReal.ofReal (profile σ (u - β * u / 2) ε A δ m 1 n) ≤
        ENNReal.ofReal ((b / a) ^ u * profile σ u ε A δ c (δ ^ (-2 * ν)) k) := by
      apply ENNReal.ofReal_le_ofReal
      exact flat_profile_transfer hσ.le hσhalf hu hA.le hδ hδ1 hν.le hβ
        hνsmall ha hb (by linarith) hcm hn hret hflat
    _ ≤ volume (⋃ i, (Y ∘ g) i) := hbound
    _ ≤ volume (⋃ i, Y i) := volume_restrict g Y

end WangZahlLot.Obl.wz_flat_factored_improvement
