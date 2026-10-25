-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.UniformLocal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Elementary
import Submission.WZ.Obl.wz_multiscale_finite_tower.LocalEstimates
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

lemma FrameAdmissible.mono {d r θ θ' : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : FrameAdmissible d r θ n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') : FrameAdmissible d r θ' n x v Y := by
  have hp : d ^ θ' ≤ d ^ θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθ
  have hn : d ^ (-θ) ≤ d ^ (-θ') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1.mono hn, h.2.2.2.2.2.mono hn⟩
  exact (ENNReal.ofReal_le_ofReal (by gcongr)).trans h.2.2.2.1

/-- The endpoint assumption gives a lower bound on every normalized interval in a tower.
All losses are measured at the same bottom radius, even for intervals close to radius one. -/
theorem Endpoint.all_local_scales {σ ω : ℝ} (hE : Endpoint σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    {loss D : ℝ} (hloss : 0 < loss) (hD : 0 < D) :
    ∃ a : ℝ, 0 < a ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧
    ∀ d r : ℝ, 0 < d → d ≤ 1 → d ≤ d₀ → d ≤ r → r ≤ 1 →
      ∀ n x v Y, FrameAdmissible d r θ n x v Y →
      ENNReal.ofReal (a * d ^ loss * volumeFactor σ ω r n) ≤ volume (⋃ i, Y i) := by
  let h : ℝ := loss / 10
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨a, ha, η, hη, hη1, hlarge⟩ := hE.on_large_gap hσ hloss hh
  obtain ⟨d₀, hd₀, hd₀D, hcut⟩ := exists_scale_cutoff (1 / 100) h D (by norm_num) hh hD
  let θ : ℝ := min η (loss / 8)
  have hθ : 0 < θ := lt_min hη (by positivity)
  have hθη : θ ≤ η := min_le_left _ _
  have hθloss : θ ≤ loss / 8 := min_le_right _ _
  refine ⟨min a (1 / 16), lt_min ha (by norm_num), θ, hθ, hθη.trans hη1,
    d₀, hd₀, hd₀D, ?_⟩
  intro d r hd hd1 hdd hdr hr1 n x v Y hA
  have hr : 0 < r := hd.trans_le hdr
  have hfac : 0 ≤ d ^ loss * volumeFactor σ ω r n := by dsimp [volumeFactor]; positivity
  rcases le_total (d ^ h) r with hgap | hgap
  · have hv := hA.small_gap hd hd1 hr hr1 hσ hσ1 hω hgap
      (show 2 * θ + (5 / 2 : ℝ) * h ≤ loss by dsimp [h]; linarith)
    apply le_trans (ENNReal.ofReal_le_ofReal _) hv
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_right a (1 / 16)) hfac
  · have hr100 : r ≤ 1 / 100 := hgap.trans (hcut d hd hdd)
    have hv := hlarge d r hd hd1 hdr hr100 hgap n x v Y (hA.mono hd hd1 hθη)
    apply le_trans (ENNReal.ofReal_le_ofReal _) hv
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_left a (1 / 16)) hfac

end WangZahlLot.Obl.wz_multiscale_finite_tower
