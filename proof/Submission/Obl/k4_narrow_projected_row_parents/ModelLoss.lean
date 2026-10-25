/- Adapted from this LOT tree, obligation o254, session x0898, commit 52ee31b1,
   Submission/Obl/k4_general_parent_wide_layer_candidates/ParentLoss.lean.
   The atlas proof here uses the accepted general prepared-model interface. -/
import Submission.Obl.k4_narrow_projected_row_parents.ModelBridge

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] (cfg : Model α)

/-- Enlarge the permitted loss while retaining every original measure,
trajectory, polynomial and true assignment. -/
def withLoss (M : ℕ → ℝ) : Model α := { cfg with K := M }

theorem parameters_withLoss (M : ℕ → ℝ) :
    parameters (cfg.withLoss M) = { parameters cfg with K := M } := rfl

theorem prepared_withLoss (M : ℕ → ℝ) :
    prepared (cfg.withLoss M) = prepared cfg := rfl

theorem candidates_withLoss (M : ℕ → ℝ) :
    (cfg.withLoss M).Candidates ↔ cfg.Candidates := Iff.rfl

theorem basic_withLoss (hv : cfg.Basic) {M : ℕ → ℝ}
    (hK : ∀ k, 0 < cfg.K k) (hKM : ∀ k, cfg.K k ≤ M k) :
    (cfg.withLoss M).Basic := by
  dsimp only [Submission.Obl.k4_critical_intercept_concentration.Data.Basic, withLoss]
  intro k
  obtain ⟨hb, hν, hπ, hμ, hρ, hsupp, hmass, hP, hclip, hnative⟩ := hv k
  have hinv : (M k)⁻¹ ≤ (cfg.K k)⁻¹ := inv_anti₀ (hK k) (hKM k)
  refine ⟨hb, hν, hπ, hμ.trans ?_, hρ, hsupp,
    (ENNReal.ofReal_le_ofReal hinv).trans hmass, hP, ?_, ?_⟩
  · gcongr
    exact hKM k
  · exact hclip.mono (fun _ hl => hl.trans (hKM k))
  · filter_upwards [hnative] with z hz
    refine ⟨fun t ht => ?_, hinv.trans hz.2⟩
    exact ⟨(hz.1 t ht).1.trans (hKM k), (hz.1 t ht).2.1.trans (hKM k),
      (hz.1 t ht).2.2.trans (hKM k)⟩

theorem atlasAt_withLoss {k : ℕ} {s R : ℝ}
    (hat : (prepared cfg).AtlasAt (parameters cfg) R k s)
    (hN : 0 < cfg.N k) (hK : 0 < cfg.K k) {M : ℕ → ℝ} (hKM : cfg.K k ≤ M k) :
    (prepared (cfg.withLoss M)).AtlasAt (parameters (cfg.withLoss M)) R k s := by
  dsimp only [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.AtlasAt,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q,
    prepared, parameters, withLoss] at hat ⊢
  obtain ⟨hTlo, hThi, hsets, hdisj, hlabels, hcover, hpal⟩ := hat
  have hinv : (M k)⁻¹ ≤ (cfg.K k)⁻¹ := inv_anti₀ hK hKM
  have hq : 0 < (2 : ℝ) ^ (-(cfg.T k s : ℤ)) := by positivity
  have ha : 0 < cfg.N k ^ (-s) := by positivity
  have hg : 0 < cfg.N k ^ (-cfg.ℓ * s) := by positivity
  have hM : 0 ≤ M k := hK.le.trans hKM
  refine ⟨(div_le_div_of_nonneg_left (by positivity) hK hKM).trans hTlo,
    hThi.trans (mul_le_mul_of_nonneg_right hKM (by positivity)), hsets, hdisj, ?_, hcover, ?_⟩
  · intro i
    obtain ⟨hlo, hhi, hmass, hc, hF, hgeo, hfit, hderiv⟩ := hlabels i
    refine ⟨?_, ?_, ?_, fun e => (hc e).trans hKM, hF, ?_, ?_, ?_⟩
    · exact (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_left (by positivity) hK hKM)).trans hlo
    · apply hhi.trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
    · apply le_trans _ hmass
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_left hq.le hK hKM)) le_rfl
    · intro l hl t ht
      obtain ⟨hz, hy, hv⟩ := hgeo l hl t ht
      exact ⟨hz.trans (mul_le_mul_of_nonneg_right hKM hq.le),
        hy.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKM hq.le) hg.le),
        hv.trans (mul_le_mul_of_nonneg_right hKM hg.le)⟩
    · intro l hl t ht
      obtain ⟨hf, hd, hdd⟩ := hfit l hl t ht
      exact ⟨hf.trans (mul_le_mul_of_nonneg_right hKM ha.le), hd.trans hKM,
        hdd.trans (div_le_div_of_nonneg_right hKM ha.le)⟩
    · filter_upwards [hderiv] with z hz hl ht
      exact hinv.trans (hz hl ht)
  · intro i v v₀ hv hvR
    apply (hpal i v v₀ hv hvR).trans
    gcongr

theorem caps_withLoss (hv : cfg.Caps) {M : ℕ → ℝ}
    (hN : ∀ k, 0 < cfg.N k) (hKM : ∀ k, cfg.K k ≤ M k) :
    (cfg.withLoss M).Caps := by
  dsimp only [Submission.Obl.k4_critical_intercept_concentration.Data.Caps, withLoss]
  intro R hR
  filter_upwards [hv R hR] with k hk
  intro r s v hr hrR hs hsR hv hvR
  have hNk := hN k
  obtain ⟨hpal, hpure, hjoint⟩ := hk r s v hr hrR hs hsR hv hvR
  refine ⟨fun j => (hpal j).trans ?_, fun h q j => (hpure h q j).trans ?_,
    fun h q j v₀ => (hjoint h q j v₀).trans ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKM k) (by positivity))
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKM k) (by positivity))
  · exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hKM k) (by positivity))) le_rfl

/-- The whole frozen general model survives a larger subpower loss, including
the original true-label floors, palette numerators and hidden derivative test. -/
theorem Valid.withLoss {cfg : Model α} (hv : Valid cfg) {M : ℕ → ℝ}
    (hKM : ∀ k, cfg.K k ≤ M k) (hMs : Subpow cfg.N M) :
    Valid (cfg.withLoss M) := by
  have hK : ∀ k, 0 < cfg.K k := fun k => zero_lt_one.trans_le (hv.subpower.1 k)
  have hN : ∀ k, 0 < cfg.N k := fun k => by linarith [hv.scale k]
  refine { hv with
    subpower := ⟨fun k => (hv.subpower.1 k).trans (hKM k), hMs⟩
    basic := cfg.basic_withLoss hv.basic hK hKM
    caps := cfg.caps_withLoss hv.caps hN hKM
    atlas := ?_ }
  intro R hR
  filter_upwards [(prepared_valid hv).2.2.1 R hR] with k hk
  intro s hs hsU
  have hat := cfg.atlasAt_withLoss (hk s hs hsU) (hN k) (hK k) (hKM k)
  simpa [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.AtlasAt,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.block,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.interval,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.x,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.fit,
    Submission.Lib.K4ContactNormalization.point,
    Submission.Obl.k4_critical_intercept_concentration.Data.x,
    Submission.Obl.k4_critical_intercept_concentration.Data.I,
    Submission.Obl.k4_critical_intercept_concentration.Data.fit,
    parameters, prepared, withLoss] using hat

theorem parameters_valid_withLoss {cfg : Model α} (hv : Valid cfg)
    {M : ℕ → ℝ} (hKM : ∀ k, cfg.K k ≤ M k) (hMs : Subpow cfg.N M) :
    ({ parameters cfg with K := M } :
      Submission.Obl.k4_general_parent_projected_layers.Parameters).Valid :=
  parameters_valid (hv.withLoss hKM hMs)

theorem prepared_valid_withLoss {cfg : Model α} (hv : Valid cfg)
    {M : ℕ → ℝ} (hKM : ∀ k, cfg.K k ≤ M k) (hMs : Subpow cfg.N M) :
    (prepared cfg).Valid { parameters cfg with K := M } :=
  prepared_valid (hv.withLoss hKM hMs)

end Model
end

end Submission.Obl.k4_narrow_projected_row_parents
