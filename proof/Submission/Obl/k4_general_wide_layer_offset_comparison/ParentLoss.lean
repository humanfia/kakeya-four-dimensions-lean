import Submission.Obl.k4_general_wide_layer_offset_comparison.Model

-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/ParentLoss.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Increase the permitted subpower loss while retaining every original
measure, polynomial, assignment and incidence. -/
def withLoss (M : ℕ → ℝ) : Parent α := { p with K := M }

theorem basic_withLoss (hp : p.Basic) {M : ℕ → ℝ}
    (hK : ∀ k, 0 < p.K k) (hKM : ∀ k, p.K k ≤ M k) : (p.withLoss M).Basic := by
  dsimp only [Submission.Obl.k4_critical_intercept_concentration.Data.Basic, withLoss]
  intro k
  obtain ⟨hb, hν, hπ, hμ, hρ, hsupp, hmass, hP, hclip, hnative⟩ := hp k
  have hinv : (M k)⁻¹ ≤ (p.K k)⁻¹ := inv_anti₀ (hK k) (hKM k)
  refine ⟨hb, hν, hπ, hμ.trans ?_, hρ, hsupp,
    (ENNReal.ofReal_le_ofReal hinv).trans hmass, hP, ?_, ?_⟩
  · gcongr
    exact hKM k
  · exact hclip.mono (fun _ hl => hl.trans (hKM k))
  · filter_upwards [hnative] with ω hω
    refine ⟨fun t ht => ?_, hinv.trans hω.2⟩
    exact ⟨(hω.1 t ht).1.trans (hKM k), (hω.1 t ht).2.1.trans (hKM k),
      (hω.1 t ht).2.2.trans (hKM k)⟩

theorem atDepth_withLoss {k : ℕ} {s R : ℝ} (hat : p.AtDepth k s R)
    (hN : 0 < p.N k) (hK : 0 < p.K k) {M : ℕ → ℝ} (hKM : p.K k ≤ M k) :
    (p.withLoss M).AtDepth k s R := by
  dsimp only [AtDepth, withLoss]
  obtain ⟨hTlo, hThi, hsets, hdisj, hlabels, hcover, hpal⟩ := hat
  have hinv : (M k)⁻¹ ≤ (p.K k)⁻¹ := inv_anti₀ hK hKM
  have hq : 0 < (2 : ℝ) ^ (-(p.T k s : ℤ)) := by positivity
  have ha : 0 < p.N k ^ (-s) := by positivity
  have hg : 0 < p.N k ^ (-p.ℓ * s) := by positivity
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
    · filter_upwards [hderiv] with ω hω hl ht
      exact hinv.trans (hω hl ht)
  · intro i v v₀ hv hvR
    apply (hpal i v v₀ hv hvR).trans
    gcongr

theorem caps_withLoss (hp : p.Caps) {M : ℕ → ℝ}
    (hN : ∀ k, 0 < p.N k) (hKM : ∀ k, p.K k ≤ M k) : (p.withLoss M).Caps := by
  dsimp only [Submission.Obl.k4_critical_intercept_concentration.Data.Caps, withLoss]
  intro R hR
  filter_upwards [hp R hR] with k hk
  intro r s v hr hrR hs hsR hv hvR
  have hNk := hN k
  obtain ⟨hpal, hpure, hjoint⟩ := hk r s v hr hrR hs hsR hv hvR
  refine ⟨fun j => (hpal j).trans ?_, fun h q j => (hpure h q j).trans ?_,
    fun h q j v₀ => (hjoint h q j v₀).trans ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKM k) (by positivity))
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKM k) (by positivity))
  · exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hKM k) (by positivity))) le_rfl

/-- All general prepared-parent hypotheses survive a larger subpower
loss. In particular one may absorb the projected preparation loss before
using the native stable-sheet kernel. -/
theorem Valid.withLoss {p : Parent α} (hp : p.Valid) {M : ℕ → ℝ}
    (hKM : ∀ k, p.K k ≤ M k)
    (hMs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    (p.withLoss M).Valid := by
  have hK : ∀ k, 0 < p.K k := fun k => zero_lt_one.trans_le (hp.subpower.1 k)
  have hN : ∀ k, 0 < p.N k := fun k => by linarith [hp.scale k]
  refine { hp with
    subpower := ⟨fun k => (hp.subpower.1 k).trans (hKM k), hMs⟩
    basic := p.basic_withLoss hp.basic hK hKM
    caps := p.caps_withLoss hp.caps hN hKM
    prepared := ?_ }
  intro R hR
  filter_upwards [hp.prepared R hR] with k hk s hs hsU
  exact p.atDepth_withLoss (hk s hs hsU) (hN k) (hK k) (hKM k)

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
