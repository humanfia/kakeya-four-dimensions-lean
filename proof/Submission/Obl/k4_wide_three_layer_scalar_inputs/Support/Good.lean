import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Blocks

set_option linter.unusedVariables false

/-!
# Good incidences of a compared block

Almost every incidence of the law of a compared block lies in the block, satisfies both fits,
has its chart equal to the chart of its coarse predictor, and its coarse predictor and offsets
in the chosen per-chart lists.  On such incidences the normalized coordinates and the velocity
are bounded by the block geometry.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H : ℝ}

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H)

/-- The frame of the compared block. -/
def frame : Frame := blockFrame cfg k s CB.i CB.L

/-- The original chart of an incidence. -/
def chart (_CB : ComparedBlock cfg k s u v χ H) (p : α × ℝ) : ℤ × ℤ :=
  (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋)

/-- The chosen per-chart lists. -/
def G (ch : ℤ × ℤ) : Finset CB.Γ := Classical.choose (CB.coarse_list ch.1 ch.2)

def F1 (ch : ℤ × ℤ) (γ : CB.Γ) : Finset ℤ := Classical.choose (CB.offset1_list ch.1 ch.2 γ)

def F2 (ch : ℤ × ℤ) (γ : CB.Γ) : Finset ℤ := Classical.choose (CB.offset2_list ch.1 ch.2 γ)

theorem G_card (ch : ℤ × ℤ) : ((CB.G ch).card : ℝ) ≤ H :=
  (Classical.choose_spec (CB.coarse_list ch.1 ch.2)).1

theorem F1_card (ch : ℤ × ℤ) (γ : CB.Γ) : ((CB.F1 ch γ).card : ℝ) ≤ H * cfg.N k ^ (cfg.d * u) :=
  (Classical.choose_spec (CB.offset1_list ch.1 ch.2 γ)).1

theorem F2_card (ch : ℤ × ℤ) (γ : CB.Γ) : ((CB.F2 ch γ).card : ℝ) ≤ H * cfg.N k ^ (cfg.d * v) :=
  (Classical.choose_spec (CB.offset2_list ch.1 ch.2 γ)).1

/-- A good incidence. -/
structure Good (p : α × ℝ) : Prop where
  B : p.1 ∈ cfg.B k s CB.i
  I : p.2 ∈ Data.I (cfg.T k s) (cfg.j k s CB.i)
  fit1 : |CB.frame.resid (cfg.b k p.1) p.2 -
      quadZ (CB.pc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) -
      CB.D1 (CB.lab p.1) -
      transv (CB.tc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)
        (CB.frame.tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-u)
  fit2 : |CB.frame.resid (cfg.b k p.1) p.2 -
      quadZ (CB.pc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) -
      CB.D2 (CB.lab p.1) -
      transv (CB.tc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)
        (CB.frame.tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-v)
  chart : CB.chart p = CB.chartOf (CB.crs (CB.lab p.1))
  coarse : CB.crs (CB.lab p.1) ∈ CB.G (CB.chart p)
  off1 : ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ ∈ CB.F1 (CB.chart p) (CB.crs (CB.lab p.1))
  off2 : ⌊CB.D2 (CB.lab p.1) / cfg.N k ^ (-v)⌋ ∈ CB.F2 (CB.chart p) (CB.crs (CB.lab p.1))

theorem ae_good : ∀ᵐ p ∂CB.lam, CB.Good p := by
  have hG : ∀ᵐ p ∂CB.lam, CB.crs (CB.lab p.1) ∈ CB.G (CB.chart p) := by
    have h : ∀ ch : ℤ × ℤ, ∀ᵐ p ∂CB.lam, CB.chart p = ch → CB.crs (CB.lab p.1) ∈ CB.G ch := by
      intro ch
      filter_upwards [(Classical.choose_spec (CB.coarse_list ch.1 ch.2)).2] with p hp hch
      simp only [chart, Prod.ext_iff] at hch
      exact hp hch.1 hch.2
    rw [← ae_all_iff] at h
    filter_upwards [h] with p hp using hp _ rfl
  have hF1 : ∀ᵐ p ∂CB.lam, ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ ∈
      CB.F1 (CB.chart p) (CB.crs (CB.lab p.1)) := by
    have h : ∀ ch : ℤ × ℤ, ∀ γ : CB.Γ, ∀ᵐ p ∂CB.lam, CB.chart p = ch → CB.crs (CB.lab p.1) = γ →
        ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ ∈ CB.F1 ch γ := by
      intro ch γ
      filter_upwards [(Classical.choose_spec (CB.offset1_list ch.1 ch.2 γ)).2] with p hp hch hγ
      simp only [chart, Prod.ext_iff] at hch
      exact hp hch.1 hch.2 hγ
    have h' : ∀ᵐ p ∂CB.lam, ∀ ch : ℤ × ℤ, ∀ γ : CB.Γ, CB.chart p = ch → CB.crs (CB.lab p.1) = γ →
        ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ ∈ CB.F1 ch γ := by
      rw [ae_all_iff]; intro ch; rw [ae_all_iff]; exact h ch
    filter_upwards [h'] with p hp using hp _ _ rfl rfl
  have hF2 : ∀ᵐ p ∂CB.lam, ⌊CB.D2 (CB.lab p.1) / cfg.N k ^ (-v)⌋ ∈
      CB.F2 (CB.chart p) (CB.crs (CB.lab p.1)) := by
    have h : ∀ ch : ℤ × ℤ, ∀ γ : CB.Γ, ∀ᵐ p ∂CB.lam, CB.chart p = ch → CB.crs (CB.lab p.1) = γ →
        ⌊CB.D2 (CB.lab p.1) / cfg.N k ^ (-v)⌋ ∈ CB.F2 ch γ := by
      intro ch γ
      filter_upwards [(Classical.choose_spec (CB.offset2_list ch.1 ch.2 γ)).2] with p hp hch hγ
      simp only [chart, Prod.ext_iff] at hch
      exact hp hch.1 hch.2 hγ
    have h' : ∀ᵐ p ∂CB.lam, ∀ ch : ℤ × ℤ, ∀ γ : CB.Γ, CB.chart p = ch → CB.crs (CB.lab p.1) = γ →
        ⌊CB.D2 (CB.lab p.1) / cfg.N k ^ (-v)⌋ ∈ CB.F2 ch γ := by
      rw [ae_all_iff]; intro ch; rw [ae_all_iff]; exact h ch
    filter_upwards [h'] with p hp using hp _ _ rfl rfl
  filter_upwards [CB.lam_supp, CB.fit1, CB.fit2, CB.chart_ae, hG, hF1, hF2] with p hs h1 h2 hc hG hF1 hF2
  refine ⟨hs.1, ?_, h1, h2, hc, hG, hF1, hF2⟩
  have := hs.2
  simp only [Data.I, mem_Icc] at this ⊢
  constructor
  · exact this.1
  · have e : (((cfg.j k s CB.i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ cfg.T k s =
        ((cfg.j k s CB.i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹ := by
      field_simp
    rw [e]; exact this.2

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
