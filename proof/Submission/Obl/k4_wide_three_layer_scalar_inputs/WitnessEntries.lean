import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses
import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyEntryTools
import Submission.Obl.k4_wide_three_layer_scalar_inputs.RawShortBudget

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core Inherited.MatchGML2D

noncomputable section

open scoped Classical

variable {α : Type} [MeasurableSpace α] (W : Context α)

def depth (h : Fin 3) : ℝ := ![W.s, W.s + W.u, W.s + W.v] h
def width (h : Fin 3) : ℝ := W.cfg.N W.k ^ (-W.depth h)
def reference (h : Fin 3) (key : Fin 3 → ℤ) : ℝ :=
  keyRef W.cfg.comparisonData W.k W.χ W.m W.q (W.width h) key
def tolerance (h : Fin 3) : ℝ :=
  rawSheetError (W.cfg.N W.k ^ W.ε) W.q (W.width h) W.D W.χ W.ζ

abbrev HeavyPiece (h : Fin 3) (key : Fin 3 → ℤ) :=
  {j : Fin (W.layers.np h) // pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁
    h j (W.cfg.j W.k W.s W.i) key}

def entryLabels (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) : Set α :=
  pieceLab W.cfg.comparisonData W.k W.s W.datum W.m h j.1 (W.cfg.j W.k W.s W.i) key

def entryGraph (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) : Fin 6 → ℝ :=
  sheetKeyCoeff (W.layers.G h j.1) (W.width h) W.χ W.m W.q W.t₀ key

theorem entryLabels_measurable (hb : Measurable (W.cfg.b W.k))
    (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) :
    MeasurableSet (W.entryLabels h key j) :=
  (W.layers.meas h j.1).inter (measurableSet_slotKey hb _ _ _ _)

theorem entryLabels_disjoint (h : Fin 3) (key : Fin 3 → ℤ)
    (j j' : W.HeavyPiece h key) (hne : j ≠ j') :
    Disjoint (W.entryLabels h key j) (W.entryLabels h key j') :=
  Disjoint.mono inter_subset_left inter_subset_left
    (W.layers.disj h j.1 j'.1 (fun heq => hne (Subtype.ext heq)))

theorem entry_floor (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) :
    ENNReal.ofReal (W.reference h key / W.K₁) ≤
      W.layers.ρs (W.entryLabels h key j ×ˢ Icc W.t₀ (W.t₀ + W.q)) := by
  have hj := j.2.1
  rw [I_eq_slot W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)] at hj
  exact hj

theorem entry_graph {Xb : ℝ} (hN : 0 < W.cfg.N W.k) (hχ : 0 < W.χ) (hD : 0 < W.D)
    (hXb : 2 * W.cfg.N W.k ^ W.ε ≤ Xb)
    (hdrift : W.ζ + W.χ ≤ W.D / 4) (hsmall : W.q * (W.ζ + W.χ) ≤ 4 * W.D)
    (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) :
    ∀ l ∈ W.entryLabels h key j, |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ →
      slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = key ∧
      ∀ τ ∈ Icc (0 : ℝ) 1,
        |W.cfg.b W.k l 2 + (W.t₀ + W.q * τ) * W.cfg.b W.k l 5| ≤ Xb ∧
        |W.cfg.b W.k l 2 + (W.t₀ + W.q * τ) * W.cfg.b W.k l 5 -
          W.width h * quad2 (W.entryGraph h key j) τ (sliceY (W.cfg.b W.k) W.m W.t₀ l)| ≤
            W.width h * W.tolerance h := by
  have hm : 0 < W.m := mul_pos (slotLen_pos W.cfg.comparisonData W.k W.s)
    (Real.rpow_pos_of_pos hN _)
  exact piece_lab_graph W.cfg.comparisonData W.k W.s W.datum hχ hD hm
    (Real.rpow_pos_of_pos hN _) hXb hdrift hsmall h j.1 (W.cfg.j W.k W.s W.i) key

theorem entry_coefficients {B : ℝ} (hN : 0 < W.cfg.N W.k) (hχ : 0 < W.χ) (hD : 0 < W.D)
    (hdrift : W.ζ + W.χ ≤ W.D / 4)
    (hsmall : 4 * W.m + W.q * (W.ζ + W.χ) ≤ 4 * W.D)
    (hnull : W.layers.ρs (horizSet (W.cfg.b W.k) W.ζ)ᶜ = 0)
    (h : Fin 3) (hB : 8 * (11 * (160 * W.cfg.N W.k ^ W.ε) / W.width h) ≤ B)
    (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) :
    ∀ e, |W.entryGraph h key j e| ≤ B := by
  have hm : 0 < W.m := mul_pos (slotLen_pos W.cfg.comparisonData W.k W.s)
    (Real.rpow_pos_of_pos hN _)
  obtain ⟨l, hl, hh⟩ := shortBound_exists_horiz hnull j.2.2
  exact sheet_entry_coefficients W.cfg.comparisonData W.k W.s W.datum hχ hD hm hdrift
    hsmall (Real.rpow_pos_of_pos hN _) h j.1 (W.cfg.j W.k W.s W.i) key hl hh hB

theorem entry_reference_pos [IsFiniteMeasure (W.cfg.π W.k)]
    {r sp vp : ℝ} (hχ : W.χ = W.cfg.N W.k ^ (-vp))
    (hcap : JointCapAt (W.cfg.μ W.k) (W.cfg.π W.k) (W.cfg.b W.k)
      (W.cfg.N W.k) (W.cfg.K W.k) W.cfg.d r sp vp)
    (hρμ : W.layers.ρs ≤ W.cfg.μ W.k) (hN : 0 < W.cfg.N W.k)
    (h : Fin 3) (key : Fin 3 → ℤ) (j : W.HeavyPiece h key) :
    0 < W.reference h key := by
  have hm : 0 < W.m := mul_pos (slotLen_pos W.cfg.comparisonData W.k W.s)
    (Real.rpow_pos_of_pos hN _)
  have hpos := j.2.2
  rw [I_eq_slot W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)] at hpos
  have hp := occupied_key_palette_pos hcap hρμ (W.entryLabels h key j)
    (by
      intro l hl
      have hk : slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = key := hl.2
      simpa only [← hχ, t₀] using hk) hpos
  unfold reference keyRef
  rw [hχ]
  exact mul_pos (mul_pos (mul_pos (mul_pos (slotLen_pos _ _ _)
    (Real.rpow_pos_of_pos hN _)) hm)
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _)) hp

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
