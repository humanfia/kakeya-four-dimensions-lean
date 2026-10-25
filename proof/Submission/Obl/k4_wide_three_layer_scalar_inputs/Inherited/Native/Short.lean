/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit 525ce8d3c8ed1d02854b5f6c797e220d2ac13ddd, file Submission/Obl/k4_horizontal_wide_interval_return/Native/Short.lean.
Namespace/imports renamed; velocity nullness dependency minimized. Earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortDefs

set_option autoImplicit false

/-!
# The short comparison at one index

Over the slot keys of a finite key box `KB`, the light block entries, the light piece entries of
the three layers, and the incidences of heavy (block, layer-0 piece) pairs whose key graphs differ
by `Mst` in some coefficient form `shortBad`.  Its mass is bounded by the reference sums divided
by `K₁` and by the matching bound (`short_bad_le`); off it, every incidence of a block and of
pieces has heavy entries and close key graphs (`short_good`).
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

section

variable (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
  (L : LayerDatum cfg k ε R χ D depth) (m K₁ Mst : ℝ)

/-- A heavy block entry. -/
def blockHeavy (i : Fin (cfg.n k s)) (κ : Fin 3 → ℤ) : Prop :=
  Heavy L.ρs (blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i))
    (keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) K₁

/-- A heavy piece entry. -/
def pieceHeavy (h : Fin 3) (i : Fin (L.np h)) (jj : Fin (2 ^ cfg.T k s)) (κ : Fin 3 → ℤ) : Prop :=
  Heavy L.ρs (pieceLab cfg k s L m h i jj κ ×ˢ cfg.I (cfg.T k s) jj)
    (keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ) K₁

/-- A block and a layer-0 piece whose key graphs are far apart. -/
def pairBad (i : Fin (cfg.n k s)) (i₀ : Fin (L.np 0)) (κ : Fin 3 → ℤ) : Prop :=
  ∃ e, Mst ≤ |blockKeyCoeff (cfg.F k s i) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
      (slotStart cfg k s (cfg.j k s i)) κ e -
    sheetKeyCoeff (L.G 0 i₀) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
      (slotStart cfg k s (cfg.j k s i)) κ e|

/-- The bad incidences of the short comparison. -/
def shortBad (KB : Finset (Fin 3 → ℤ)) : Set (α × ℝ) :=
  (⋃ i, ⋃ κ ∈ KB, {p | p ∈ blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ∧
      ¬ blockHeavy cfg k s L m K₁ i κ}) ∪
  (⋃ h, ⋃ i, ⋃ jj, ⋃ κ ∈ KB, {p | p ∈ pieceLab cfg k s L m h i jj κ ×ˢ cfg.I (cfg.T k s) jj ∧
      ¬ pieceHeavy cfg k s L m K₁ h i jj κ}) ∪
  (⋃ i, ⋃ i₀, ⋃ κ ∈ KB, {p | p ∈ (blockLab cfg k s L m i κ ∩ pieceLab cfg k s L m 0 i₀
      (cfg.j k s i) κ) ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ∧ blockHeavy cfg k s L m K₁ i κ ∧
      pieceHeavy cfg k s L m K₁ 0 i₀ (cfg.j k s i) κ ∧ pairBad cfg k s L m Mst i i₀ κ})

/-- **Off the bad set, entries are heavy and graphs close.** -/
theorem short_good (KB : Finset (Fin 3 → ℤ)) {p : α × ℝ}
    (hp : p ∉ shortBad cfg k s L m K₁ Mst KB) (hpg : p.1 ∈ goodLab L)
    (i : Fin (cfg.n k s)) (hpB : p.1 ∈ cfg.B k s i)
    (hpI : p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i))
    (hKB : slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1 ∈ KB) :
    blockHeavy cfg k s L m K₁ i (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1) ∧
    (∀ h (ih : Fin (L.np h)), p.1 ∈ L.C h ih →
      pieceHeavy cfg k s L m K₁ h ih (cfg.j k s i)
        (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1)) ∧
    (∀ i₀, p.1 ∈ L.C 0 i₀ →
      ¬ pairBad cfg k s L m Mst i i₀
        (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1)) := by
  set κ := slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1 with hκ
  have hpBl : p ∈ blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) :=
    ⟨⟨⟨hpB, hpg⟩, hκ.symm⟩, hpI⟩
  have hbh : blockHeavy cfg k s L m K₁ i κ := by
    by_contra hc
    exact hp (Or.inl (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr ⟨κ, hKB, hpBl, hc⟩⟩)))
  have hph : ∀ h (ih : Fin (L.np h)), p.1 ∈ L.C h ih →
      pieceHeavy cfg k s L m K₁ h ih (cfg.j k s i) κ := by
    intro h ih hih
    by_contra hc
    have hmem : p ∈ pieceLab cfg k s L m h ih (cfg.j k s i) κ ×ˢ
        cfg.I (cfg.T k s) (cfg.j k s i) := ⟨⟨hih, hκ.symm⟩, hpI⟩
    exact hp (Or.inl (Or.inr (mem_iUnion.mpr ⟨h, mem_iUnion.mpr ⟨ih, mem_iUnion.mpr
      ⟨cfg.j k s i, mem_iUnion₂.mpr ⟨κ, hKB, hmem, hc⟩⟩⟩⟩)))
  refine ⟨hbh, hph, ?_⟩
  intro i₀ hi₀ hbad
  have hmem : p ∈ (blockLab cfg k s L m i κ ∩ pieceLab cfg k s L m 0 i₀ (cfg.j k s i) κ) ×ˢ
      cfg.I (cfg.T k s) (cfg.j k s i) := ⟨⟨hpBl.1, ⟨hi₀, hκ.symm⟩⟩, hpI⟩
  exact hp (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨i₀, mem_iUnion₂.mpr
    ⟨κ, hKB, hmem, hbh, hph 0 i₀ hi₀, hbad⟩⟩⟩))

end

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
