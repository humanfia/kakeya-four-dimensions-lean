-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Basic

/-!
# Named versions of the frozen predicates of o173

Ported from x0418's `Defs.lean` on o152's branches (namespace renamed; only the predicates
o173 needs are kept). Every definition below is a literal transcription of the corresponding
`fun`-binder of the frozen statement of `WangZahlLot.wz_move_two_fibre_multiplicity_gain`
(with `V = Space`, `μ = volume`, `ι = fun p i => p i`, `M = MeasurableSet`); the main file
checks that the frozen statement follows from the named one.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube := WangZahlLot.Obl.wz_tower_balanced_refinement.Tube
abbrev ConvexCount := WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount
abbrev SlabCount := WangZahlLot.Obl.wz_tower_balanced_refinement.SlabCount
abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible

/-- `X`: an essentially distinct family. -/
abbrev Distinct (d : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
    1 / 2 * volume (Tube d (x i) (v i))

/-- `C d h n x v Y S Z ρ N y w f True`. -/
def Cover (d h : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y w : Fin N → Space) (f : Fin n → Fin N) : Prop :=
  (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
  ENNReal.ofReal (d ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S, volume (Z i) ∧
  (∀ k, ‖w k‖ = 1) ∧
  (∀ i ∈ S, Tube d (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) ∧
  SlabCount ρ (d ^ (-h)) N y w ∧
  True ∧
  (∀ k k', (Set.ncard {i | i ∈ S ∧ f i = k} : ℝ) ≤
    d ^ (-h) * (Set.ncard {i | i ∈ S ∧ f i = k'} : ℝ)) ∧
  Distinct ρ N y w ∧
  ∀ i ∈ S, (Set.ncard {k | Tube d (x i) (v i) ⊆ Tube ρ (y k) (w k)} : ℝ) ≤ d ^ (-h)

/-- The volume gain alternative. -/
def Gain (σ ω α κ δ : ℝ) (n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
