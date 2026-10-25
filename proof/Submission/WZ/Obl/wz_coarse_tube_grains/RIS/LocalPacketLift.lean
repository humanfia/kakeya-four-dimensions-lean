-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPacketLift.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPacketData
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SelectedShading

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set
open scoped Classical

/-- Restore the ambient fine indices after constructing a local family on
one selected local cell. Geometry and both density exponents are unchanged. -/
noncomputable def LocalPrismPacket.lift {δ r ρ c ε : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {p₀ y w : V} (Q : Finset (Fin n))
    (hzero : ∀ i, i ∉ Q → Y i = ∅)
    (R : LocalPrismPacket δ r ρ c ε (x ∘ SelectedShading.enum Q)
      (v ∘ SelectedShading.enum Q) (Y ∘ SelectedShading.enum Q) p₀ y w) :
    LocalPrismPacket δ r ρ c ε x v Y p₀ y w where
  level := R.level
  centers := R.centers
  frame := R.frame
  shading := SelectedShading.lift Q R.shading
  pieces := R.pieces
  aligned := R.aligned
  refines := SelectedShading.lift_refines Q Y R.shading R.refines
  disjoint := R.disjoint
  piece_data := R.piece_data
  union_eq := R.union_eq.trans (SelectedShading.union_lift Q R.shading).symm
  retains := by
    rw [SelectedShading.sum_lift]
    have hs := SelectedShading.sum_enum μ Q Y hzero
    simpa only [Function.comp_apply, hs] using R.retains
  density := R.density
  crossing := by
    intro i l hl hmeet
    obtain ⟨a, ha, _⟩ := SelectedShading.lift_nonempty Q R.shading
      (hmeet.mono inter_subset_left)
    subst i
    rw [SelectedShading.lift_enum] at hmeet ⊢
    exact R.crossing a l hl hmeet
  uniform := by
    intro p hp
    rw [SelectedShading.union_lift] at hp
    simpa only [SelectedShading.card_lift] using R.uniform p hp

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
