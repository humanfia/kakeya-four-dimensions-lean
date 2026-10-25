-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)

noncomputable section

/-- Finite real shading weights and their aggregate lower bound, extracted
from the frozen grain witnesses. -/
theorem grain_real_weights {δ h ρ a c b g : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m) :
    (∀ j, μ (Hg j) ≠ ⊤) ∧
      (∀ j, 0 ≤ (μ (Hg j)).toReal ∧ (μ (Hg j)).toReal ≤ a * (ρ * c) * c) ∧
      δ ^ h * L * (a * (ρ * c) * c) ≤ ∑ j, (μ (Hg j)).toReal := by
  obtain ⟨hda, hab, hbc, _, hgeom, _, _, hmass, _⟩ := hG
  have ha : 0 ≤ a := hδ.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  have hv : 0 ≤ a * (ρ * c) * c := by positivity
  have hupper : ∀ j, μ (Hg j) ≤ O (a * (ρ * c) * c) := by
    intro j
    exact (measure_mono (hgeom j).2.1).trans_eq (frozen_prism_volume ha hrc hc (z j) (e j))
  have hfin : ∀ j, μ (Hg j) ≠ ⊤ :=
    fun j => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper j)
  refine ⟨hfin, ?_, ?_⟩
  · intro j
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    simpa only [O, ENNReal.toReal_ofReal hv] using ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper j)
  · have ht : (∑ j, μ (Hg j)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
    have hh := ENNReal.toReal_mono ht hmass
    rw [ENNReal.toReal_sum (fun j _ => hfin j),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ h * L * a * (ρ * c) * c)] at hh
    nlinarith

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
