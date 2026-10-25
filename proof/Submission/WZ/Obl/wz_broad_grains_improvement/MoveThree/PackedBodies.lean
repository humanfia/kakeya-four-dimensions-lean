-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PackedBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PackedBodies.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedBodies
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PackingPowers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyGeometry BodyPacking)

noncomputable section
namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Common normalization supplies the geometry, density and independent
packing hypotheses needed for the convex-body estimate. -/
theorem normalized_packed_bodies (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (hιinj : Function.Injective ι)
    (j₀ : Fin D.L) (hι : ∀ j, ι j ∈ D.Q)
    (hnear : ∀ j, grainNear D.a ρ c D.z D.e j₀ (ι j)) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      BodyGeometry (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (fun j => f (D.z (ι j))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64) ∧
      (∀ j, MeasurableSet (f '' D.Hg (ι j))) ∧
      (∀ j, f '' D.Hg (ι j) ⊆ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, O (δ ^ (21 * ε / 40)) *
        μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ μ (f '' D.Hg (ι j))) ∧
      BodyPacking (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (ρ ^ 2 / 64) (grainPackingCoefficient δ ε) := by
  obtain ⟨f, hvol, hgeom, hm, hs, hd, hround, hlong⟩ :=
    D.normalized_bodies_round hδ ι j₀ hι hnear
  exact ⟨f, hvol, hgeom, hm, hs, hd,
    D.selected_image_packing hδ ι hιinj hι f hvol hround hlong⟩

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
