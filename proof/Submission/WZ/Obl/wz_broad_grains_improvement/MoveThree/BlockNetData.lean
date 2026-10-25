-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockNetData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockNetData.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockFirstFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FillingNetFamily

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (prism cTube netConst)

noncomputable section
namespace BlockFirstFilling

variable {ω ζ δ ε b ρ c β τ lam den k : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}

abbrev map (F : BlockFirstFilling A lam den k hk) (l : Fin A.labels.card) : V ≃ᵃ[ℝ] V :=
  (F.affine l).trans (uniformMap hk).toAffineEquiv

def radius (_F : BlockFirstFilling A lam den k hk) : ℝ := 256 * k * (2 * ρ) / A.packetShort

def volumeFactor (_F : BlockFirstFilling A lam den k hk) : ℝ :=
  k ^ 3 / (4 * A.packetShort * A.packetMiddle)

theorem map_volume (F : BlockFirstFilling A lam den k hk) (l : Fin A.labels.card) (Q : Set V) :
    μ (F.map l '' Q) = O F.volumeFactor * μ Q :=
  contracted_flat_normalization_volume hk (F.affine l) (F.jacobian l) Q

theorem radius_pos (F : BlockFirstFilling A lam den k hk) (hδ : 0 < δ) (hR : R.Nonempty) :
    0 < F.radius := by
  have hρ := (D.dimensions hδ).2.1
  have ha := (A.packet_dimensions hδ hR).1
  unfold radius
  positivity

theorem volumeFactor_pos (F : BlockFirstFilling A lam den k hk)
    (hδ : 0 < δ) (hR : R.Nonempty) : 0 < F.volumeFactor := by
  obtain ⟨ha, _, hab, _⟩ := A.packet_dimensions hδ hR
  have hb := ha.trans_le hab
  unfold volumeFactor
  positivity

theorem good_nonempty (F : BlockFirstFilling A lam den k hk)
    (hδ : 0 < δ) (hR : R.Nonempty) (hlam : 0 < lam) : F.good.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hcount := F.count
  rw [he, Finset.sum_empty] at hcount
  have hc : (0 : ℝ) < R.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hR)
  have hh : 0 < (lam * δ ^ (τ + 21 * ε / 40) / 16) * R.card := by positivity
  linarith

theorem radius_small (F : BlockFirstFilling A lam den k hk)
    (hδ : 0 < δ) (hR : R.Nonempty) (hlam : 0 < lam) : F.radius ≤ 1 / 1000000 := by
  obtain ⟨l, hl⟩ := F.good_nonempty hδ hR hlam
  exact (F.filling l hl).2.2.1

end BlockFirstFilling

/-- Balanced carrier nets of the actual first fillings. The low-cardinality
estimate keeps its concentration gain and the common affine volume factor. -/
structure BlockNetData {σ ω ζ δ ε b ρ c β τ lam den k : ℝ} {p n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    {A : BlockAngularData D R G β τ} {hk : 0 < k}
    (F : BlockFirstFilling A lam den k hk) (Cnet e Λ Kc : ℝ) (d : ℕ) where
  N : Fin A.labels.card → ℕ
  size : Fin A.labels.card → ℕ
  representative : ∀ l, Fin (N l) → Fin R.card
  fibre : ∀ l, Fin (N l) → Finset (Fin R.card)
  net : ∀ l ∈ F.good, 0 < N l ∧ 0 < size l ∧
    (∀ j, representative l j ∈ F.indices l) ∧ (∀ j, fibre l j ⊆ F.indices l) ∧
    (∀ j, (fibre l j).card = size l) ∧
    (∀ j j', j ≠ j' → Disjoint (fibre l j) (fibre l j')) ∧
    netConst * ((F.indices l).card : ℝ) ≤ (d : ℝ) * Λ * N l * size l ∧
    (∀ j, ∀ i ∈ fibre l j, F.map l '' D.normalizedBody R G.affine i ⊆
      cTube F.radius (F.map l (A.start (representative l j) +
        (1 / 2 : ℝ) • A.axis (representative l j))) (F.direction l (representative l j))) ∧
    (∀ j j', j ≠ j' →
      μ (cTube F.radius (F.map l (A.start (representative l j) +
          (1 / 2 : ℝ) • A.axis (representative l j))) (F.direction l (representative l j)) ∩
        cTube F.radius (F.map l (A.start (representative l j') +
          (1 / 2 : ℝ) • A.axis (representative l j'))) (F.direction l (representative l j'))) ≤
        (1 / 2 : ENNReal) * μ (cTube F.radius (F.map l (A.start (representative l j) +
          (1 / 2 : ℝ) • A.axis (representative l j))) (F.direction l (representative l j))))
  low_sum : let M := grainCoefficient D.a ρ c D.z D.e D.Q
    let low := F.good.filter fun l => (size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)) ≤
      M * (4 * F.radius) ^ 2 / Kc
    (∑ l ∈ low, O (lowQCoeff Cnet δ e F.radius ω σ (F.volumeFactor * (ρ ^ 2 / 64)) M Λ d *
        Kc ^ (σ / 2) * (F.indices l).card)) ≤
      O F.volumeFactor * ∑ l ∈ low, μ (⋃ i, A.normalizedPiece l i)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
