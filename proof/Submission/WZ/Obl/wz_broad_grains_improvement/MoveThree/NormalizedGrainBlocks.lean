-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NormalizedGrainBlocks.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NormalizedGrainBlocks.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PackedBodies
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.UpperBodies
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RoundBlockEnclosure

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyGeometry BodyConvexCount BodyPacking)
open WangZahlLot.Obl.wz_separated_cover_refinement
  (enumerate enumerate_mem enumerate_injective)

noncomputable section
namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

abbrev normalizedBody (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (R : Finset (Fin D.L)) (f : V ≃ᵃ[ℝ] V) : Fin R.card → Set V :=
  fun i => f '' P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i))

abbrev normalizedShade (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (R : Finset (Fin D.L)) (f : V ≃ᵃ[ℝ] V) : Fin R.card → Set V :=
  fun i => f '' D.Hg (enumerate R i)

/-- A saturated block in its natural coordinates, including all source
hypotheses for a further normalization and the body estimate. -/
structure NormalizedBlock (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (R : Finset (Fin D.L)) where
  affine : V ≃ᵃ[ℝ] V
  short : ℝ
  middle : ℝ
  center : V
  frame : V ≃ₗᵢ[ℝ] V
  short_pos : 0 < short
  ordered : short ≤ middle
  middle_le : middle ≤ 4
  jacobian : ∀ W, μ (affine '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W
  forward_lipschitz : ∀ p q, dist (affine p) (affine q) ≤ (ρ / (4 * D.a)) * dist p q
  natural_anchor : Fin D.L
  natural_near : ∀ i, grainNear D.a ρ c D.z D.e natural_anchor (enumerate R i)
  inverse_lipschitz : ∀ p q, dist p q / (4 * c) ≤ dist (affine p) (affine q)
  coordinates : ∀ q i, affine q i =
    (![ρ / (4 * D.a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
      D.e natural_anchor (q - D.z natural_anchor) i
  unit_ball : ∀ i, D.normalizedBody R affine i ⊆ ball (0 : V) 1
  geometry : BodyGeometry (D.normalizedBody R affine)
    (fun i => affine (D.z (enumerate R i))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64)
  round : ∀ i, ball (affine (D.z (enumerate R i))) (ρ / 100) ⊆ D.normalizedBody R affine i
  long : ∀ i, ∃ q ∈ D.normalizedBody R affine i,
    ∃ q' ∈ D.normalizedBody R affine i, (1 / 4 : ℝ) ≤ dist q q'
  body_volume : ∀ i, μ (D.normalizedBody R affine i) = O (ρ ^ 2 / 64)
  measurable : ∀ i, MeasurableSet (D.normalizedShade R affine i)
  contained : ∀ i, D.normalizedShade R affine i ⊆ D.normalizedBody R affine i
  dense : ∀ i, O (δ ^ (21 * ε / 40)) * μ (D.normalizedBody R affine i) ≤
    μ (D.normalizedShade R affine i)
  convex_count : BodyConvexCount (D.normalizedBody R affine) (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q)
  packing : BodyPacking (D.normalizedBody R affine) (ρ ^ 2 / 64)
    (grainPackingCoefficient δ ε)
  enclosure : ∀ i, D.normalizedBody R affine i ⊆ P short middle 4 center frame
  saturated : grainCoefficient D.a ρ c D.z D.e D.Q * (4 * short * middle) ≤
    (110592 * (2 : ℝ) ^ p) * R.card * (ρ ^ 2 / 64)

/-- Stable local concentration provides disjoint saturated normalized
blocks covering at least half of the selected grain indices. -/
theorem normalized_saturated_blocks (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) :
    ∃ F : Finset (Finset (Fin D.L)),
      (∀ R ∈ F, R.Nonempty ∧ R ⊆ D.Q ∧ Nonempty (NormalizedBlock D R)) ∧
      (↑F : Set (Finset (Fin D.L))).PairwiseDisjoint id ∧
      (D.Q.card : ℝ) ≤ 2 * (F.biUnion id).card := by
  classical
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  let U := fun j => P D.a (ρ * c) c (D.z j) (D.e j)
  let w := D.a * (ρ * c) * c
  let M := grainCoefficient D.a ρ c D.z D.e D.Q
  have hw : 0 < w := by dsimp [w]; positivity
  have hM : 0 < M := by
    have hh := D.above_stability
    change 2 * (2 : ℝ) ^ p < M at hh
    exact (by positivity : 0 < 2 * (2 : ℝ) ^ p).trans hh
  have hv j : μ (U j) = O w := frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le _ _
  obtain ⟨F, hF, hdisj, hcard⟩ := localCoefficient_dense_blocks U
    (grainNear D.a ρ c D.z D.e) D.Q hw (by positivity : 0 < (2 : ℝ) ^ p)
    (fun j _ => (hv j).ge) D.above_stability D.stable
  refine ⟨F, ?_, hdisj, hcard⟩
  intro R hR
  obtain ⟨hRne, hRQ, j₀, hj₀, W, hW, hWfin, hcover, hsat, hupper⟩ := hF R hR
  change M / (2 * (2 : ℝ) ^ p) * (μ W).toReal < (R.card : ℝ) * w at hsat
  change WangZahlLot.Obl.wz_concentrated_convex_factorization.Upper U w R M at hupper
  have hι i : enumerate R i ∈ D.Q := hRQ (enumerate_mem R i)
  have hnear i : grainNear D.a ρ c D.z D.e j₀ (enumerate R i) :=
    (hcover _ (enumerate_mem R i)).1
  obtain ⟨f, hvol, hgeom, hmeas, hsub, hdense, hround, hlong, hLip, hdist, hcoord, hunit⟩ :=
    D.normalized_bodies_exact hδ (enumerate R) j₀ hι hnear
  have hpack := D.selected_image_packing hδ (enumerate R) (enumerate_injective R)
    hι f hvol hround hlong
  let J := ρ / (64 * D.a * c ^ 2)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJw : J * w = ρ ^ 2 / 64 := by dsimp [J, w]; field_simp
  have hJvol : ∀ W', μ (f '' W') = O J * μ W' := hvol
  have hbodyvol i : μ (D.normalizedBody R f i) = O (ρ ^ 2 / 64) := by
    change μ (f '' U (enumerate R i)) = _
    rw [hJvol, hv, ← ENNReal.ofReal_mul hJ.le, hJw]
  have hcount : BodyConvexCount (D.normalizedBody R f) (ρ ^ 2 / 64) M := by
    have hh := upper_enumerate_affine_body_count hw.le hJ f hJvol hupper
    rw [hJw] at hh
    exact hh
  have hfin : μ (f '' W) ≠ ⊤ := by rw [hJvol]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin
  have hcontain i : D.normalizedBody R f i ⊆ f '' W :=
    image_mono (hcover _ (enumerate_mem R i)).2
  obtain ⟨A, B, z₀, E, hA, hAB, hB, hbox, hboxvol⟩ := normalized_block_enclosure
    (Finset.card_pos.mpr hRne) (D.normalizedBody R f) (fun i => f (D.z (enumerate R i)))
    (by positivity : 0 < ρ / 100) hround hgeom.bounded hlong
    (hW.affine_image f.toAffineMap) hfin hcontain
  have hsat' : M / (2 * (2 : ℝ) ^ p) * (μ (f '' W)).toReal <
      (R.card : ℝ) * (ρ ^ 2 / 64) := by
    rw [hJvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ.le]
    rw [← hJw]
    have hh := mul_lt_mul_of_pos_left hsat hJ
    convert hh using 1 <;> ring
  have hscalar : M * (4 * A * B) ≤ (110592 * (2 : ℝ) ^ p) * R.card * (ρ ^ 2 / 64) := by
    have hs := (div_lt_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ p)).mp
      (show (M * (μ (f '' W)).toReal) / (2 * (2 : ℝ) ^ p) <
        (R.card : ℝ) * (ρ ^ 2 / 64) by simpa only [div_mul_eq_mul_div] using hsat')
    change 4 * A * B ≤ 55296 * (μ (f '' W)).toReal at hboxvol
    have hh := mul_le_mul_of_nonneg_left hboxvol hM.le
    nlinarith only [hs, hh]
  exact ⟨hRne, hRQ, ⟨⟨f, A, B, z₀, E, hA, hAB, hB, hvol, hLip, j₀, hnear, hdist, hcoord, hunit, hgeom,
    hround, hlong, hbodyvol, hmeas, hsub, hdense, hcount, hpack, hbox, hscalar⟩⟩⟩

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
