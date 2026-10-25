-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityUpper.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockDensityUpper.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedGrainBlocks
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AffinePrismDensity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section
namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

theorem grain_subset_ambient (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (j : Fin D.L) : D.Hg j ⊆ ⋃ i, Y i := by
  intro q hq
  have hh := (D.grains.2.2.2.2.2.2.1 (D.γ j)).subset ⟨j, rfl, hq⟩
  obtain ⟨i, hi, hf, hqi⟩ := hh
  exact mem_iUnion.mpr ⟨i, (D.cover.1 i).2.1 hqi⟩

/-- A global physical density cap bounds the density in every normalized
block, with the same short-scale power as the analytic lower bound. -/
theorem normalized_block_density_upper_at (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {s t : ℝ} (hs : 0 ≤ s)
    (hA : A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (hcap : ∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-t) * (δ / r) ^ s * r ^ 3))
    (R : Finset (Fin D.L)) (G : D.NormalizedBlock R)
    {scale : ℝ} (hscale : 0 < scale) (hscale_short : scale ≤ G.short) :
    μ (⋃ i, D.normalizedShade R G.affine i) ≤
      O (512 * (4 : ℝ) ^ s * δ ^ (-t) * (ρ / scale) ^ s * (4 * G.short * G.middle)) := by
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  have hshort := G.short_pos
  have hmid := G.short_pos.trans_le G.ordered
  let r := D.a * scale / (4 * ρ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by positivity : 0 < 4 * ρ)).mpr
    have hh := mul_le_mul_of_nonneg_right D.grains.2.1 hscale.le
    have hsc : c * scale ≤ 4 :=
      (mul_le_mul_of_nonneg_right hc1 hscale.le).trans (by simpa using hscale_short.trans (G.ordered.trans G.middle_le))
    nlinarith
  have hfit : (ρ / (4 * D.a)) * r ≤ G.short / 2 := by
    have he : (ρ / (4 * D.a)) * r = scale / 16 := by dsimp [r]; field_simp; ring
    rw [he]
    linarith
  have hratio : δ / r ≤ 4 * ρ / scale := by
    apply (div_le_iff₀ hr).mpr
    have he : (4 * ρ / scale) * r = D.a := by dsimp [r]; field_simp
    rw [he]
    exact D.grains.1
  let F := ⋃ i : Fin R.card, D.Hg (enumerate R i)
  let U := ⋃ i, Y i
  have hFU : F ⊆ U := iUnion_subset fun i => D.grain_subset_ambient (enumerate R i)
  have hUball : U ⊆ ball (0 : V) 1 := iUnion_subset fun i =>
    (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1
  have hupper : ∀ q ∈ F, μ (U ∩ ball q r) ≤
      O ((δ ^ (-t) * (4 * ρ / scale) ^ s) * r ^ 3) := by
    intro q hq
    apply (hcap q (hFU hq) r hr hr1).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  have hbox : G.affine '' F ⊆ P G.short G.middle 4 G.center G.frame := by
    rw [image_iUnion]
    exact iUnion_subset fun i => (G.contained i).trans (G.enclosure i)
  have hh := affine_prism_density_upper G.short_pos G.ordered G.middle_le hr
    (by positivity : 0 ≤ ρ / (4 * D.a)) hfit (by positivity : 0 ≤ δ ^ (-t) * (4 * ρ / scale) ^ s)
    (by positivity : 0 ≤ ρ / (64 * D.a * c ^ 2)) G.affine G.center G.frame F U
    G.jacobian G.forward_lipschitz hFU hUball hbox hupper
  have hpow : (4 * ρ / scale) ^ s = (4 : ℝ) ^ s * (ρ / scale) ^ s := by
    rw [mul_div_assoc, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
  rw [hpow] at hh
  simpa only [F, image_iUnion, normalizedShade, mul_assoc, mul_left_comm, mul_comm] using hh


/-- The short-side specialization of the arbitrary smaller-scale cap. -/
theorem normalized_block_density_upper (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {s t : ℝ} (hs : 0 ≤ s)
    (hA : A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (hcap : ∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-t) * (δ / r) ^ s * r ^ 3))
    (R : Finset (Fin D.L)) (G : D.NormalizedBlock R) :
    μ (⋃ i, D.normalizedShade R G.affine i) ≤
      O (512 * (4 : ℝ) ^ s * δ ^ (-t) * (ρ / G.short) ^ s * (4 * G.short * G.middle)) :=
  D.normalized_block_density_upper_at hδ hs hA hcap R G G.short_pos le_rfl

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
