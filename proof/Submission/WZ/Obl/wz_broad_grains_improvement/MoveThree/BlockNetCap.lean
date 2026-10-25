-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockNetCap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockNetCap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityUpper

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

def netCapCoefficient (k s : ℝ) : ℝ := 512 * (25 / (128 * k)) ^ s

theorem netCapCoefficient_pos {k s : ℝ} (hk : 0 < k) : 0 < netCapCoefficient k s := by
  unfold netCapCoefficient
  positivity

namespace BlockFirstFilling

variable {ω ζ δ ε b ρ c β τ lam den k : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}

/-- Express the ambient density cap in the exact radius used by the filled
carrier net. Its constant is uniform over every block and packet. -/
theorem normalized_block_net_cap (F : BlockFirstFilling A lam den k hk)
    (hδ : 0 < δ) (hR : R.Nonempty) {s uc : ℝ} (hs : 0 ≤ s)
    (hA : WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.A δ (ε / 4)
      (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (hcap : ∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-uc) * (δ / r) ^ s * r ^ 3)) :
    μ (⋃ i, D.normalizedShade R G.affine i) ≤
      O (netCapCoefficient k s * δ ^ (-uc) * (4 * F.radius) ^ s *
        (4 * G.short * G.middle)) := by
  have hρ := (D.dimensions hδ).2.1
  have ha := (A.packet_dimensions hδ hR).1
  have hB := F.radius_pos hδ hR
  have hscale : A.packetShort / 100 ≤ G.short := by
    have hh := A.packet_short_le_old hδ hR
    linarith only [hh]
  have H := D.normalized_block_density_upper_at hδ hs hA hcap R G
    (by positivity : 0 < A.packetShort / 100) hscale
  have hp : (4 : ℝ) ^ s * (ρ / (A.packetShort / 100)) ^ s =
      (25 / (128 * k)) ^ s * (4 * F.radius) ^ s := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
      ← Real.mul_rpow (by positivity : 0 ≤ 25 / (128 * k))
        (by positivity : 0 ≤ 4 * F.radius)]
    congr 1
    unfold radius
    field_simp
    ring
  have heq : 512 * (4 : ℝ) ^ s * δ ^ (-uc) * (ρ / (A.packetShort / 100)) ^ s *
      (4 * G.short * G.middle) =
      netCapCoefficient k s * δ ^ (-uc) * (4 * F.radius) ^ s *
        (4 * G.short * G.middle) := by
    calc
      _ = 512 * δ ^ (-uc) * ((4 : ℝ) ^ s * (ρ / (A.packetShort / 100)) ^ s) *
          (4 * G.short * G.middle) := by ring
      _ = _ := by rw [hp]; unfold netCapCoefficient; ring
  simpa only [heq] using H

end BlockFirstFilling
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
