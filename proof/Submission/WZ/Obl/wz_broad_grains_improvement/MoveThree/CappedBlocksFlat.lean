-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CappedBlocksFlat.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CappedBlocksFlat.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SharpBlockDensity
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityUpper
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NonflatPowers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- In a family satisfying the ball-density cap, every saturated block is
flat by a fixed zeta power. The width bound keeps this power independent of
the ratio between sigma and omega. -/
theorem capped_normalized_blocks_flat {σ ω ζ : ℝ}
    (hσ : 0 < σ) (hω : 0 < ω) (hζ : 0 < ζ) (hbody : BodyEstimate σ ω) :
    ∃ η : ℝ, 0 < η ∧ η ≤ min 1 (ζ / 16) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η → ∀ p : ℕ,
      ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (b ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
        (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
          μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) →
        ∀ (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
          (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
          G.short / G.middle < δ ^ (ζ / 4) := by
  obtain ⟨C, η, d₁, hC, hη, hd₁, hd₁small, Hlow⟩ :=
    sharp_normalized_block_density hbody (ζ * σ / 16) (by positivity)
  refine ⟨min η (min 1 (ζ / 16)), by positivity, min_le_right _ _, ?_⟩
  intro ε hε hεη p
  have hεbody : ε ≤ η := hεη.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ : ε ≤ ζ / 16 := hεη.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨d₂, hd₂, hd₂one, HP⟩ := grainPackingCoefficient_power_bound hε
  let K := 512 * (4 : ℝ) ^ (σ + ω)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨d₃, hd₃, HC⟩ := exists_rpow_cutoff (by positivity : 0 < 3 * ζ * σ / 16)
    (by positivity : 0 < (C / (2 : ℝ) ^ p) / (2 * K))
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃),
    (min_le_left _ _).trans (hd₁small.trans (by norm_num)), ?_⟩
  intro δ hδ hδd b ρ c n x v Y hA hcap D R hR G
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδd₂.trans hd₂one
  have hP := grainPackingCoefficient_ge_one δ ε
  have hshort := G.short_pos
  have hmiddle := G.short_pos.trans_le G.ordered
  obtain ⟨ha, hρ, -, hc, -⟩ := D.dimensions hδ
  by_contra hnonflat
  have haspect : δ ^ (ζ / 4) ≤ G.short / G.middle := le_of_not_gt hnonflat
  have hfactor := sharp_nonflat_density_factor hδ hδ1 hζ hσ hεζ le_rfl D.large.le
    (zero_lt_one.trans_le hP) (HP δ hδ hδd₂) haspect
  have hlo := Hlow δ ε hδ hδd₁ hε.le (le_min hεbody hε1) ζ b ρ c p n x v Y hA D R hR G
  have hup := D.normalized_block_density_upper hδ (show 0 ≤ σ + ω by positivity) hA
    (by simpa only [add_comm σ ω] using hcap) R G
  let X := (ρ / G.short) ^ (σ + ω) * (4 * G.short * G.middle)
  have hX : 0 < X := by dsimp [X]; positivity
  have hup' : μ (⋃ i, D.normalizedShade R G.affine i) ≤
      O ((K * δ ^ (-(ζ * σ / 16))) * X) := by
    convert hup using 1 <;> dsimp [K, X] <;> ring
  have hreal : (C / (2 : ℝ) ^ p) * δ ^ (-(ζ * σ / 4)) ≤ K * δ ^ (-(ζ * σ / 16)) := by
    have hh : O (((C / (2 : ℝ) ^ p) * δ ^ (-(ζ * σ / 4))) * X) ≤
        O ((K * δ ^ (-(ζ * σ / 16))) * X) := by
      apply le_trans _ (hlo.trans hup')
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ (C / (2 : ℝ) ^ p) * X)
      dsimp [X] at h ⊢
      nlinarith only [h]
    exact (mul_le_mul_iff_left₀ hX).mp
      ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh)
  have hid₁ : δ ^ (-(ζ * σ / 4)) * δ ^ (ζ * σ / 4) = 1 := by
    rw [← Real.rpow_add hδ]
    simp
  have hid₂ : δ ^ (-(ζ * σ / 16)) * δ ^ (ζ * σ / 4) = δ ^ (3 * ζ * σ / 16) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg hδ.le (ζ * σ / 4))
  rw [mul_assoc, hid₁, mul_one, mul_assoc, hid₂] at hh
  have hcut := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp (HC δ hδ hδd₃)
  have hcoef : 0 < C / (2 : ℝ) ^ p := by positivity
  nlinarith

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
