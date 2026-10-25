-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockNetParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockNetParameters.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockFirstFilling

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate exists_rpow_cutoff)

noncomputable section

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- The sharper original-scale form of the cardinality estimate used in
`block_cardinality_bound`. -/
theorem block_cardinality_at_base (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4096) (hε : ε ≤ 1)
    (hA : A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (R : Finset (Fin D.L)) : (R.card : ℝ) ≤ δ ^ (-100 : ℝ) := by
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hcard : (R.card : ℝ) ≤ D.L := by
    exact_mod_cast (show R.card ≤ D.L by simpa using Finset.card_le_univ R)
  have hL := grain_card_bound hδ hA D.cover D.grains
  have h64 : (64 : ℝ) ≤ δ ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ]
    linarith
  have hexp : δ ^ (-(2 * (ε / 4) + 5)) ≤ δ ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    _ ≤ (D.L : ℝ) := hcard
    _ ≤ 64 * δ ^ (-(2 * (ε / 4) + 5)) := hL
    _ ≤ δ ^ (-1 : ℝ) * δ ^ (-6 : ℝ) :=
      mul_le_mul h64 hexp (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-7 : ℝ) := by rw [← Real.rpow_add hδ]; norm_num
    _ ≤ δ ^ (-100 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)

/-- Saturation with a positive original coefficient rules out an empty block. -/
theorem NormalizedBlock.nonempty (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    {R : Finset (Fin D.L)} (G : D.NormalizedBlock R) (hδ : 0 < δ) : R.Nonempty := by
  by_contra hnone
  have hempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hcard0 : R.card = 0 := by rw [hempty]; rfl
  have hsat := G.saturated
  rw [hcard0, Nat.cast_zero, mul_zero, zero_mul] at hsat
  have hshort := G.short_pos
  have hmid := hshort.trans_le G.ordered
  have hM := (Real.rpow_pos_of_pos hδ (-ζ)).trans D.large
  have hpos : 0 < grainCoefficient D.a ρ c D.z D.e D.Q *
      (4 * G.short * G.middle) := by positivity
  exact (not_lt_of_ge hsat) hpos

end ConcentratedGrainData

/-- A fixed balancing depth suffices at every original scale. -/
theorem net_balancing_depth {s : ℝ} (hs : 0 < s) :
    ∃ d : ℕ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      1 < δ ^ (-s) ∧ δ ^ (-100 : ℝ) < (δ ^ (-s)) ^ d := by
  obtain ⟨d, hd⟩ := exists_nat_gt (100 / s)
  have hsd : 100 < s * (d : ℝ) := by
    have hh := (div_lt_iff₀ hs).mp hd
    nlinarith only [hh]
  have hd0 : 0 < d := by
    have : (0 : ℝ) < d := (by positivity : (0 : ℝ) < 100 / s).trans hd
    exact_mod_cast this
  refine ⟨d, hd0, ?_⟩
  intro δ hδ hδ1
  refine ⟨Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδ1 (neg_neg_of_pos hs), ?_⟩
  rw [← Real.rpow_mul_natCast hδ.le]
  exact Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by nlinarith only [hsd])

namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

theorem packet_short_le_old (A : BlockAngularData D R G β τ)
    (hδ : 0 < δ) (hR : R.Nonempty) : A.packetShort ≤ 100 * G.short := by
  have hρ := (D.dimensions hδ).2.1
  let i : Fin R.card := ⟨0, Finset.card_pos.mpr hR⟩
  have hr := ball_in_prism_short_width (by positivity : 0 < ρ / 100)
    (G.affine (D.z (enumerate R i))) G.center G.frame ((G.round i).trans (G.enclosure i))
  unfold packetShort
  exact max_le (by linarith) ((min_le_left _ _).trans (by nlinarith only [G.short_pos]))

end BlockAngularData

/-- The coarse lower-scale condition absorbs the fixed contraction in the
net radius, uniformly over every block and angular label. -/
theorem first_filling_net_scale_cutoff {ω k : ℝ} (hω : 0 < ω) (hk : 0 < k) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ ρ a : ℝ, δ ^ (1 - ω / 100) ≤ ρ → 0 < a → a ≤ 4 →
        4 * δ ≤ 256 * k * (2 * ρ) / a := by
  obtain ⟨d₀, hd₀, H⟩ := exists_rpow_cutoff (by positivity : 0 < ω / 100)
    (by positivity : 0 < 32 * k)
  refine ⟨d₀, hd₀, ?_⟩
  intro δ hδ hδd ρ a hρ ha ha4
  have hρ0 := (Real.rpow_pos_of_pos hδ (1 - ω / 100)).trans_le hρ
  have hδρ : δ ≤ 32 * k * ρ := by
    calc
      δ = δ ^ (ω / 100) * δ ^ (1 - ω / 100) := by
        rw [← Real.rpow_add hδ, show ω / 100 + (1 - ω / 100) = 1 by ring, Real.rpow_one]
      _ ≤ 32 * k * ρ := mul_le_mul (H δ hδ hδd) hρ
        (Real.rpow_nonneg hδ.le _) (by positivity)
  apply (le_div_iff₀ ha).mpr
  have hh := mul_le_mul_of_nonneg_left ha4 (by positivity : 0 ≤ 4 * δ)
  nlinarith only [hh, hδρ]

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
