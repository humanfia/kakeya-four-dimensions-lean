-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseUniform.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RefinedCoarseMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorRetention

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Multiplicity never exceeds the number of members. -/
theorem multiplicity_le_family_card {N : ℕ} (Y : Fin N → Set Space) (p : Space) :
    multiplicity Y p ≤ (N : ENNReal) := by
  classical
  calc
    _ ≤ ∑ _j : Fin N, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hp : p ∈ Y j <;> simp [Set.indicator, hp]
    _ = _ := by simp

namespace Interfaces

/-- A uniform coarse estimate at every scale. Small carriers use E and large
carriers use the convex count. All input errors can be chosen independently
below explicit thresholds. -/
theorem uniform_coarse_multiplicity {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hE : E σ ω) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Cc H0 d0 : ℝ, 0 < Cc ∧ 0 < H0 ∧ 0 < d0 ∧
    ∀ {δ η h ρ ν ξ t m a b H M0 : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {Y Z Z' : Fin n → Set V} {S : Finset (Fin n)}
      {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L},
      0 < δ → δ ≤ d0 → δ ≤ ρ →
      0 ≤ h → 0 ≤ η → 0 ≤ ν → 0 ≤ ξ →
      h ≤ τ / 100 → η ≤ τ / 100 → ν ≤ τ / 100 → ξ ≤ τ / 100 → t ≤ τ / 100 → H ≤ H0 →
      U.Nonempty → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
      Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g →
      δ ^ t * b ≤ a → (∀ i, Z' i ⊆ Z i) →
      (∃ j, (packetShading b S Z' f U g j).Nonempty) →
      (n : ℝ) ≤ δ ^ (-ξ) * (S.filter fun i => f i ∈ U).card →
      (∀ k ∈ U, (∃ i ∈ S, f i = k ∧ (Z' i).Nonempty) →
        o (δ ^ H * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤ ∑ i ∈ S with f i = k, μ (Z' i)) →
      0 ≤ M0 →
      (∀ p ∈ ⋃ j, packetUnion S Z' f U g j, o M0 ≤ multiplicity (packetUnion S Z' f U g) p) →
      M0 ≤ Cc * δ ^ (-τ) * (b ^ (-ω) * (L * b) ^ σ) := by
  classical
  let β := τ / 100
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨Cf, ηE, hCf, hηE, hfar⟩ := refined_coarse_multiplicity hσ hE β hβ
  let H0 := β * ηE / 2
  have hH0 : 0 < H0 := by dsimp [H0]; positivity
  obtain ⟨d1, hd1, hsmall1⟩ := fixed_constant_power_bound (C := 900) (by norm_num) hH0
  obtain ⟨d2, hd2, hsmall2⟩ := fixed_constant_power_bound (C := 3) (by norm_num) hβ
  refine ⟨max Cf (8 * coarseVolumeConstant), H0, min 1 (min d1 d2),
    lt_of_lt_of_le hCf (le_max_left _ _), hH0, lt_min zero_lt_one (lt_min hd1 hd2), ?_⟩
  intro δ η h ρ ν ξ t m a b H M0 n N L x v Y Z Z' S y w f U z e g
    hδ hδd hδρ hh hη hν hξ hhsmall hηsmall hνsmall hξsmall htsmall hHsmall
    hU hA hC hcover hround hsub hoccupied hcard hdense hM0 hmult
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδd1 : δ ≤ d1 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  have hL : 0 < L := by
    obtain ⟨j, _⟩ := hoccupied
    exact Nat.zero_lt_of_lt j.isLt
  by_cases hscale : b ≤ δ ^ β
  · have hβsmall : δ ^ β ≤ 1 / 3 := by
      have hh := mul_le_mul_of_nonneg_left (hsmall2 δ hδ hδd2) (Real.rpow_nonneg hδ.le β)
      rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero] at hh
      linarith
    have hdensity : 900 * ((3 / 100 : ℝ) * b) ^ ηE ≤ δ ^ H := by
      calc
        _ ≤ 900 * (δ ^ β) ^ ηE := by
          gcongr
          nlinarith
        _ = 900 * δ ^ (β * ηE) := by rw [← Real.rpow_mul hδ.le]
        _ ≤ δ ^ (-H0) * δ ^ (β * ηE) :=
          mul_le_mul_of_nonneg_right (hsmall1 δ hδ hδd1) (Real.rpow_nonneg hδ.le _)
        _ = δ ^ H0 := by rw [← Real.rpow_add hδ]; congr 1; dsimp [H0]; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hHsmall
    have hv := hfar hδ hδ1 hδρ hh hη hν hξ (hscale.trans hβsmall) hU hA hC hcover
      hround hsub hoccupied hcard hdense hdensity hM0 hmult
    have hsum : h + ν + ξ + η ≤ 4 * β := by dsimp [β]; linarith
    have hprod : σ * (h + ν + ξ + η) ≤ (1 / 2 : ℝ) * (4 * β) :=
      mul_le_mul hσ2 hsum (by positivity) (by norm_num)
    have herr : 2 * (ν + t) + σ * (h + ν + ξ + η) + β ≤ τ := by
      dsimp [β] at hprod ⊢
      linarith
    refine hv.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg herr))
        (Real.rpow_nonneg hδ.le _) (hCf.le.trans (le_max_left _ _))) (by positivity)
  · have hlarge : δ ^ β ≤ b := le_of_not_ge hscale
    have hb8 : b ≤ 8 := by
      simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hcover.bounded
    have hcount := near_round_carrier_count hδ hδρ hA hC hcover hround
    have hclose := close_coarse_count_bound hδ hb hb8
      (show 0 ≤ coarseVolumeConstant by exact le_trans zero_le_one (le_max_left _ _))
      (show (1 : ℝ) ≤ L by exact_mod_cast hL) hσ hω hω1 hlarge hcount
    have hlevel : M0 ≤ (L : ℝ) := by
      obtain ⟨j, q, hq⟩ := hoccupied
      obtain ⟨p, hp, _⟩ := mem_thickening_iff.mp hq
      have hh := (hmult p (Set.mem_iUnion.mpr ⟨j, hp⟩)).trans
        (multiplicity_le_family_card (packetUnion S Z' f U g) p)
      rw [← ENNReal.ofReal_natCast L] at hh
      exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hh
    have herr : ν + t + β * (2 + σ) ≤ τ := by
      have hh := mul_le_mul_of_nonneg_left hσ2 hβ.le
      dsimp [β] at hh ⊢
      nlinarith
    refine hlevel.trans (hclose.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith :
          -τ ≤ -(ν + t) - β * (2 + σ)))
        (Real.rpow_nonneg hδ.le _) (hCf.le.trans (le_max_left _ _))) (by positivity)

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
