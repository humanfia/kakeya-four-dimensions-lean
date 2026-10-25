-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DiscretizedRingGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RingCoverDichotomy
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RingNumerics
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealFrostmanPair

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A fixed expression consisting of `A` plus four differences of products
has a power gain over a nonconcentrated one-dimensional set. This statement
concerns the full expression, not just the two sets `A + A` and `A * A`. -/
theorem discretized_ring_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ η gain δ₀ : ℝ, 0 < η ∧ 0 < gain ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A →
          CoverLower δ (↑(A + fourProductDifference A) : Set ℝ) (δ ^ (-σ - gain)) := by
  classical
  let κ := min ε 1 / 10000
  have hκ : 0 < κ := by dsimp [κ]; exact div_pos (lt_min hε (by norm_num)) (by norm_num)
  have hκ1 : κ ≤ 1 / 10000 := by dsimp [κ]; linarith [min_le_right ε (1 : ℝ)]
  obtain ⟨ρ₀, hρ₀, hcore⟩ := ring_cover_dichotomy (2500 * κ) (by positivity)
  obtain ⟨d₁, hd₁, hd₁1, hcut⟩ := exists_monomial_bound 128 (a := κ) (b := 0) hκ
  obtain ⟨d₂, hd₂, hd₂1, hscale⟩ := exists_monomial_bound (16 / ρ₀)
    (a := 1 - 200 * κ) (b := 0) (by linarith)
  refine ⟨κ, 10 * κ, min d₁ d₂, hκ, by positivity, lt_min hd₁ hd₂,
    (min_le_left _ _).trans hd₁1, ?_⟩
  intro δ σ C hδ hδs hσ hσmax hC hCb A hAne hA hAF m cc hcov
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hd₁1
  have hsmall : 128 * δ ^ κ ≤ 1 := by
    simpa only [Real.rpow_zero] using hcut δ hδ (hδs.trans (min_le_left _ _))
  have hb := ring_scale_budget hδ hδ1 hκ hκ1 hσ hCb hsmall
  have hσmax' : σ ≤ 1 - 10000 * κ := by dsimp [κ]; linarith [min_le_left ε (1 : ℝ)]
  have hscaled : 16 * δ / (δ ^ (100 * κ) * δ ^ (100 * κ)) ≤ ρ₀ := by
    rw [ring_ratio_scale hδ]
    have hh := hscale δ hδ (hδs.trans (min_le_right _ _))
    rw [Real.rpow_zero] at hh
    have hh' : (16 * δ ^ (1 - 200 * κ)) / ρ₀ ≤ 1 := by convert hh using 1 <;> ring
    have := (div_le_iff₀ hρ₀).mp hh'
    simpa only [one_mul] using this
  have hpair := hAF.exists_separated_pair hAne hb.1 hb.2.2
  rcases hcore δ (δ ^ (100 * κ)) C σ hδ hb.1 hb.2.1 hscaled hC hσ A hAne hA hAF
      hpair m cc hcov with hdense | hsparse
  · exact ring_dense_power_gain hδ hδ1 hκ hκ1 hσmax' (by linarith) hCb
      (Nat.cast_nonneg _) hsmall hdense
  · exact ring_sparse_power_gain hδ hδ1 hκ hσ (by linarith : σ ≤ 1) (by linarith) hCb
      (Nat.cast_nonneg _) hsmall hsparse

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
