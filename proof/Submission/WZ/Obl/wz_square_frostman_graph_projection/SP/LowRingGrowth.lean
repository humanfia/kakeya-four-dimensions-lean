-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LowRingGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LowRingDichotomy
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LowRingNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanPair

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Uniform ring growth for every fixed range of positive exponents
below one half. Separation is not required. -/
theorem low_discretized_ring_growth (β : ℝ) (hβ : 0 < β) :
    ∃ η gain δ₀ : ℝ, 0 < η ∧ 0 < gain ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → β ≤ σ → σ ≤ 1 / 2 →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A →
          CoverLower δ (↑(A + fourProductDifference A) : Set ℝ) (δ ^ (-σ - gain)) := by
  classical
  let b := min β (1 / 2)
  let κ := b / 100000
  have hb : 0 < b := lt_min hβ (by norm_num)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hbκ : 100000 * κ = b := by dsimp [κ]; ring
  obtain ⟨dC, hdC, hdC1, hcut⟩ := exists_power_bound (max 128 (5120 * energyConstant (3 / 4))) hκ
  obtain ⟨dR, hdR, hdR1, hscale⟩ := exists_monomial_bound 16 (a := 499 / 500) (b := 0) (by norm_num)
  refine ⟨κ, 10 * κ, min dC (min dR (1 / 2)), hκ, by positivity,
    lt_min hdC (lt_min hdR (by norm_num)), (min_le_left _ _).trans hdC1, ?_⟩
  intro δ σ C hδ hδs hσ hσ1 hC hCb A hA hAb hAF m cc hcov
  have hδC : δ ≤ dC := hδs.trans (min_le_left _ _)
  have hδR : δ ≤ dR := (hδs.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := (hδs.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδlt : δ < 1 := by linarith
  have hσb : 100000 * κ ≤ σ := by rw [hbκ]; exact (min_le_left _ _).trans hσ
  have hσp : 0 < σ := hβ.trans_le hσ
  have hconst := hcut δ hδ hδC
  have hδq : δ ≤ δ ^ (1 / 1000 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num : (1 / 1000 : ℝ) ≤ 1)
  have hq1 : δ ^ (1 / 1000 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hsmall : 16 * δ / (δ ^ (1 / 1000 : ℝ) * δ ^ (1 / 1000 : ℝ)) ≤ 1 := by
    rw [low_ring_ratio_scale hδ]
    simpa only [Real.rpow_zero] using hscale δ hδ hδR
  have hpairbudget : C * (δ ^ (1 / 1000 : ℝ)) ^ σ < 1 := by
    calc
      C * (δ ^ (1 / 1000 : ℝ)) ^ σ ≤ δ ^ (-κ) * (δ ^ (1 / 1000 : ℝ)) ^ σ := by gcongr
      _ = δ ^ (σ / 1000 - κ) := by rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ κ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ < 1 := Real.rpow_lt_one hδ.le hδlt hκ
  have hpair := hAF.exists_separated_pair hA hδq hpairbudget
  have hbounds := low_ring_power_bounds hδ hδ1 hκ hσb hσ1 (by linarith) hCb hconst
  have hh : 1 ≤ δ ^ (σ + 10 * κ) * (m : ℝ) := by
    rcases low_ring_cover_dichotomy hδ hδq hq1 hsmall hC hσp hσ1 A hA hAb hAF hpair m cc hcov with h | h
    · exact h.trans (mul_le_mul_of_nonneg_right hbounds.1 (Nat.cast_nonneg _))
    · exact h.trans (mul_le_mul_of_nonneg_right hbounds.2 (Nat.cast_nonneg _))
  calc
    δ ^ (-σ - 10 * κ) = δ ^ (-σ - 10 * κ) * 1 := (mul_one _).symm
    _ ≤ δ ^ (-σ - 10 * κ) * (δ ^ (σ + 10 * κ) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le _)
    _ = (m : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
