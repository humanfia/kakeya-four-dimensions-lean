import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WeightBounds
import Submission.Obl.k4_tempered_grid_selection.SelectionMass
import Submission.Lib.K4ModelReduction.PowerComparison

/-! A retained class of clipped weight exponents cannot consist of tiny worlds. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_tempered_grid_selection

/-- Inverse-subpower retained incidence mass forces a selected weight class
above the clipping threshold. Every selected world then has a positive weight
with the same limiting exponent. -/
theorem clipped_weight_class
    (N K B : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hB : Subpower N B)
    (W : ℕ → ℕ) (M : ℕ) (hW : ∀ k, (W k : ℝ) ≤ N k ^ M)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (m : (k : ℕ) → Fin (W k) → ENNReal)
    (S : (k : ℕ) → Finset (Fin (W k)))
    (hω : ∀ k b, 0 ≤ ω k b ∧ ω k b ≤ 1) (hm : ∀ k b, m k b ≤ 1)
    (hretain : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ ENNReal.ofReal (B k) *
      ∑ b ∈ S k, ENNReal.ofReal (ω k b) * m k b)
    (C β : ℝ) (hC : 0 ≤ C) (hMC : (M : ℝ) < C)
    (hfit : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ S k,
      |weightExponent C (N k) (ω k b) - β| < ε) :
    β ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ S k,
      0 < ω k b ∧ N k ^ (-β - ε) ≤ ω k b ∧ ω k b ≤ N k ^ (-β + ε) := by
  have hN0 : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hNgt : ∀ k, 1 < N k := fun k => by linarith [hN k]
  have hβ : β ≤ M := by
    by_contra hnot
    have hgap : (M : ℝ) < β := lt_of_not_ge hnot
    let ε : ℝ := (β - M) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hupper : ∀ᶠ k in atTop, (∑ b ∈ S k, ENNReal.ofReal (ω k b) * m k b) ≤
        ENNReal.ofReal (N k ^ ((M : ℝ) - β + ε)) := by
      filter_upwards [hfit ε hε] with k hk
      have hωup : ∀ b ∈ S k, ω k b ≤ N k ^ (-β + ε) := by
        intro b hb
        refine (weight_le_rpow_neg_weightExponent hC (hNgt k) (hω k b).1 (hω k b).2).trans ?_
        apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
        linarith [(abs_lt.mp (hk b hb)).1]
      have hcard : ((S k).card : ENNReal) ≤ (W k : ENNReal) := by
        have hc : (S k).card ≤ W k := by
          simpa using Finset.card_le_card (Finset.subset_univ (S k))
        exact_mod_cast hc
      have hcount : (W k : ENNReal) ≤ ENNReal.ofReal (N k ^ M) := by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hW k)
      calc
        _ ≤ ∑ _b ∈ S k, ENNReal.ofReal (N k ^ (-β + ε)) := by
          refine Finset.sum_le_sum fun b hb => ?_
          calc
            _ ≤ ENNReal.ofReal (ω k b) * 1 := mul_le_mul' le_rfl (hm k b)
            _ ≤ ENNReal.ofReal (N k ^ (-β + ε)) := by
              rw [mul_one]
              exact ENNReal.ofReal_le_ofReal (hωup b hb)
        _ = ((S k).card : ENNReal) * ENNReal.ofReal (N k ^ (-β + ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal (N k ^ M) * ENNReal.ofReal (N k ^ (-β + ε)) :=
          mul_le_mul' (hcard.trans hcount) le_rfl
        _ = ENNReal.ofReal (N k ^ ((M : ℝ) - β + ε)) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (hN0 k).le M),
            ← Real.rpow_natCast (N k) M, ← Real.rpow_add (hN0 k)]
          congr 2
          ring
    have hnum : ∀ᶠ k in atTop, 1 ≤ (K k * B k) * N k ^ ((M : ℝ) - β + ε) := by
      filter_upwards [hupper] with k hk
      have hK0 : 0 < K k := by linarith [hK.1 k]
      have hBk : 0 ≤ B k := by linarith [hB.1 k]
      have he : ENNReal.ofReal ((K k)⁻¹) ≤
          ENNReal.ofReal (B k * N k ^ ((M : ℝ) - β + ε)) := by
        calc
          _ ≤ ENNReal.ofReal (B k) *
              (∑ b ∈ S k, ENNReal.ofReal (ω k b) * m k b) := hretain k
          _ ≤ ENNReal.ofReal (B k) * ENNReal.ofReal (N k ^ ((M : ℝ) - β + ε)) :=
            mul_le_mul' le_rfl hk
          _ = _ := (ENNReal.ofReal_mul hBk).symm
      have hre : (K k)⁻¹ ≤ B k * N k ^ ((M : ℝ) - β + ε) :=
        (ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg hBk (Real.rpow_nonneg (hN0 k).le _))).mp he
      have h1 := (div_le_iff₀ hK0).mp
        (show 1 / K k ≤ B k * N k ^ ((M : ℝ) - β + ε) by simpa only [one_div] using hre)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
    have hKB : Subpower N (fun k => K k * B k) := subpower_mul hN0 hK hB
    have hnonneg : 0 ≤ (M : ℝ) - β + ε :=
      Submission.Lib.K4ModelReduction.exponent_le_of_subpower_loss
        N (fun k => K k * B k) hNt hKB.2
        (a := 0) (by simpa only [Real.rpow_zero] using hnum)
    dsimp [ε] at hnonneg
    linarith
  refine ⟨hβ, ?_⟩
  intro ε hε
  have hclipε : 0 < C - β := by linarith
  filter_upwards [hfit ε hε, hfit ((C - β) / 2) (by positivity)] with k hk hclip b hb
  have hc : weightExponent C (N k) (ω k b) < C := by
    have := (abs_lt.mp (hclip b hb)).2
    linarith
  obtain ⟨hpos, hactual⟩ := weightExponent_unclipped hC (hNgt k) (hω k b).2 hc
  have hband := power_band_of_exponent_fit (hNgt k) hpos
    (show |logarithmicExponent (N k) (ω k b) - β| ≤ ε by
      rw [← hactual]
      exact (hk b hb).le)
  exact ⟨hpos, hband⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
