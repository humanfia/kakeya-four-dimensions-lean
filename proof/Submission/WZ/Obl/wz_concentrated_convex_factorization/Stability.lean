-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Stability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Coefficient

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section

/-- A finite variational argument: a large subfamily whose coefficient is stable under halving.
The positive integer power can be chosen once as a function of the desired loss exponent. -/
theorem stable_subfamily {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (f : Finset ι → ℝ) (hf : ∀ R ⊆ S, R.Nonempty → 1 ≤ f R)
    (p : ℕ) (hp : 0 < p) {η B : ℝ} (hη : 0 ≤ η) (hB : f S ≤ B)
    (hsmall : η ^ p * B ≤ 1) :
    ∃ R : Finset ι, R ⊆ S ∧ R.Nonempty ∧ η * S.card ≤ R.card ∧
      ∀ P ⊆ R, (R.card : ℝ) ≤ 2 * P.card → f R ≤ 2 ^ p * f P := by
  classical
  let A := S.powerset.filter fun R => R.Nonempty
  have hAS : S ∈ A := by simp [A, hS]
  obtain ⟨R, hRA, hmin⟩ := Finset.exists_min_image A
    (fun R => f R / (R.card : ℝ) ^ p) ⟨S, hAS⟩
  have hRS : R ⊆ S := (Finset.mem_powerset.mp (Finset.mem_filter.mp hRA).1)
  have hR : R.Nonempty := (Finset.mem_filter.mp hRA).2
  have hR0 : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hR1 := hf R hRS hR
  have hRp : 0 < (R.card : ℝ) ^ p := pow_pos hR0 _
  have hSp : 0 < (S.card : ℝ) ^ p := pow_pos hS0 _
  refine ⟨R, hRS, hR, ?_, ?_⟩
  · have hh := (div_le_div_iff₀ hRp hSp).mp (hmin S hAS)
    have hnp : (S.card : ℝ) ^ p ≤ B * (R.card : ℝ) ^ p := calc
      (S.card : ℝ) ^ p ≤ f R * (S.card : ℝ) ^ p := by nlinarith
      _ ≤ f S * (R.card : ℝ) ^ p := hh
      _ ≤ B * (R.card : ℝ) ^ p := mul_le_mul_of_nonneg_right hB hRp.le
    have he : (η * S.card) ^ p ≤ (R.card : ℝ) ^ p := calc
      (η * S.card) ^ p = η ^ p * (S.card : ℝ) ^ p := mul_pow _ _ _
      _ ≤ η ^ p * (B * (R.card : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left hnp (pow_nonneg hη _)
      _ ≤ (R.card : ℝ) ^ p := by nlinarith [mul_le_mul_of_nonneg_right hsmall hRp.le]
    exact (pow_le_pow_iff_left₀ (mul_nonneg hη hS0.le) hR0.le hp.ne').mp he
  · intro P hPR hhalf
    have hP0 : (0 : ℝ) < P.card := by linarith
    have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hP0)
    have hPA : P ∈ A := by simp [A, hPR.trans hRS, hP]
    have hPp : 0 < (P.card : ℝ) ^ p := pow_pos hP0 _
    have hP1 := hf P (hPR.trans hRS) hP
    have hh := (div_le_div_iff₀ hRp hPp).mp (hmin P hPA)
    have hpow : (R.card : ℝ) ^ p ≤ 2 ^ p * (P.card : ℝ) ^ p := by
      simpa only [mul_pow] using pow_le_pow_left₀ hR0.le hhalf p
    have h := hh.trans (mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ f P))
    have he : f P * (2 ^ p * (P.card : ℝ) ^ p) = (2 ^ p * f P) * (P.card : ℝ) ^ p := by ring
    rw [he] at h
    exact (mul_le_mul_iff_left₀ hPp).mp h

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
