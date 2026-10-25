import Submission.Obl.k4_compatible_pair_frame_preparation.FrameScales
import Submission.Obl.k4_compatible_pair_frame_preparation.FramePowers
import Submission.Obl.k4_compatible_pair_frame_preparation.PolynomialBudgets

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial Construction Construction.PrepData

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

/-- The new moving frame has polynomial size and the required subpower width. -/
theorem polynomial_frame_bounds (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ)
    (hκN : frameSlack p.κ ≤ Nk) (i : Fin p.toPrep.J) :
    (p.toPrep.fQ i).det ≠ 0 ∧
    ‖p.toPrep.fc i‖ + ‖p.toPrep.fu i‖ ≤ Nk ^ (M + 5) ∧
    (∑ r : Fin 2, ∑ c : Fin 2, (|p.toPrep.fQ i r c| + |(p.toPrep.fQ i)⁻¹ r c|)) ≤
      Nk ^ (M + 4) ∧
    (∑ r : Fin 2, ∑ c : Fin 2, |p.toPrep.fQ i r c|) ≤ frameSlack p.κ / (2 : ℝ) ^ p.T := by
  let hp := p.toPrep_hyp hN hB
  have hκ : p.κ ≤ Nk := (frameSlack_input p.κ_one).trans hκN
  have hK := frameSlack_matrix p.κ_one
  have hwidth := (hp.frame_bounds i).2.1
  have hwidthK : (∑ r : Fin 2, ∑ c : Fin 2, |p.toPrep.fQ i r c|) ≤
      frameSlack p.κ / (2 : ℝ) ^ p.T :=
    hwidth.trans (div_le_div_of_nonneg_right hK (by positivity))
  refine ⟨(hp.frame_bounds i).1,
    (hp.frame_cu i).trans (center_polynomial_budget hN hκ M), ?_, hwidthK⟩
  apply (hp.frame_bounds i).2.2.1.trans
  have hT : (1 : ℝ) ≤ 2 ^ p.T := one_le_pow₀ (by norm_num)
  have hdiv : (632 * (4 * p.κ) ^ 2) / (2 : ℝ) ^ p.T ≤ Nk := by
    apply le_trans (div_le_self (by positivity) hT)
    exact hK.trans hκN
  have hscale : p.R₂ ≤ p.toPrep.Afr * p.toPrep.S₂ :=
    hp.R₂_le_S₂.trans (le_mul_of_one_le_left hp.S₂pos.le hp.Afr_one)
  have hi : 1 / (p.toPrep.Afr * p.toPrep.S₂) ≤ Nk ^ M := by
    calc
      1 / (p.toPrep.Afr * p.toPrep.S₂) ≤ p.R₂⁻¹ := by
        rw [one_div]
        exact inv_anti₀ p.hR₂pos hscale
      _ ≤ Nk ^ M := p.hR₂inv
  calc
    4 * ((632 * (4 * p.toPrep.κ₀) ^ 2) / (2 : ℝ) ^ p.toPrep.T) +
        4 / (p.toPrep.Afr * p.toPrep.S₂) ≤ 4 * Nk + 4 * Nk ^ M := by
      change 4 * ((632 * (4 * p.κ) ^ 2) / (2 : ℝ) ^ p.T) +
        4 / (p.toPrep.Afr * p.toPrep.S₂) ≤ _
      rw [div_eq_mul_one_div 4]
      linarith
    _ ≤ Nk ^ (M + 4) := matrix_polynomial_budget hN M

/-- The transported tests have one fixed polynomial coefficient exponent. -/
theorem polynomial_test_bounds (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ)
    {Mb : ℕ} (hBinv : ∀ γ, (Bk γ)⁻¹ ≤ Nk ^ Mb)
    (hκN : frameSlack p.κ ≤ Nk) (s : Fin p.toPrep.m) :
    (p.toPrep.P (frameSlack p.κ) s).totalDegree ≤ 2 ∧
    ∀ d, |(p.toPrep.P (frameSlack p.κ) s).coeff d| ≤ Nk ^ (30 * (M + Mb + 10)) := by
  let hp := p.toPrep_hyp hN hB
  let Z := Nk ^ (M + Mb + 10)
  have hN1 : 1 ≤ Nk := by linarith
  have hNZ : Nk ≤ Z := by
    dsimp [Z]
    simpa only [pow_one] using pow_le_pow_right₀ hN1 (show 1 ≤ M + Mb + 10 by omega)
  have hZ : 2 ≤ Z := hN.trans hNZ
  have hκZ : frameSlack p.κ ≤ Z := hκN.trans hNZ
  have hκ0 : 0 ≤ frameSlack p.κ := zero_le_one.trans (frameSlack_one p.κ_one)
  let i := p.toPrep.frame s
  have hfr := p.polynomial_frame_bounds hN hB hκN i
  have hcu : ‖p.toPrep.fc i‖ + ‖p.toPrep.fu i‖ ≤ Z :=
    hfr.2.1.trans (pow_le_pow_right₀ hN1 (by omega))
  have hQ : (∑ r : Fin 2, ∑ c : Fin 2, |p.toPrep.fQ i r c|) ≤ Z := by
    apply hfr.2.2.2.trans
    exact (div_le_self hκ0 (one_le_pow₀ (by norm_num))).trans hκZ
  have hBi : (Bk (p.toPrep.fγ i))⁻¹ ≤ Z :=
    (hBinv _).trans (pow_le_pow_right₀ hN1 (by omega))
  have hj : (((p.toPrep.fj i : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ p.toPrep.T := by
    exact_mod_cast (p.toPrep.fj i).isLt
  have hs := physScale_le (Nat.cast_nonneg (p.toPrep.fj i : ℕ)) hj hκ0
    (hB (p.toPrep.fγ i)) (p.toPrep.fc i) (p.toPrep.fu i) (p.toPrep.fQ i)
  have hscale : physScale p.toPrep.T ((p.toPrep.fj i : ℕ) : ℝ) (frameSlack p.κ)
      (Bk (p.toPrep.fγ i)) (p.toPrep.fc i) (p.toPrep.fu i) (p.toPrep.fQ i) ≤ Z ^ 11 :=
    substitution_polynomial_budget hZ hκ0 hκZ (by positivity) hcu (by positivity) hQ hBi hs
  have hP := hp.P_props (frameSlack p.κ) s
  refine ⟨hP.1, fun d => (hP.2 d).trans ?_⟩
  have hMZ : Nk ^ M ≤ Z := pow_le_pow_right₀ hN1 (by omega)
  calc
    81 * Nk ^ M * physScale p.toPrep.T ((p.toPrep.fj i : ℕ) : ℝ) (frameSlack p.κ)
        (p.toPrep.B (p.toPrep.fγ i)) (p.toPrep.fc i) (p.toPrep.fu i) (p.toPrep.fQ i) ^ 2 ≤
        Z ^ 30 := coefficient_polynomial_budget hZ (by positivity) hMZ
          ((one_le_physScale _ _ _ _ _ _ _).trans' zero_le_one) hscale
    _ = Nk ^ (30 * (M + Mb + 10)) := by
      dsimp [Z]
      rw [← pow_mul, Nat.mul_comm (M + Mb + 10) 30]

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
