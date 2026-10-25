-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/ZoomDiscriminant.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/ZoomDiscriminant.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.ZoomCoordinates
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.DiscriminantFromGroup

/-!
# The discriminant hypotheses of the sampled exit, from cube data

In cube coordinates the native discriminant has coefficients at most `A_R` (for instance from
`discriminant_coeff_bound_of_group`), and the zoom centre `c` is a point of the group's native
sheet. After centring at `c` (`centered_native_discriminant_preparation`, cost `A_R ↦ A_R^q`) and
dilating by `λ = (A_R^q)^Mexp`, the zoomed coordinates satisfy exactly the three discriminant
hypotheses of `sampled_exit_of_certified_group` with `A = A_R^q`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- The forward zoomed normalization and its inverse. -/
theorem zoom_inverse {c₁ c₁' : Fin 3 → ℝ} {M₁ M₁' : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M₁' * M₁ = 1) (hc : ∀ k, c₁' k = -∑ i : Fin 3, M₁' k i * c₁ i)
    (c : Fin 3 → ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    zoomMatrix M₁' lam * (lam • M₁) = 1 ∧
    ∀ k, zoomShift c₁' M₁' c k = -∑ i : Fin 3, zoomMatrix M₁' lam k i * (lam * (c₁ i - c i)) := by
  refine ⟨?_, ?_⟩
  · rw [zoomMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hlam, one_smul,
      hM]
  · intro k
    simp only [zoomShift, zoomMatrix, Matrix.smul_apply, smul_eq_mul, hc k, Fin.sum_univ_three]
    field_simp
    ring

/-- Cube discriminant bounds and a group point at the centre give the exit's discriminant
hypotheses in zoomed coordinates. -/
theorem zoom_discriminant_conditions (d : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (Mexp : ℕ) (A_R : ℝ), 2 ≤ A_R →
    ∀ (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ) (c : Fin 3 → ℝ)
      (R0 : Poly) (Pot : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 → Pot.totalDegree ≤ d →
      2 ≤ d → (∀ i, |c i| ≤ 1) →
    ∀ (σ A₁ ε wc : ℝ), 2 ≤ A₁ → 2 * A₁ ^ 2 ≤ A_R ^ 2 →
      4 * |nativeA (transportPolynomial c₁' M₁' B' R0)| * ε ≤ (2 * A₁ ^ 2)⁻¹ →
      (∀ m, |(nativeBaseDiscriminant (nativeA (transportPolynomial c₁' M₁' B' R0))
        (nativeB (transportPolynomial c₁' M₁' B' R0))
        (nativeC (transportPolynomial c₁' M₁' B' R0) (basePullback c₁' M₁' Pot))).coeff m| ≤ A_R) →
      |nativeA (transportPolynomial c₁' M₁' B' R0) * wc ^ 2 +
          eval c (nativeB (transportPolynomial c₁' M₁' B' R0)) * wc +
          eval c (nativeC (transportPolynomial c₁' M₁' B' R0) (basePullback c₁' M₁' Pot))| ≤ ε →
      A₁⁻¹ ≤ |2 * nativeA (transportPolynomial c₁' M₁' B' R0) * wc +
          eval c (nativeB (transportPolynomial c₁' M₁' B' R0))| →
      |2 * nativeA (transportPolynomial c₁' M₁' B' R0) * wc +
          eval c (nativeB (transportPolynomial c₁' M₁' B' R0))| ≤ A₁ →
      0 < (2 * nativeA (transportPolynomial c₁' M₁' B' R0) * wc +
          eval c (nativeB (transportPolynomial c₁' M₁' B' R0))) * σ →
      let A := A_R ^ q
      let lam := A ^ Mexp
      let Sz := transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0
      let Pz := basePullback (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) Pot
      2 ≤ A ∧
      (nativeA Sz = 0 → 0 < eval (fun _ => (0 : ℝ)) (baseDilation lam (nativeB Sz)) * σ) ∧
      (∀ m, |(nativeBaseDiscriminant (nativeA Sz) (baseDilation lam (nativeB Sz))
        (baseDilation lam (nativeC Sz Pz))).coeff m| ≤ A) ∧
      (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) (nativeBaseDiscriminant (nativeA Sz)
        (baseDilation lam (nativeB Sz)) (baseDilation lam (nativeC Sz Pz))) := by
  obtain ⟨q, hq, hcentered⟩ := centered_native_discriminant_preparation d
  refine ⟨q, hq, ?_⟩
  intro Mexp A_R hAR c₁' M₁' B' c R0 Pot hR0 hPot hd hc σ A₁ ε wc hA₁ hA₁R hsmall hcoeff hfit hlo
    hhi hsign A lam Sz Pz
  set Sx := transportPolynomial c₁' M₁' B' R0
  set Px := basePullback c₁' M₁' Pot
  have hA2 : 2 ≤ A := hAR.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ A_R) hq)
  have hlam : lam ≠ 0 := pow_ne_zero _ (by positivity)
  obtain ⟨hAeq, hBeq, hCeq⟩ := zoom_native_coefficients c₁' M₁' B' c hlam R0 hR0 Pot
  have hSx : Sx.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hBdeg : (nativeB Sx).totalDegree ≤ d := (totalDegree_nativeB Sx hSx).trans (by omega)
  have hCdeg : (nativeC Sx Px).totalDegree ≤ d :=
    totalDegree_nativeC Sx Px hSx hd ((totalDegree_basePullback _ _ _).trans hPot)
  -- the centre is a point of the sheet: its discriminant clears `A_R⁻²`
  have hwin := discriminant_window hA₁ hfit hlo hhi hsmall
  have hcentre : (A_R⁻¹) ^ 2 ≤ eval c (nativeBaseDiscriminant (nativeA Sx) (nativeB Sx)
      (nativeC Sx Px)) := by
    rw [eval_nativeBaseDiscriminant]
    refine le_trans ?_ hwin.1
    rw [inv_pow, one_div]
    exact inv_anti₀ (by positivity) hA₁R
  obtain ⟨-, -, hcoeffT, hzeroT⟩ := hcentered A_R hAR (nativeB Sx) (nativeC Sx Px) (nativeA Sx) c
    hBdeg hCdeg hc hcoeff hcentre
  refine ⟨hA2, ?_, ?_, ?_⟩
  · intro hzero
    rw [hBeq, eval_baseTranslation]
    have hA0 : nativeA Sx = 0 := hAeq ▸ hzero
    rw [hA0] at hsign
    simpa using hsign
  · intro m
    rw [hAeq, hBeq, hCeq]
    exact hcoeffT m
  · rw [hAeq, hBeq, hCeq]
    exact hzeroT

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
