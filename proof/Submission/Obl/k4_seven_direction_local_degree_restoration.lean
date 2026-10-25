import Submission.Obl.k4_seven_direction_third_derivative_bound
import Submission.Obl.k4_approximate_conic_taylor_decomposition
import Submission.Obl.k4_seven_direction_local_degree_restoration.Small
import Submission.Obl.k4_seven_direction_local_degree_restoration.Hessian
import Submission.Obl.k4_seven_direction_local_degree_restoration.LargeCertificate

namespace Submission

open Obl.k4_seven_direction_local_degree_restoration

/-- The two remaining differential interpolation steps, assembled with the existing
Taylor graph and conic correction constructions. -/
theorem k4_seven_direction_local_degree_restoration :
((fun (ev : MvPolynomial (Fin 4) ℝ → (EuclideanSpace ℝ (Fin 3)) → ℝ → ℝ) (dw : MvPolynomial (Fin 4) ℝ → MvPolynomial (Fin 4) ℝ) => ∃ C : ℕ, 1 ≤ C ∧ ∀ (A Z a b h s : ℝ) (S : MvPolynomial (Fin 4) ℝ) (f : (EuclideanSpace ℝ (Fin 3)) → ℝ) (p : Fin 7 → (EuclideanSpace ℝ (Fin 3))), 2 ≤ A → A ≤ Z → 0 < b → b ≤ a → a ≤ 1 → 0 < h → h * A ^ C ≤ b / a → 0 ≤ s → b⁻¹ ≤ Z → S.totalDegree ≤ 2 → (∀ e, |S.coeff e| ≤ Z) → (∀ u w, |ev (dw (dw S)) u w| ≤ A / a) → ContDiffOn ℝ 6 f (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) 3) → |f 0| ≤ Z → ‖fderiv ℝ f 0‖ ≤ Z → ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z → (∀ (c : ℝ) (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ), ∃ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, s ≤ |f u - c - L u|) → (∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j f u‖ ≤ A * s) → (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) → (∀ i : Fin 7, ∀ j : ℕ, j ≤ 1 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ ≤ A * (b + s * h)) → ((fun R : (EuclideanSpace ℝ (Fin 3)) → ℝ => (∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j R u‖ ≤ A) ∧ (∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤ A * b / a)) (fun u => ev S u (f u) / a)) → ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ Z ^ C) ∧ ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, ∀ w : ℝ, |w - f u| ≤ A * b → A⁻¹ ≤ |ev (dw S) u w| → |ev (dw S) u w| ≤ A → |ev Q u w| ≤ A ^ C * b ∧ A ^ (-(C : ℤ)) ≤ |ev (dw Q) u w| ∧ |ev (dw Q) u w| ≤ A ^ C ∧ |ev (dw (dw Q)) u w| ≤ A ^ C / b) (fun (P : MvPolynomial (Fin 4) ℝ) (u : (EuclideanSpace ℝ (Fin 3))) (w : ℝ) => MvPolynomial.eval ![u 0, u 1, u 2, w] P) (fun P : MvPolynomial (Fin 4) ℝ => MvPolynomial.pderiv (3 : Fin 4) P)) := by
  obtain ⟨Kf, hKf, third_bound⟩ := k4_seven_direction_third_derivative_bound
  obtain ⟨Kr, hKr, conic_decomposition⟩ := k4_approximate_conic_taylor_decomposition
  let K : ℕ := Kf + Kr + 6
  let C : ℕ := 3 * K + 20
  have hK6 : 6 ≤ K := by dsimp [K]; omega
  have hKfK : Kf ≤ K := by dsimp [K]; omega
  have hKrK : Kr ≤ K := by dsimp [K]; omega
  have hKC : K ≤ C := by dsimp [C]; omega
  have hKfC : Kf ≤ C := hKfK.trans hKC
  have hKrC : Kr ≤ C := hKrK.trans hKC
  have hsmallC : Kf + 5 ≤ C := by dsimp [C, K]; omega
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro A Z a b h s S f p hA hAZ hb hba ha1 hh hscale hs0 hbinv
    hSdeg hScoeff hScurv hf hf0 hf1 hf2 hnon hder hp hdet hfdir hRbounds
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have ha : 0 < a := hb.trans_le hba
  have hratio1 : b / a ≤ 1 := (div_le_one₀ ha).2 hba
  have hthird : ∀ u ∈ Metric.closedBall (0 : Base) 2,
      ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ Kf * (b + s * h) := by
    apply third_bound A (b + s * h) f p hA (by positivity) hf hp hdet
    intro i u hu
    simpa only [norm_iteratedFDeriv_one] using hfdir i 1 (by omega) u hu
  by_cases hsmall : s * h ≤ b
  · obtain ⟨Q, hdeg, hcoeff, hQ⟩ :=
      small_nonaffine_case Kf hA hAZ hb hf hf0 hf1 hf2 hthird hsmall
    have hpowA : A ^ (Kf + 5) ≤ A ^ C := pow_le_pow_right₀ hA1 hsmallC
    have hpowZ : Z ^ (Kf + 5) ≤ Z ^ C := pow_le_pow_right₀ hZ1 hsmallC
    have hfloor : A ^ (-(C : ℤ)) ≤ A ^ (-((Kf + 5 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ hA1 (by exact_mod_cast (neg_le_neg (Int.ofNat_le.mpr hsmallC)))
    refine ⟨Q, hdeg, fun e => (hcoeff e).trans hpowZ, ?_⟩
    intro u hu w hw _ _
    obtain ⟨hval, hlow, hupp, hcurv⟩ := hQ u hu w hw
    exact ⟨hval.trans (mul_le_mul_of_nonneg_right hpowA hb.le),
      hfloor.trans hlow, hupp.trans hpowA,
      hcurv.trans (div_le_div_of_nonneg_right hpowA hb.le)⟩
  · have hlarge : b < s * h := lt_of_not_ge hsmall
    have hscale_f : A ^ Kf * h ≤ 1 := by
      calc A ^ Kf * h ≤ A ^ C * h :=
             mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 hKfC) hh.le
           _ = h * A ^ C := by ring
           _ ≤ b / a := hscale
           _ ≤ 1 := hratio1
    obtain ⟨hs, hsymm, hMlo, hMhi, hMdir, hfq⟩ :=
      large_normalizedHessian Kf hA hb hh hlarge hscale_f
        (hf.of_le (by norm_num)) hnon (hder 2 (by omega) (by omega) 0 (by simp))
        (fun u hu => hthird u
          (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hu)) p
        (by
          intro i
          simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
            hfdir i 0 (by omega) 0 (by simp))
    let R : Base → ℝ := fun u => evalAt S u (f u) / a
    let q : Base → ℝ := fun u =>
      Obl.k4_real_conic_restoration.quad (normalizedHessian f s) (fun i => u i)
    have hRjets : ∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j R u‖ ≤ A := hRbounds.1
    have hRtests : ∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 →
        ∀ u ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j (fun v : Base => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤
          A * (b / a) := by
      intro i j hj u hu
      exact (hRbounds.2 i j hj u hu).trans_eq (by ring)
    have hscale_r : h * A ^ Kr ≤ b / a :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 hKrC) hh.le).trans hscale
    obtain ⟨L, lam, hL, hlam, happrox⟩ :=
      conic_decomposition A (b / a) h (normalizedHessian f s) R p hA
        (div_pos hb ha) hratio1 hh hscale_r hsymm hMlo hMhi hp hdet hMdir
        (normalizedGraph_contDiffOn hf S a) hRjets hRtests
    change ∀ u ∈ Metric.closedBall (0 : Base) 1,
      |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
        q u * L u + lam * (q u) ^ 2)| ≤ A ^ Kr * (b / a) at happrox
    have hpowf : A ^ Kf ≤ A ^ K := pow_le_pow_right₀ hA1 hKfK
    have hpowr : A ^ Kr ≤ A ^ K := pow_le_pow_right₀ hA1 hKrK
    apply large_case_of_decomposition K C hK6 (by dsimp [C]; omega)
      hA hAZ hb hba ha1 hh hscale hlarge hbinv hSdeg hScoeff hScurv hf0 hf1
      (R := R) (q := q) (L := L) (lam := lam)
    · intro u
      dsimp [R]
      field_simp
    · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hRjets 0 (by omega) 0 (by simp)
    · simpa only [norm_iteratedFDeriv_one] using hRjets 1 (by omega) 0 (by simp)
    · exact hRjets 2 (by omega) 0 (by simp)
    · intro u hu
      exact (abs_quad_le_coeff (Q := normalizedHessian f s) (by simpa using hu)).trans
        (hMhi.trans (pow_le_pow_right₀ hA1 (by omega : 4 ≤ K)))
    · intro u hu
      exact (hfq u hu).trans (mul_le_mul_of_nonneg_right hpowf hh.le)
    · exact hL.trans hpowr
    · exact hlam.trans hpowr
    · intro u hu
      calc |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
             q u * L u + lam * (q u) ^ 2)| ≤ A ^ Kr * (b / a) := happrox u hu
           _ ≤ A ^ K * (b / a) := mul_le_mul_of_nonneg_right hpowr (by positivity)
           _ = A ^ K * b / a := by ring

end Submission
