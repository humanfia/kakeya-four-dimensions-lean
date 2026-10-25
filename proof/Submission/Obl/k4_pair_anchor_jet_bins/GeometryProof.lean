import Submission.Obl.k4_pair_anchor_jet_bins.Geometry
import Submission.Obl.k4_pair_anchor_jet_bins.DiscIdentities
import Submission.Obl.k4_pair_anchor_jet_bins.Path
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Perturbation

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Set Metric MvPolynomial Submission.Lib.K4QuadraticSheets
open DiscIdentities

private lemma emb_norm_geo (z : R3) : ‖emb z‖ = ‖z‖ :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).norm_map z

/-- The geometric input follows from quadratic coefficient bounds and a nonvanishing path tube. -/
theorem exists_geometry (Cs : ℕ) : ∃ k A₀ : ℝ, Geometry Cs k A₀ := by
  obtain ⟨L, hL, hLip⟩ := Submission.Obl.k4_quadratic_discriminant_safe_paths.exists_quadratic_lipschitz
  let k : ℝ := (Cs : ℝ) + 2
  let A₀ : ℝ := max 2 (L + 2)
  have hk : 1 ≤ k := by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) Cs]
  have hA₂ : ∀ A : ℝ, A₀ ≤ A → 2 ≤ A := fun A hA => (le_max_left _ _).trans hA
  have hLA : ∀ A : ℝ, A₀ ≤ A → L + 2 ≤ A := fun A hA => (le_max_right _ _).trans hA
  have hscale : ∀ A : ℝ, A₀ ≤ A → 2 ≤ A ∧ 2 ≤ A ^ k ∧ (A ^ k)⁻¹ ≤ A⁻¹ := by
    intro A hA
    have hA2 := hA₂ A hA
    have hA0 : 0 < A := by linarith
    have hAk : A ≤ A ^ k := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ A) hk
    exact ⟨hA2, hA2.trans hAk, (inv_le_inv₀ (Real.rpow_pos_of_pos hA0 k) hA0).mpr hAk⟩
  have hinvρ : ∀ A : ℝ, A₀ ≤ A → (A ^ k)⁻¹ ≤ A ^ (-(Cs : ℝ)) := by
    intro A hA
    have hA0 : 0 < A := by linarith [hA₂ A hA]
    rw [← Real.rpow_neg hA0.le k]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hA₂ A hA] : 1 ≤ A)
    dsimp [k]
    linarith
  have hpower : ∀ A : ℝ, A₀ ≤ A → A * A * (A ^ k)⁻¹ = A ^ (-(Cs : ℝ)) := by
    intro A hA
    have hA0 : 0 < A := by linarith [hA₂ A hA]
    rw [← Real.rpow_neg hA0.le k]
    calc
      _ = (A ^ (1 : ℝ) * A ^ (1 : ℝ)) * A ^ (-k) := by simp only [Real.rpow_one]
      _ = A ^ ((1 + 1) + -k) := by rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]
      _ = _ := by congr 1; dsimp [k]; ring
  have hreal : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ),
      ‖eval (fun i => (x i : ℂ)) (P.map (algebraMap ℝ ℂ))‖ = |eval x P| := by
    intro n P x
    rw [eval_map_real, Complex.norm_real, Real.norm_eq_abs]
  have hdisc : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
      ∀ ζ : E3, ‖ζ‖ ≤ 1 → ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i)‖ ≤ A ^ (2 : ℕ) := by
    intro A hA δ P hP ζ hζ
    have hA0 : 0 < A := by linarith [hA₂ A hA]
    have hlip := hLip A (disc P) hA0.le hP.2.2.1 hP.2.2.2 ζ 0 hζ (by simp)
    simp only [PiLp.zero_apply] at hlip
    have hzero : ‖eval (0 : Fin 3 → ℂ) ((disc P).map (algebraMap ℝ ℂ))‖ ≤ A := by
      simpa [eval_zero, constantCoeff_eq, coeff_map, Complex.norm_real, Real.norm_eq_abs] using hP.2.2.2 0
    have hnorm : ‖eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ))‖ ≤ (L + 1) * A := by
      have hdist : dist ζ 0 ≤ 1 := by simpa using hζ
      have hh := norm_add_le
        (eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ)) -
          eval (0 : Fin 3 → ℂ) ((disc P).map (algebraMap ℝ ℂ)))
        (eval (0 : Fin 3 → ℂ) ((disc P).map (algebraMap ℝ ℂ)))
      rw [sub_add_cancel] at hh
      have hmul : L * A * dist ζ 0 ≤ L * A := by nlinarith [mul_pos hL hA0]
      calc
        _ ≤ ‖eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ)) -
            eval (0 : Fin 3 → ℂ) ((disc P).map (algebraMap ℝ ℂ))‖ +
            ‖eval (0 : Fin 3 → ℂ) ((disc P).map (algebraMap ℝ ℂ))‖ := hh
        _ ≤ L * A * dist ζ 0 + A := add_le_add hlip hzero
        _ ≤ L * A + A := add_le_add hmul (le_refl A)
        _ = (L + 1) * A := by ring
    rw [← eval_disc_eq_qdisc P hP.1]
    apply hnorm.trans
    simpa only [pow_two] using mul_le_mul_of_nonneg_right
      (show L + 1 ≤ A by linarith [hLA A hA]) hA0.le
  have hroot : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
      ∀ (ζ : E3) (w : ℂ), ‖ζ‖ ≤ 1 →
      eval (Fin.snoc (fun i => ζ i) w) (P.map (algebraMap ℝ ℂ)) = 0 →
      ‖eval (Fin.snoc (fun i => ζ i) w) (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ ≤
        A ^ (2 : ℕ) := by
    intro A hA δ P hP ζ w hζ hw
    have heq := pderiv_sq_eq_qdisc_of_root (P.map (algebraMap ℝ ℂ))
      ((degree_map_le P).trans hP.1) (fun i => ζ i) w hw
    have hnorm : ‖eval (Fin.snoc (fun i => ζ i) w)
        (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ ^ 2 ≤ A ^ (2 : ℕ) := by
      rw [← norm_pow, heq]
      exact hdisc A hA δ P hP ζ hζ
    have hA2 := hA₂ A hA
    have hn := norm_nonneg (eval (Fin.snoc (fun i => ζ i) w)
      (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))))
    have hd : ‖eval (Fin.snoc (fun i => ζ i) w)
        (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ ≤ A :=
      (sq_le_sq₀ hn (by linarith : 0 ≤ A)).mp hnorm
    exact hd.trans (by nlinarith [mul_nonneg (show 0 ≤ A by linarith) (show 0 ≤ A - 1 by linarith)])
  have hanchor : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
      ∀ α : R3, α ∈ closedBall (0 : R3) (1 / 8) →
      A ^ (-(Cs : ℝ)) ≤ |eval (fun i => α i) (disc P)| →
      P.map (algebraMap ℝ ℂ) ≠ 0 ∧
      ∀ ζ ∈ ball (emb α) (A ^ k)⁻¹,
        ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) -
          qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖ <
          ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖ := by
    intro A hA δ P hP α hα hlow
    have hA2 := hA₂ A hA
    have hA0 : 0 < A := by linarith
    have hρ : 0 < A ^ (-(Cs : ℝ)) := Real.rpow_pos_of_pos hA0 _
    have hTinv : 0 < (A ^ k)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hA0 k)
    have hαn : ‖α‖ ≤ 1 / 8 := by simpa using hα
    have hαc : ‖emb α‖ ≤ 1 := by rw [emb_norm_geo]; linarith
    have hlow' : A ^ (-(Cs : ℝ)) ≤ ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖ := by
      rw [← eval_disc_eq_qdisc P hP.1]
      change A ^ (-(Cs : ℝ)) ≤ ‖eval (fun i => (α i : ℂ)) ((disc P).map (algebraMap ℝ ℂ))‖
      rwa [hreal]
    have hd0 : qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlow'
      linarith
    refine ⟨?_, ?_⟩
    · intro h0
      apply hd0
      simp [h0, qdisc, qb, qc, qg]
    · intro ζ hζ
      have hlocal := (hscale A hA).2.2
      have hAinv : A⁻¹ ≤ (1 / 2 : ℝ) := by
        calc A⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hA0 (by norm_num)).mpr hA2
             _ = _ := by norm_num
      have hdist : dist ζ (emb α) < (A ^ k)⁻¹ := mem_ball.mp hζ
      have hζn : ‖ζ‖ ≤ 1 := by
        have hh := norm_add_le (ζ - emb α) (emb α)
        rw [sub_add_cancel, emb_norm_geo] at hh
        rw [dist_eq_norm] at hdist
        linarith
      have hlip := hLip A (disc P) hA0.le hP.2.2.1 hP.2.2.2 ζ (emb α) hζn hαc
      rw [eval_disc_eq_qdisc P hP.1, eval_disc_eq_qdisc P hP.1] at hlip
      calc
        _ ≤ L * A * dist ζ (emb α) := hlip
        _ < L * A * (A ^ k)⁻¹ := mul_lt_mul_of_pos_left hdist (mul_pos hL hA0)
        _ < A * A * (A ^ k)⁻¹ := by
          have hh := mul_lt_mul_of_pos_right (show L < A by linarith [hLA A hA])
            (mul_pos hA0 hTinv)
          simpa only [mul_assoc] using hh
        _ = A ^ (-(Cs : ℝ)) := hpower A hA
        _ ≤ _ := hlow'
  refine ⟨k, A₀, {
    exponent := hk
    scale := hscale
    degree := degree_map_le
    qc := ?_
    real_eval := hreal
    disc := hdisc
    root_deriv := hroot
    anchor := hanchor
    sqrt := ?_ }⟩
  · intro A δ P hP
    rw [qc_map_real, Complex.norm_real, Real.norm_eq_abs]
    exact hP.2.1
  · intro A hA δ P P' hP hP' z α σ hsafe
    have hA0 : 0 < A := by linarith [hA₂ A hA]
    have hρ : 0 < A ^ (-(Cs : ℝ)) := Real.rpow_pos_of_pos hA0 _
    have hTinv : 0 < (A ^ k)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hA0 k)
    have hsqrt : ∀ R : Test, ScaleTest A δ R →
        (∀ ζ ∈ thickening (A ^ (-(Cs : ℝ))) (safePath z α σ),
          A ^ (-(Cs : ℝ)) ≤ ‖eval (fun i => ζ i) ((disc R).map (algebraMap ℝ ℂ))‖) →
        ∃ S : E3 → ℂ, AnalyticOnNhd ℂ S (thickening (A ^ k)⁻¹ (safePath z α σ)) ∧
          ∀ ζ ∈ thickening (A ^ k)⁻¹ (safePath z α σ),
            S ζ ^ 2 = qdisc (R.map (algebraMap ℝ ℂ)) (fun i => ζ i) ∧
            qdisc (R.map (algebraMap ℝ ℂ)) (fun i => ζ i) ≠ 0 := by
      intro R hR hlow
      apply sqrt_on_broken_tube (R.map (algebraMap ℝ ℂ)) (emb z)
        (emb z + σ • (emb α - emb z)) (emb α) hTinv
      intro ζ hζ h0
      have hh := hlow ζ ((thickening_mono (hinvρ A hA) (safePath z α σ)) hζ)
      rw [eval_disc_eq_qdisc R hR.1, h0, norm_zero] at hh
      linarith
    obtain ⟨S, hS⟩ := hsqrt P hP (fun ζ hζ => (hsafe ζ hζ).1)
    obtain ⟨S', hS'⟩ := hsqrt P' hP' (fun ζ hζ => (hsafe ζ hζ).2)
    exact ⟨S, S', hS, hS'⟩

end Submission.Obl.k4_pair_anchor_jet_bins
