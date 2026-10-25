import Submission.Obl.k4_quadratic_discriminant_safe_paths.FiberEstimate
import Submission.Obl.k4_quadratic_discriminant_safe_paths.ProductEstimate
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Scales

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

/-- The remaining real-variable input: a source value controls the volume of
small anchor values at a sufficiently small fixed inverse-power threshold. -/
def AnchorBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ n : ℕ, 1 ≤ n ∧
    ∀ A : ℝ, 2 ≤ A → ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ 2 →
      ∀ a : RealSpace, ‖a‖ ≤ (1 : ℝ) / 8 →
        A⁻¹ ≤ |MvPolynomial.eval (fun i => a i) P| →
    volume {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
      |MvPolynomial.eval (fun i => x i) P| < K * (A ^ n)⁻¹} ≤
      ENNReal.ofReal (A⁻¹ / 4) * volume (closedBall (0 : RealSpace) (1 / 8))

theorem safe_paths_from_anchor_bound (hanchor : AnchorBound) :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℝ, 2 ≤ A →
    ∀ P P' : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ 2 → P'.totalDegree ≤ 2 →
      (∀ d, |P.coeff d| ≤ A) → (∀ d, |P'.coeff d| ≤ A) →
    ∀ a : RealSpace, ‖a‖ ≤ (1 : ℝ) / 8 →
      A⁻¹ ≤ |MvPolynomial.eval (fun i => a i) P| →
      A⁻¹ ≤ |MvPolynomial.eval (fun i => a i) P'| →
    MeasurableSet (badSet a P P' (A ^ (-(C : ℝ)))) ∧
      (volume.prod volume) (badSet a P P' (A ^ (-(C : ℝ)))) ≤
        ENNReal.ofReal A⁻¹ * (volume.prod volume)
          (closedBall (0 : RealSpace) (1 / 8) ×ˢ closedBall (1 / 2 : ℂ) (1 / 4)) := by
  obtain ⟨K, hK, n, hn, hanchor⟩ := hanchor
  let k := min K 1
  have hk : 0 < k := lt_min hK zero_lt_one
  have hkK : k ≤ K := min_le_left _ _
  have hk1 : k ≤ 1 := min_le_right _ _
  obtain ⟨L, hL, hLip⟩ := exists_quadratic_lipschitz
  obtain ⟨J, hJ, hJhalf, hdetour⟩ := exists_detour_scale
  obtain ⟨C, hC, hscales⟩ := exists_power_radius L k J hL.le hk hJ n
  refine ⟨C, hC, ?_⟩
  intro A hA P P' hP hP' hcoeff hcoeff' a ha hsource hsource'
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  let r := A ^ (-(C : ℝ))
  let κ := k * (A ^ n)⁻¹
  let δ := J / A
  obtain ⟨hr, hscale⟩ := hscales A hA
  obtain ⟨hδ₀, hδ, hδvol⟩ := hdetour A hA
  have hκsource : κ ≤ A⁻¹ := by
    have hpow : A ≤ A ^ n := by
      simpa only [pow_one] using pow_le_pow_right₀ hAone hn
    calc
      κ ≤ 1 * (A ^ n)⁻¹ := mul_le_mul_of_nonneg_right hk1 (by positivity)
      _ = (A ^ n)⁻¹ := one_mul _
      _ ≤ A⁻¹ := inv_anti₀ hApos hpow
  have hsingle (R : MvPolynomial (Fin 3) ℝ) (hR : R.totalDegree ≤ 2)
      (hs : A⁻¹ ≤ |MvPolynomial.eval (fun i => a i) R|) :
      volume {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) R| < κ} ≤
        ENNReal.ofReal (A⁻¹ / 4) * volume (closedBall (0 : RealSpace) (1 / 8)) := by
    have hthreshold : κ ≤ K * (A ^ n)⁻¹ :=
      mul_le_mul_of_nonneg_right hkK (by positivity)
    have hsub : {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) R| < κ} ⊆
        {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
          |MvPolynomial.eval (fun i => x i) R| < K * (A ^ n)⁻¹} :=
      fun x hx => ⟨hx.1, hx.2.trans_le hthreshold⟩
    exact (measure_mono hsub).trans
      (hanchor A hA R hR a ha hs)
  refine ⟨measurableSet_badSet a P P' r, ?_⟩
  apply product_badSet_le_relative a P P' r κ (64 * δ) A⁻¹ (by positivity)
  · intro x hx hgood
    have hxnorm : ‖x‖ ≤ (1 : ℝ) / 8 := mem_closedBall_zero_iff.mp hx
    have hPx : κ ≤ |MvPolynomial.eval (fun i => x i) P| := by
      by_contra! h
      exact hgood ⟨hx, Or.inl h⟩
    have hPx' : κ ≤ |MvPolynomial.eval (fun i => x i) P'| := by
      by_contra! h
      exact hgood ⟨hx, Or.inr h⟩
    apply volume_good_anchor_fiber a x P P' hApos.le hL.le hr hP hP' hcoeff hcoeff'
      (fun R hR hcR => hLip A R hApos.le hR hcR) ha hxnorm hδ₀ hδ
      (hκsource.trans hsource) (hκsource.trans hsource') hPx hPx' hscale
  · exact anchorBad_volume_le_of_single P P' κ A⁻¹ (by positivity)
      (hsingle P hP hsource) (hsingle P' hP' hsource')
  · exact hδvol

end Submission.Obl.k4_quadratic_discriminant_safe_paths
