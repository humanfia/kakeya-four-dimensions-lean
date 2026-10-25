import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineClustering

/-! The affine clustering estimate is uniform over a compact positive depth range. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical ENNReal

theorem small_bins_bound_affine_occupation_uniform_depth (d ε R : ℝ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hε : 0 < ε) (hR : 1 ≤ R) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
      ∀ (X : Type) [MeasurableSpace X]
        (μ : Measure (X × ℝ)) [IsFiniteMeasure μ] (θ : Measure X) [SFinite θ]
        (ν : Measure X) (π : Measure ℝ) [IsProbabilityMeasure π]
        (a : X → Fin 5 → ℝ), Measurable a →
        ∀ (A E : Set (X × ℝ)), MeasurableSet A → MeasurableSet E →
        ∀ (K D L τ : ℝ), 0 ≤ K → 0 ≤ D → 0 ≤ L → 0 < τ →
        ∀ (q₀ c : ℤ) (p Cdom : ℝ≥0∞), p ≠ 0 → p ≠ ∞ →
        (∀ z ∈ A, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K) →
        μ.restrict A ≤ ENNReal.ofReal D • θ.prod volume →
        (physicalScalarGridTag (N ^ (-s)) '' (scalarPacketPosition a '' A)).Finite →
        (∀ z ∈ A, ENNReal.ofReal τ * π (scalarVelocityBin (N ^ (-s)) ⌊a z.1 1 / N ^ (-s)⌋) ≤
          μ (A ∩ {z' | physicalScalarGridTag (N ^ (-s)) (scalarPacketPosition a z') =
            physicalScalarGridTag (N ^ (-s)) (scalarPacketPosition a z) ∧
            a z'.1 1 ∈ scalarVelocityBin (N ^ (-s)) ⌊a z.1 1 / N ^ (-s)⌋})) →
        (∀ z ∈ E, z ∈ A ∧ a z.1 0 ∈ scalarVelocityBin (N ^ (-s)) q₀ ∧
          a z.1 1 ∈ scalarVelocityBin (N ^ (-s)) c) →
        (∀ q : ℤ, θ {l | a l 0 ∈ scalarVelocityBin (N ^ (-s)) q ∧
          a l 1 ∈ scalarVelocityBin (N ^ (-s)) c} ≤
            ENNReal.ofReal L * π (scalarVelocityBin (N ^ (-s)) c)) →
        (ν.prod volume).restrict E ≤ Cdom • μ.restrict E →
        3 * K ≤ N ^ η → ν Set.univ ≤ p * ENNReal.ofReal (N ^ η) →
        (D * (4 * (K + 3) + 2) * L) / τ ≤ N ^ η * (N ^ (-s)) ^ (-1 - d) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-s) ≤ r →
          ν {l | boundedScalarHiddenCoefficients K (a l) ∈ Metric.ball b r} ≤
            p * ENNReal.ofReal (N ^ η * r ^ d)) →
        (∀ q : Fin 3 → ℤ, ν {l | ∀ j : Fin 3,
          (⌊boundedScalarHiddenCoefficients K (a l) j / N ^ (-s)⌋ : ℤ) = q j} <
            p * ENNReal.ofReal (N ^ (-s * d - ε))) →
        (ν.prod volume) E < p * ENNReal.ofReal (N ^ (-η)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨η,hη,Q₀,hQ₀,hcore⟩ := small_bins_bound_affine_occupation d (ε / R)
    hd hd₁ (div_pos hε hRp)
  have hevent : ∀ᶠ N : ℝ in atTop, Q₀ ≤ N ^ R⁻¹ :=
    (tendsto_rpow_atTop (inv_pos.mpr hRp)).eventually (eventually_ge_atTop Q₀)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hevent
  refine ⟨η / R,div_pos hη hRp,max 2 N₁,le_max_left _ _,?_⟩
  intro N hN s hs hs' X _ μ _ θ _ ν π _ a ha A E hA hE K D L τ hK hD hL hτ
    q₀ c p Cdom hp₀ hpt hpoint hdom hfinite hfloor hEA hprior hProductDom
    hnorm htotal hsize hball hbin
  have hN₂ : 2 ≤ N := (le_max_left _ _).trans hN
  have hN₁' : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  let Q : ℝ := N ^ s
  have hQ : Q₀ ≤ Q := (hN₁ N ((le_max_right _ _).trans hN)).trans
    (Real.rpow_le_rpow_of_exponent_le hN₁' hs)
  have hmesh : Q ^ (-1 : ℝ) = N ^ (-s) := by
    dsimp only [Q]
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hnorm' : N ^ (η / R) ≤ Q ^ η := by
    dsimp only [Q]
    rw [← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN₁'
    have hh := mul_le_mul_of_nonneg_right hs hη.le
    rw [inv_mul_eq_div] at hh
    nlinarith only [hh]
  have hnegative : Q ^ (-η) ≤ N ^ (-(η / R)) := by
    dsimp only [Q]
    rw [← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN₁'
    have hh := mul_le_mul_of_nonneg_right hs hη.le
    rw [inv_mul_eq_div] at hh
    nlinarith only [hh]
  have hlight : N ^ (-s * d - ε) ≤ Q ^ (-d - ε / R) := by
    dsimp only [Q]
    rw [← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN₁'
    have hh := mul_le_mul_of_nonneg_right hs' (div_nonneg hε.le hRp.le)
    have heq : R * (ε / R) = ε := by field_simp
    nlinarith only [hh,heq]
  have hcore' := hcore Q hQ X μ θ ν π a ha A E hA hE K D L τ hK hD hL hτ
    q₀ c p Cdom hp₀ hpt
  rw [hmesh] at hcore'
  have hout := hcore' hpoint hdom hfinite hfloor hEA hprior hProductDom
    (hnorm.trans hnorm')
    (htotal.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hnorm')))
    (hsize.trans (mul_le_mul_of_nonneg_right hnorm' (Real.rpow_nonneg (by positivity) _)))
    (fun b r hr => (hball b r hr).trans (mul_le_mul' le_rfl
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hnorm'
        (Real.rpow_nonneg ((Real.rpow_pos_of_pos hNp _).le.trans hr) _)))))
    (fun q => (hbin q).trans_le (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlight)))
  exact hout.trans_le (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hnegative))

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
