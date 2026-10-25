import Submission.Obl.k4_scalar_grid_parameter_preparation.UniformAffineClustering
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineFrostman
import Submission.Obl.k4_scalar_grid_parameter_preparation.PriorComparability

/-! Original incidence mass in deficient coefficient bins inside one visible affine bin. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical ENNReal

theorem deficient_affine_mass (d ε R : ℝ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hε : 0 < ε) (hR : 1 ≤ R) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
      ∀ (X : Type) [MeasurableSpace X] (μ : Measure (X × ℝ)) [IsFiniteMeasure μ]
        (θ : Measure X) [SFinite θ] (π : Measure ℝ) [IsProbabilityMeasure π]
        (a : X → Fin 5 → ℝ), Measurable a →
      ∀ (A : Set (X × ℝ)), MeasurableSet A →
      ∀ (B D H σ τ c₀ : ℝ), 1 ≤ B → 0 ≤ D → 0 ≤ H →
        0 < σ → N ^ (-s) ≤ σ → σ ≤ 1 → 0 < τ → 0 < c₀ →
      (∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B) →
      (∀ z ∈ A, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ B) →
      μ.restrict A ≤ ENNReal.ofReal D • θ.prod volume →
      ENNReal.ofReal c₀ • (θ.prod volume).restrict A ≤ μ.restrict A →
      (physicalScalarGridTag (N ^ (-s)) '' (scalarPacketPosition a '' A)).Finite →
      (∀ z ∈ A, ENNReal.ofReal τ * π (scalarVelocityBin (N ^ (-s)) ⌊a z.1 1 / N ^ (-s)⌋) ≤
        μ (A ∩ {z' | physicalScalarGridTag (N ^ (-s)) (scalarPacketPosition a z') =
          physicalScalarGridTag (N ^ (-s)) (scalarPacketPosition a z) ∧
          a z'.1 1 ∈ scalarVelocityBin (N ^ (-s)) ⌊a z.1 1 / N ^ (-s)⌋})) →
      (∀ ζ : ℝ, N ^ (-s) ≤ ζ → ζ ≤ σ → ∀ z : Fin 5 → ℤ,
        θ {l | scalarMixedCoefficientTag (N ^ (-s)) ζ (a l) = z} ≤
          ENNReal.ofReal (H * N ^ (-s) * ζ ^ d) * π (scalarVelocityBin (N ^ (-s)) (z 1))) →
      3 * B ≤ N ^ η → (6 * B / σ) ^ 3 * H ≤ N ^ η →
      (D * (4 * (B + 3) + 2) * (((6 * B / σ) ^ 3 * H) * N ^ (-s))) / τ ≤
        N ^ η * (N ^ (-s)) ^ (-1 - d) →
      ∀ q c : ℤ,
        μ {z | z ∈ A ∧ z.1 ∈ scalarLightCoefficientSet θ a π (N ^ (-s)) d (N ^ (-ε)) ∩
          scalarAffineCoefficientCell a (N ^ (-s)) q c} ≤
            ENNReal.ofReal (D * N ^ (-s) * N ^ (-η)) * π (scalarVelocityBin (N ^ (-s)) c) := by
  obtain ⟨η,hη,N₀,hN₀,hcore⟩ := small_bins_bound_affine_occupation_uniform_depth
    d ε R hd hd₁ hε hR
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN s hs hs' X _ μ _ θ _ π _ a ha A hA B D H σ τ c₀ hB hD hH hσ
    hξσ hσ₁ hτ hc₀ hbounded hpoint hdom hlo hfinite hfloor hcap hnorm hQ hsize q c
  have hNp : 0 < N := by linarith
  let ξ := N ^ (-s)
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNp _
  let Q := (6 * B / σ) ^ 3 * H
  let S := scalarLightCoefficientSet θ a π ξ d (N ^ (-ε)) ∩
    scalarAffineCoefficientCell a ξ q c
  let ν := θ.restrict S
  let E := {z : X × ℝ | z ∈ A ∧ z.1 ∈ S}
  let p := ENNReal.ofReal ξ * π (scalarVelocityBin ξ c)
  have hS : MeasurableSet S :=
    (measurableSet_scalarLightCoefficientSet θ a ha π ξ d _).inter
      (measurableSet_scalarAffineCoefficientCell ha ξ q c)
  have hE : MeasurableSet E := hA.inter (hS.preimage measurable_fst)
  have hEA : E ⊆ A := fun _ hz => hz.1
  have hES : E ⊆ S ×ˢ Set.univ := fun _ hz => ⟨hz.2,Set.mem_univ _⟩
  have hνθ : ν ≤ θ := Measure.restrict_le_self
  have hνAff : ν ≤ θ.restrict (scalarAffineCoefficientCell a ξ q c) :=
    Measure.restrict_mono_set _ (fun _ hl => hl.2)
  have hfrost := restricted_affine_prior_frostman θ ν a ha π ξ σ B H d hξ hσ hξσ hσ₁
    hB hH hd q c hbounded hνAff hcap
  change ν Set.univ ≤ p * ENNReal.ofReal Q ∧ _ at hfrost
  have hupper : μ E ≤ ENNReal.ofReal D * (ν.prod volume) E := by
    have hh := hdom E
    rw [Measure.restrict_apply hE,Set.inter_eq_left.mpr hEA] at hh
    have heq : (ν.prod volume) E = (θ.prod volume) E := by
      dsimp only [ν]
      rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply hE,
        Set.inter_eq_left.mpr hES]
    simpa only [Measure.smul_apply,smul_eq_mul,← heq] using hh
  change μ E ≤ ENNReal.ofReal (D * ξ * N ^ (-η)) * π (scalarVelocityBin ξ c)
  by_cases hπ : π (scalarVelocityBin ξ c) = 0
  · have hz : ν Set.univ = 0 := by
      have hh : ν Set.univ ≤ (0 : ℝ≥0∞) := by
        simpa only [p,hπ,mul_zero,zero_mul] using hfrost.1
      exact le_antisymm hh zero_le
    have hνzero : ν = 0 := Measure.measure_univ_eq_zero.mp hz
    have hμzero : μ E = 0 := by simpa only [hνzero,Measure.zero_prod,Measure.coe_zero,
      Pi.zero_apply,mul_zero,nonpos_iff_eq_zero] using hupper
    rw [hμzero,hπ,mul_zero]
  have hp₀ : p ≠ 0 := mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hξ) hπ
  have hpt : p ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top π _)
  have hprior (q' : ℤ) :
      θ {l | a l 0 ∈ scalarVelocityBin ξ q' ∧ a l 1 ∈ scalarVelocityBin ξ c} ≤
        ENNReal.ofReal (Q * ξ) * π (scalarVelocityBin ξ c) := by
    have hh := (restricted_affine_prior_frostman θ
      (θ.restrict (scalarAffineCoefficientCell a ξ q' c)) a ha π ξ σ B H d hξ hσ hξσ hσ₁
      hB hH hd q' c hbounded le_rfl hcap).1
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
    apply hh.trans_eq
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Q)]
    dsimp only [Q]
    ring
  have hProductDom : (ν.prod volume).restrict E ≤
      (ENNReal.ofReal c₀)⁻¹ • μ.restrict E :=
    subprior_product_restriction_domination θ ν μ A E hEA hνθ (ENNReal.ofReal c₀)
      (ENNReal.ofReal_ne_zero_iff.mpr hc₀) ENNReal.ofReal_ne_top hlo
  have hbin (b : Fin 3 → ℤ) :
      ν {l | ∀ j : Fin 3, (⌊boundedScalarHiddenCoefficients B (a l) j / ξ⌋ : ℤ) = b j} <
        p * ENNReal.ofReal (N ^ (-s * d - ε)) := by
    have hh := restricted_light_affine_hidden_bin_cap θ ν a ha π ξ B d (N ^ (-ε)) hξ
      (Real.rpow_pos_of_pos hNp _) q c hbounded hπ le_rfl b
    have heq : ξ ^ (1 + d) * N ^ (-ε) = ξ * N ^ (-s * d - ε) := by
      dsimp only [ξ]
      rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp,← Real.rpow_add hNp]
      congr 1
      ring
    rw [heq,ENNReal.ofReal_mul hξ.le] at hh
    have hre : ENNReal.ofReal ξ * ENNReal.ofReal (N ^ (-s * d - ε)) * π (scalarVelocityBin ξ c) =
        p * ENNReal.ofReal (N ^ (-s * d - ε)) := by dsimp only [p]; ring
    simpa only [Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,funext_iff]
      using hh.trans_eq hre
  have hout := hcore N hN s hs hs' X μ θ ν π a ha A E hA hE B D (Q * ξ) τ
    (zero_le_one.trans hB) hD (by dsimp only [Q]; positivity) hτ q c p
    (ENNReal.ofReal c₀)⁻¹ hp₀ hpt hpoint hdom hfinite hfloor
    (fun z hz => ⟨hz.1,hz.2.2.1,hz.2.2.2⟩) hprior hProductDom hnorm
    (hfrost.1.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hQ))) hsize
    (fun b r hr => (hfrost.2 b r hr).trans (mul_le_mul' le_rfl
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hQ
        (Real.rpow_nonneg (hξ.le.trans hr) _))))) hbin
  have hfinal := hupper.trans (mul_le_mul' le_rfl hout.le)
  apply hfinal.trans_eq
  rw [ENNReal.ofReal_mul (mul_nonneg hD hξ.le),ENNReal.ofReal_mul hD]
  dsimp only [p]
  ring

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
