/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineClustering.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineConditionalSupport
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScaledClustering
import Submission.Obl.k4_scalar_grid_parameter_preparation.BoundedHiddenCoefficients
import Submission.Obl.k4_scalar_grid_parameter_preparation.PositiveCodeCore

/-! Conditional support and scalar clustering bound one original affine group's occupation. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical ENNReal

theorem small_bins_bound_affine_occupation (d ε : ℝ) (hd : 0 ≤ d) (hd₁ : d < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (X : Type) [MeasurableSpace X]
        (μ : Measure (X × ℝ)) [IsFiniteMeasure μ] (θ : Measure X) [SFinite θ]
        (ν : Measure X) (π : Measure ℝ) [IsProbabilityMeasure π]
        (a : X → Fin 5 → ℝ), Measurable a →
        ∀ (A E : Set (X × ℝ)), MeasurableSet A → MeasurableSet E →
        ∀ (K D L τ : ℝ), 0 ≤ K → 0 ≤ D → 0 ≤ L → 0 < τ →
        ∀ (q₀ c : ℤ) (p Cdom : ℝ≥0∞), p ≠ 0 → p ≠ ∞ →
        (∀ z ∈ A, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K) →
        μ.restrict A ≤ ENNReal.ofReal D • θ.prod volume →
        (physicalScalarGridTag (N ^ (-1 : ℝ)) '' (scalarPacketPosition a '' A)).Finite →
        (∀ z ∈ A, ENNReal.ofReal τ * π (scalarVelocityBin (N ^ (-1 : ℝ)) ⌊a z.1 1 / N ^ (-1 : ℝ)⌋) ≤
          μ (A ∩ {z' | physicalScalarGridTag (N ^ (-1 : ℝ)) (scalarPacketPosition a z') =
            physicalScalarGridTag (N ^ (-1 : ℝ)) (scalarPacketPosition a z) ∧
            a z'.1 1 ∈ scalarVelocityBin (N ^ (-1 : ℝ)) ⌊a z.1 1 / N ^ (-1 : ℝ)⌋})) →
        (∀ z ∈ E, z ∈ A ∧ a z.1 0 ∈ scalarVelocityBin (N ^ (-1 : ℝ)) q₀ ∧
          a z.1 1 ∈ scalarVelocityBin (N ^ (-1 : ℝ)) c) →
        (∀ q : ℤ, θ {l | a l 0 ∈ scalarVelocityBin (N ^ (-1 : ℝ)) q ∧
          a l 1 ∈ scalarVelocityBin (N ^ (-1 : ℝ)) c} ≤
            ENNReal.ofReal L * π (scalarVelocityBin (N ^ (-1 : ℝ)) c)) →
        (ν.prod volume).restrict E ≤ Cdom • μ.restrict E →
        3 * K ≤ N ^ η → ν Set.univ ≤ p * ENNReal.ofReal (N ^ η) →
        (D * (4 * (K + 3) + 2) * L) / τ ≤ N ^ η * (N ^ (-1 : ℝ)) ^ (-1 - d) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-1 : ℝ) ≤ r →
          ν {l | boundedScalarHiddenCoefficients K (a l) ∈ Metric.ball b r} ≤
            p * ENNReal.ofReal (N ^ η * r ^ d)) →
        (∀ q : Fin 3 → ℤ, ν {l | ∀ j : Fin 3,
          (⌊boundedScalarHiddenCoefficients K (a l) j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} <
            p * ENNReal.ofReal (N ^ (-d - ε))) →
        (ν.prod volume) E < p * ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η,hη,N₀,hN₀,hclust⟩ := small_coefficient_bins_force_small_original_occupation d ε hd hd₁ hε
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN X _ μ _ θ _ ν π _ a ha A E hA hE K D L τ hK hD hL hτ q₀ c p Cdom hp₀ hpt
    hpoint hdom hfinite hfloor hEA hprior hProductDom hnorm htotal hsize hball hbin
  have hNpos : 0 < N := by linarith
  have hξ : 0 < N ^ (-1 : ℝ) := Real.rpow_pos_of_pos hNpos _
  let code := fun z : X × ℝ => physicalScalarGridTag (N ^ (-1 : ℝ)) (scalarPacketPosition a z)
  have hcode : Measurable code := by
    apply Measurable.of_eval
    intro e
    dsimp only [code,physicalScalarGridTag]
    have hm := measurable_scalarPacketPosition ha
    fun_prop
  have hcell (q : Fin 3 → ℤ) : MeasurableSet {z | code z = q} :=
    measurableSet_eq_fun hcode measurable_const
  have hs := affine_conditional_physical_support μ θ π a ha A E hA
    (N ^ (-1 : ℝ)) K D L τ hξ hK hD hL hτ hpoint hdom hfinite hfloor q₀ c hEA hprior
  let Q := {q : Fin 3 → ℤ | (μ.restrict E) {z | code z = q} ≠ 0}
  have hQ : Q.Finite := hs.1
  have hfinE : (code '' E).Finite := by
    have hh := hfinite.subset (Set.image_mono (Set.image_mono (fun z hz => (hEA z hz).1)))
    simpa only [Set.image_image] using hh
  obtain ⟨G,hG,hGE,_,hLaw,hpos⟩ := exists_positive_code_core (ν.prod volume) E hE code hcell hfinE
  have hmem (z : X × ℝ) (hz : z ∈ G) : code z ∈ Q := by
    intro hzero
    have hh := hProductDom {z' | code z' = code z}
    simp only [Measure.smul_apply,smul_eq_mul,hzero,mul_zero] at hh
    exact (hpos z hz) (le_antisymm hh bot_le)
  let F : Finset (ℤ × ℤ) := hQ.toFinset.image fun q => (q 0,q 2)
  have hFsize : (F.card : ℝ) ≤ N ^ η * (N ^ (-1 : ℝ)) ^ (-1 - d) := by
    calc
      _ ≤ (hQ.toFinset.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (Q.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card _ hQ]
      _ ≤ (D * (4 * (K + 3) + 2) * L) / τ := hs.2
      _ ≤ _ := hsize
  have hFcover : ∀ l t, (l,t) ∈ G →
      (⌊t / N ^ (-1 : ℝ)⌋,
        ⌊(boundedScalarHiddenCoefficients K (a l) 0 + t * boundedScalarHiddenCoefficients K (a l) 1 +
          t ^ 2 * boundedScalarHiddenCoefficients K (a l) 2) / N ^ (-1 : ℝ)⌋) ∈ F := by
    intro l t hlt
    apply Finset.mem_image.mpr
    refine ⟨code (l,t),hQ.mem_toFinset.mpr (hmem (l,t) hlt),?_⟩
    have he := boundedScalarHiddenCoefficients_eq (hpoint (l,t) (hEA (l,t) (hGE hlt)).1).2
    simp [code,physicalScalarGridTag,scalarPacketPosition,he,scalarHiddenCoefficients,scalarX]
  have hout := hclust N hN X ν (fun l => boundedScalarHiddenCoefficients K (a l)) G F p hp₀ hpt
    ((measurable_boundedScalarHiddenCoefficients K).comp ha) hG
    (fun z hz => ⟨Set.mem_univ _,(hpoint z (hEA z (hGE hz)).1).1⟩)
    (fun l => (norm_boundedScalarHiddenCoefficients_le hK (a l)).trans hnorm)
    htotal hFsize hFcover hball hbin
  have he : (ν.prod volume) G = (ν.prod volume) E := by
    have hh := congrArg (fun m : Measure (X × ℝ) => m Set.univ) hLaw
    simpa only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hh
  rwa [he] at hout

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
