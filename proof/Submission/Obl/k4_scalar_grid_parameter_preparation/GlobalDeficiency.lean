import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineDeficiency
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineMassSummation

/-! Deficient original coefficient bins have small total incidence mass. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical ENNReal

theorem deficient_coefficient_mass (d ε R : ℝ)
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
      μ {z | z ∈ A ∧ z.1 ∈ scalarLightCoefficientSet θ a π (N ^ (-s)) d (N ^ (-ε))} ≤
        ENNReal.ofReal (6 * B * D * N ^ (-η)) := by
  obtain ⟨η,hη,N₀,hN₀,hcore⟩ := deficient_affine_mass d ε R hd hd₁ hε hR
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN s hs hs' X _ μ _ θ _ π _ a ha A hA B D H σ τ c₀ hB hD hH hσ
    hξσ hσ₁ hτ hc₀ hbounded hpoint hdom hlo hfinite hfloor hcap hnorm hQ hsize
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hsp : 0 < s := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hs
  let ξ := N ^ (-s)
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNp _
  have hξ₁ : ξ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith)
  let E := {z : X × ℝ | z ∈ A ∧ z.1 ∈ scalarLightCoefficientSet θ a π ξ d (N ^ (-ε))}
  have hcell (q c : ℤ) :
      μ {z | z ∈ E ∧ (⌊a z.1 0 / ξ⌋ : ℤ) = q ∧ (⌊a z.1 1 / ξ⌋ : ℤ) = c} ≤
        ENNReal.ofReal (ξ * (D * N ^ (-η))) * π (scalarVelocityBin ξ c) := by
    have he : {z : X × ℝ | z ∈ E ∧ (⌊a z.1 0 / ξ⌋ : ℤ) = q ∧ (⌊a z.1 1 / ξ⌋ : ℤ) = c} =
        {z | z ∈ A ∧ z.1 ∈ scalarLightCoefficientSet θ a π ξ d (N ^ (-ε)) ∩
          scalarAffineCoefficientCell a ξ q c} := by
      ext z
      simp only [E,scalarAffineCoefficientCell,scalarVelocityBin,Set.mem_setOf_eq,Set.mem_inter_iff]
      tauto
    rw [he]
    have hh := hcore N hN s hs hs' X μ θ π a ha A hA B D H σ τ c₀ hB hD hH hσ
      hξσ hσ₁ hτ hc₀ hbounded hpoint hdom hlo hfinite hfloor hcap hnorm hQ hsize q c
    apply hh.trans_eq
    congr 1
    congr 1
    ring
  have hmass := affine_cell_mass_sum μ π a E ξ B (D * N ^ (-η)) hξ hξ₁ hB
    (mul_nonneg hD (Real.rpow_nonneg hNp.le _))
    (fun z hz => ⟨(hpoint z hz.1).2 0,(hpoint z hz.1).2 1⟩) hcell
  apply hmass.trans_eq
  congr 1
  ring

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
