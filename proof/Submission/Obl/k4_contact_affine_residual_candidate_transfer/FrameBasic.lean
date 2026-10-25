import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameLaw
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Model

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory ProbabilityTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- Concrete per-frame bounds used to install the normalized basic model.
All mass comparisons still refer to the original source and parent prior. -/
structure FrameBasicBounds {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ}
    {s₀ U' : ℝ} (f : Frame D k s₀ U') (K' : ℝ) : Prop where
  parent_meas : MeasurableSet f.parentSet
  parent_pos : D.ν k f.parentSet ≠ 0
  core_parent : f.core ⊆ f.event 0 f.i₀ f.u₀
  density_bound : D.K k ≤ K'
  native_bound : f.H ≤ K'
  prior_bound : ∀ᵐ l ∂cond (D.ν k) f.parentSet,
    |f.coeff l 0| + |f.coeff l 1| + |f.coeff l 3| + |f.coeff l 4| ≤ K'
  residual_mass : ENNReal.ofReal K'⁻¹ * f.scale ≤ D.ρ k f.core

/-- The actual normalized model satisfies all frozen basic hypotheses once
the original frame bounds have been established. -/
theorem residualBase_basic {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic)
    (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ) (frames : (k : ℕ) → Option (Frame D k s₀ U'))
    (hK' : ∀ k, 1 ≤ K' k)
    (hframes : ∀ k f, frames k = some f → FrameBasicBounds f (K' k)) :
    (residualBase D s₀ U' e₀' K' frames).Basic := by
  intro k
  letI : IsProbabilityMeasure (D.ν k) := (h1 k).2.1
  have hK : 1 ≤ K' k := hK' k
  have hK₀ : 0 ≤ K' k := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hKi : (K' k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  cases hf : frames k with
  | none =>
    let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
    letI : IsProbabilityMeasure dt := ⟨by simp [dt, Real.volume_Icc]⟩
    have hdom : (D.ν k).prod dt ≤ ENNReal.ofReal (K' k) • (D.ν k).prod volume := by
      have hh : (D.ν k).prod dt ≤ (D.ν k).prod volume :=
        Measure.prod_mono le_rfl Measure.restrict_le_self
      intro E
      refine (hh E).trans ?_
      rw [Measure.smul_apply, smul_eq_mul]
      have hscalar : (1 : ENNReal) ≤ ENNReal.ofReal (K' k) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hK
      simpa only [one_mul] using mul_le_mul' hscalar (le_refl (((D.ν k).prod volume) E))
    have hsupport : ((D.ν k).prod dt) (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
      have heq : (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ))ᶜ = univ ×ˢ (Icc (0 : ℝ) 1)ᶜ := by
        ext x
        simp
      rw [heq, Measure.prod_prod]
      simp [dt, Measure.restrict_apply measurableSet_Icc.compl]
    have hmass : ENNReal.ofReal ((K' k)⁻¹) ≤ ((D.ν k).prod dt) univ := by
      simpa only [measure_univ, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hKi
    simp only [residualBase, hf, Data.x]
    refine ⟨measurable_const, inferInstance, (h1 k).2.2.1, hdom, le_rfl, hsupport,
      hmass, (totalDegree_X (3 : Fin 4)).le.trans (by norm_num), ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun _ => by simpa using hK₀
    · exact Filter.Eventually.of_forall fun _ => by
        simp [point, pderiv_X, hK, hK₀, hKi]
  | some f =>
    have h := hframes k f hf
    letI : IsProbabilityMeasure (cond (D.ν k) f.parentSet) :=
      ProbabilityTheory.cond_isProbabilityMeasure h.parent_pos
    have hN : 0 < D.N k := lt_of_lt_of_le (by norm_num) (p.scale k)
    have hOldK : 0 ≤ D.K k := (by norm_num : (0 : ℝ) ≤ 1).trans (p.subpower.1 k)
    have hcoreA : f.core ⊆ f.parentSet ×ˢ (univ : Set ℝ) :=
      fun _ hx => ⟨(h.core_parent hx).1, mem_univ _⟩
    have hdom₀ := f.resμ_domination hOldK h.parent_pos hcoreA (h1 k).2.2.2.1
    have hdom : f.resμ ≤ ENNReal.ofReal (K' k) • ((cond (D.ν k) f.parentSet).prod volume) := by
      intro E
      refine (hdom₀ E).trans ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal h.density_bound) le_rfl
    have hprior : ∀ᵐ l ∂cond (D.ν k) f.parentSet, l ∈ f.parentSet :=
      Measure.ae_smul_measure (ae_restrict_mem h.parent_meas) ((D.ν k) f.parentSet)⁻¹
    have hprod : ∀ᵐ x ∂(cond (D.ν k) f.parentSet).prod (volume : Measure ℝ),
        x.1 ∈ f.parentSet :=
      (Measure.quasiMeasurePreserving_fst
        (μ := cond (D.ν k) f.parentSet) (ν := (volume : Measure ℝ))).ae hprior
    have hsource : ∀ᵐ x ∂f.resμ, x.1 ∈ f.parentSet :=
      ae_mono hdom₀ (Measure.ae_smul_measure hprod (ENNReal.ofReal (D.K k)))
    have hscale : f.scale ≠ 0 := by
      unfold Frame.scale
      exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr f.q₀_pos).ne' h.parent_pos).ne'
    have hscale_top : f.scale ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (D.ν k) f.parentSet)
    have hmass : ENNReal.ofReal ((K' k)⁻¹) ≤ f.resρ univ :=
      f.resρ_mass_floor hscale hscale_top h.residual_mass
    simp only [residualBase, hf, Data.x]
    refine ⟨f.measurable_coeff (h1 k).1, inferInstance, (h1 k).2.2.1, hdom,
      f.resρ_le_resμ (h1 k).2.2.2.2.1, f.resμ_unit_support h.parent_pos h.core_parent,
      hmass, (totalDegree_X (3 : Fin 4)).le.trans (by norm_num), h.prior_bound, ?_⟩
    filter_upwards [hsource] with x hx
    constructor
    · intro t ht
      have hv := (f.parent_residual_bound hN x.1 hx t ht).trans h.native_bound
      simpa [pderiv_X, point] using And.intro hv (And.intro hK hK₀)
    · simpa [pderiv_X] using hKi

theorem residualData_basic {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic)
    (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ) (frames : (k : ℕ) → Option (Frame D k s₀ U'))
    (hK' : ∀ k, 1 ≤ K' k)
    (hframes : ∀ k f, frames k = some f → FrameBasicBounds f (K' k)) :
    (residualData D s₀ U' e₀' K' frames).Basic :=
  residualBase_basic D p h1 s₀ U' e₀' K' frames hK' hframes

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
