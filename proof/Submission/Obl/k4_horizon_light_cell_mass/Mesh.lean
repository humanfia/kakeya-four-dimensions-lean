import Submission.Obl.k4_horizon_light_cell_mass.Observation
import Submission.Obl.k4_horizon_light_cell_mass.CellCertificate

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_base_flattening (baseCoordinates ediff)

abbrev CellCode := (Fin 3 → ℤ) × ℤ

noncomputable def meshCode (ρ : Fin 3 → ℝ) (z : Observation) : CellCode :=
  (fun i => ⌊z.1 i / ρ i⌋, z.2)

lemma meshCode_measurable (ρ : Fin 3 → ℝ) : Measurable (meshCode ρ) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    dsimp [meshCode]
    fun_prop
  · exact measurable_snd

noncomputable def meshCorner (ρ : Fin 3 → ℝ) (c : CellCode) : Observation :=
  (WithLp.toLp 2 (fun i => ρ i * (c.1 i : ℝ)), c.2)

lemma meshCode_corner (ρ : Fin 3 → ℝ) (hρ : ∀ i, 0 < ρ i) (c : CellCode) :
    meshCode ρ (meshCorner ρ c) = c := by
  apply Prod.ext
  · funext i
    change ⌊ρ i * (c.1 i : ℝ) / ρ i⌋ = c.1 i
    have hh : ρ i * (c.1 i : ℝ) / ρ i = (c.1 i : ℝ) := by field_simp [(hρ i).ne']
    rw [hh, Int.floor_intCast]
  · rfl

lemma meshCode_volume (ρ : Fin 3 → ℝ) (hρ : ∀ i, 0 < ρ i) (c : CellCode) :
    reference (meshCode ρ ⁻¹' {c}) = ENNReal.ofReal (∏ i, ρ i) := by
  let T : Set Base := {z | ∀ i, ⌊z i / ρ i⌋ = c.1 i}
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hset : meshCode ρ ⁻¹' {c} = T ×ˢ {c.2} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, meshCode, Prod.mk.injEq,
      mem_prod, T, Set.mem_setOf_eq, Prod.ext_iff, funext_iff]
  rw [hset, reference, Measure.prod_prod, Measure.count_singleton, mul_one]
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hT.nullMeasurableSet]
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → Base) ⁻¹' T =
      Set.univ.pi (fun i => Set.Ico (ρ i * (c.1 i : ℝ))
        (ρ i * (c.1 i : ℝ) + ρ i)) := by
    ext x
    simp only [mem_preimage, T, mem_setOf_eq, mem_pi, mem_univ, forall_true_left,
      mem_Ico]
    apply forall_congr'
    intro i
    rw [Int.floor_eq_iff, le_div_iff₀ (hρ i), div_lt_iff₀ (hρ i)]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
  rw [hpre, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => (hρ i).le)).symm

lemma pureMarginal_same_mesh (B a ρ₁ ρ₂ : ℝ) (g : Raw → ℝ)
    (hc : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      ⌊x 0 / ρ₁⌋ = ⌊y 0 / ρ₁⌋ → ⌊x 1 / ρ₂⌋ = ⌊y 1 / ρ₂⌋ →
      ⌊x 2 / ρ₂⌋ = ⌊y 2 / ρ₂⌋ → g x = g y)
    (z z' : Observation) (hz : meshCode ![ρ₁, ρ₂, ρ₂] z =
      meshCode ![ρ₁, ρ₂, ρ₂] z') :
    pureMarginal B a (fun x => ENNReal.ofReal (g x)) z =
      pureMarginal B a (fun x => ENNReal.ofReal (g x)) z' := by
  classical
  have hb := congrArg Prod.fst hz
  have hh := congrArg Prod.snd hz
  change z.2 = z'.2 at hh
  unfold pureMarginal Submission.Lib.K4MarginalAveraging.countedMarginal
  apply lintegral_congr
  intro w
  simp only [hh, rawSplit_symm_eq]
  have hg : g (Submission.Obl.k4_native_base_flattening.join (WithLp.ofLp z.1, w)) =
      g (Submission.Obl.k4_native_base_flattening.join (WithLp.ofLp z'.1, w)) := by
    apply hc
    · intro i hi
      fin_cases i <;> simp_all [baseCoordinates, Submission.Obl.k4_native_base_flattening.join]
    · exact congrFun hb 0
    · exact congrFun hb 1
    · exact congrFun hb 2
  rw [hg]

/-- The light-cell bound expressed in the original state space. -/
theorem light_mass_of_approx (μ : Measure State) (B a ρ₁ ρ₂ θ : ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hθ0 : 0 ≤ θ)
    (F : Raw → ℝ≥0∞) (hF : Measurable F)
    (hraw : μ.map rawChart = volume.withDensity F)
    (g : Observation → ℝ≥0∞) (hg : Measurable g)
    (hobs : μ.map (pureMap B a) = reference.withDensity g)
    (H : Raw → ℝ≥0∞) (hH : Measurable H)
    (hcell : ∀ z z', meshCode ![ρ₁, ρ₂, ρ₂] z = meshCode ![ρ₁, ρ₂, ρ₂] z' →
      pureMarginal B a H z = pureMarginal B a H z') :
    μ {p | μ ((meshCode ![ρ₁, ρ₂, ρ₂] ∘ pureMap B a) ⁻¹'
        {(meshCode ![ρ₁, ρ₂, ρ₂] ∘ pureMap B a) p}) <
      ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} ≤
      3 * (∫⁻ x, ediff (F x) (H x)) +
        μ {p | g (pureMap B a p) < 4 * ENNReal.ofReal θ} := by
  let ρ : Fin 3 → ℝ := ![ρ₁, ρ₂, ρ₂]
  have hρ : ∀ i, 0 < ρ i := by intro i; fin_cases i <;> assumption
  have hm : Measurable (pureMarginal B a H) := pureMarginal_measurable B a hH
  have hmap : reference.withDensity g = reference.withDensity (pureMarginal B a F) := by
    rw [← hobs, pureMap_eq, ← Measure.map_map (rawObserve_measurable B a) rawChart_measurable,
      hraw, map_rawObserve_withDensity B a hF]
  haveI : SigmaFinite reference := by unfold reference; infer_instance
  have hae : g =ᵐ[reference] pureMarginal B a F :=
    (withDensity_eq_iff_of_sigmaFinite hg.aemeasurable
      (pureMarginal_measurable B a hF).aemeasurable).mp hmap
  have hL1 : (∫⁻ z, ediff (g z) (pureMarginal B a H z) ∂reference) ≤
      ∫⁻ x, ediff (F x) (H x) := by
    calc
      _ = ∫⁻ z, ediff (pureMarginal B a F z) (pureMarginal B a H z) ∂reference := by
        apply lintegral_congr_ae
        filter_upwards [hae] with z hz
        rw [hz]
      _ ≤ _ := pureMarginal_ediff_le B a hF hH
  let tab : CellCode → ℝ≥0∞ := fun c => pureMarginal B a H (meshCorner ρ c)
  have htab (z : Observation) : tab (meshCode ρ z) = pureMarginal B a H z :=
    hcell _ _ (meshCode_corner ρ hρ (meshCode ρ z))
  have hcert := partition_light_mass_le reference g hg (meshCode ρ)
    (meshCode_measurable ρ) tab (ENNReal.ofReal (ρ₁ * ρ₂ ^ 2)) (ENNReal.ofReal θ)
    (by finiteness) (by
      intro c
      simpa only [ρ, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.prod_univ_zero, mul_one, pow_two, mul_assoc] using meshCode_volume ρ hρ c)
  simp_rw [htab] at hcert
  have hc (z : State) :
      μ ((meshCode ρ ∘ pureMap B a) ⁻¹' {meshCode ρ (pureMap B a z)}) =
        (reference.withDensity g) (meshCode ρ ⁻¹' {meshCode ρ (pureMap B a z)}) := by
    rw [← hobs, Measure.map_apply (pureMap_measurable B a)
      ((meshCode_measurable ρ) (measurableSet_singleton _))]
    rfl
  have hθ : ENNReal.ofReal θ * ENNReal.ofReal (ρ₁ * ρ₂ ^ 2) =
      ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2) := by rw [← ENNReal.ofReal_mul hθ0]; congr 1; ring
  rw [hθ] at hcert
  have hlight : μ {p | μ ((meshCode ρ ∘ pureMap B a) ⁻¹'
      {(meshCode ρ ∘ pureMap B a) p}) < ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} =
      (reference.withDensity g) {z | (reference.withDensity g)
        (meshCode ρ ⁻¹' {meshCode ρ z}) < ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} := by
    let Light : Set Observation := {z | (reference.withDensity g)
      (meshCode ρ ⁻¹' {meshCode ρ z}) < ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)}
    have hLight : MeasurableSet Light :=
      measurableSet_lt ((measurable_of_countable
        (fun c => (reference.withDensity g) (meshCode ρ ⁻¹' {c}))).comp
          (meshCode_measurable ρ)) measurable_const
    change μ _ = (reference.withDensity g) Light
    rw [← hobs, Measure.map_apply (pureMap_measurable B a) hLight]
    congr 1
    ext p
    change (μ ((meshCode ρ ∘ pureMap B a) ⁻¹' {meshCode ρ (pureMap B a p)}) <
      ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)) ↔ ((reference.withDensity g)
        (meshCode ρ ⁻¹' {meshCode ρ (pureMap B a p)}) < ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2))
    rw [hc p]

  rw [hlight]
  refine hcert.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_right hL1 3
  · rw [← hobs, Measure.map_apply (pureMap_measurable B a)
      (measurableSet_lt hg measurable_const)]
    rfl

end Submission.Obl.k4_horizon_light_cell_mass
