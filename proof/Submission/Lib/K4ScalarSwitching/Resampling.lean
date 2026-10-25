import Mathlib

/-!
Adapted from: here:o062
Original proof: x0212, commit 27753bf,
Submission/Obl/k4_scalar_mesh_projection/Resampling.lean.

Continuous conditional resampling and unnormalized transition bounds.
Conditional-distribution stationarity is imported from Mathlib rather
than reproved by a finite approximation of the incidence space.
-/

namespace Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable def conditionalResampling {Ω C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (key : Ω → C) (hkey : Measurable key) :
    Kernel Ω Ω :=
  (condDistrib (id : Ω → Ω) key μ).comap key hkey

theorem conditionalResampling_markov {Ω C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (key : Ω → C) (hkey : Measurable key) :
    IsMarkovKernel (conditionalResampling μ key hkey) := by
  unfold conditionalResampling
  infer_instance

/-- Redrawing the entire incidence conditional on any measurable key
preserves its original finite law. -/
theorem conditionalResampling_invariant {Ω C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (key : Ω → C) (hkey : Measurable key) :
    Kernel.Invariant (conditionalResampling μ key hkey) μ := by
  change conditionalResampling μ key hkey ∘ₘ μ = μ
  rw [conditionalResampling, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map hkey]
  simpa only [Measure.map_id] using
    condDistrib_comp_map hkey.aemeasurable (aemeasurable_id : AEMeasurable (id : Ω → Ω) μ)

/-- A state resampling followed by a line resampling has the same
incidence marginal, even though the two draws are dependent. -/
theorem alternatingResampling_invariant {Ω C₁ C₂ : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace C₁] [MeasurableSpace C₂]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (key₁ : Ω → C₁) (hkey₁ : Measurable key₁) (key₂ : Ω → C₂) (hkey₂ : Measurable key₂) :
    Kernel.Invariant
      (conditionalResampling μ key₂ hkey₂ ∘ₖ conditionalResampling μ key₁ hkey₁) μ :=
  (conditionalResampling_invariant μ key₂ hkey₂).comp
    (conditionalResampling_invariant μ key₁ hkey₁)

theorem conditionalResampling_event_mass {Ω C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (key : Ω → C) (hkey : Measurable key)
    (B : Set Ω) (hB : MeasurableSet B) :
    (∫⁻ ω, conditionalResampling μ key hkey ω B ∂μ) = μ B := by
  have h := congrArg (fun ν : Measure Ω => ν B) (conditionalResampling_invariant μ key hkey)
  rw [Measure.bind_apply hB (Kernel.aemeasurable _)] at h
  exact h

/-- A conditional redraw keeps the conditioning state or line, outside
one null set for the original incidence law. -/
theorem conditionalResampling_ae_key {Ω C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace C] [StandardBorelSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (key : Ω → C) (hkey : Measurable key) :
    ∀ᵐ ω ∂μ, ∀ᵐ ω' ∂conditionalResampling μ key hkey ω, key ω' = key ω := by
  letI : Nonempty C := Nonempty.map key inferInstance
  have hmapkey : ∀ᵐ c ∂μ.map key,
      Measure.map key (condDistrib (id : Ω → Ω) key μ c) = Measure.dirac c := by
    filter_upwards [condDistrib_comp hkey.aemeasurable
      (aemeasurable_id : AEMeasurable (id : Ω → Ω) μ) hkey,
      condDistrib_self hkey.aemeasurable] with c hc hs
    rw [Kernel.map_apply _ hkey c] at hc
    simpa only [Kernel.id_apply] using hc.symm.trans hs
  have hdraw : ∀ᵐ c ∂μ.map key,
      ∀ᵐ ω' ∂condDistrib (id : Ω → Ω) key μ c, key ω' = c := by
    filter_upwards [hmapkey] with c hc
    apply ae_iff.mpr
    have hzero : Measure.map key (condDistrib (id : Ω → Ω) key μ c) ({c}ᶜ) = 0 := by
      rw [hc]
      simp
    rwa [Measure.map_apply hkey (measurableSet_singleton c).compl] at hzero
  exact ae_of_ae_map hkey.aemeasurable hdraw

/-- A lower duration floor and an upper incidence-density ceiling give the
endpoint-time ceiling without renormalizing the retained transition event. -/
theorem normalized_fiber_measure_le {T : Type*} [MeasurableSpace T]
    (τ : Measure T) (f : T → ENNReal) (K q : ENNReal)
    (hbound : f ≤ᵐ[τ] fun _ => K) (hfloor : q ≤ ∫⁻ t, f t ∂τ) :
    (∫⁻ t, f t ∂τ)⁻¹ • τ.withDensity f ≤ (K / q) • τ := by
  have hden : τ.withDensity f ≤ K • τ := by
    calc
      τ.withDensity f ≤ τ.withDensity (fun _ => K) := withDensity_mono hbound
      _ = K • τ := withDensity_const K
  refine Measure.le_iff.mpr ?_
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  have hA' := Measure.le_iff.mp hden A hA
  simp only [Measure.smul_apply, smul_eq_mul] at hA'
  have hinv : (∫⁻ t, f t ∂τ)⁻¹ ≤ q⁻¹ := ENNReal.inv_le_inv.mpr hfloor
  calc
    (∫⁻ t, f t ∂τ)⁻¹ * τ.withDensity f A ≤ q⁻¹ * (K * τ A) := mul_le_mul' hinv hA'
    _ = (K / q) * τ A := by rw [div_eq_mul_inv]; ac_rfl

/-- A pointwise endpoint-time ceiling is retained by an arbitrary mixture
over the line selected by the preceding switch. -/
theorem compProd_le_of_endpoint_ceiling {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (θ : Measure X) [SFinite θ] (τ : Measure T) [SFinite τ]
    (κ : Kernel X T) [IsSFiniteKernel κ] (D : ENNReal)
    (hκ : ∀ x, κ x ≤ D • τ) :
    θ ⊗ₘ κ ≤ D • θ.prod τ := by
  refine Measure.le_iff.mpr ?_
  intro A hA
  rw [Measure.compProd_apply hA, Measure.smul_apply, smul_eq_mul,
    Measure.prod_apply hA]
  calc
    (∫⁻ x, κ x (Prod.mk x ⁻¹' A) ∂θ) ≤
        ∫⁻ x, D * τ (Prod.mk x ⁻¹' A) ∂θ := by
      apply lintegral_mono
      intro x
      exact Measure.le_iff.mp (hκ x) _
        (hA.preimage (measurable_const.prodMk measurable_id))
    _ = D * ∫⁻ x, τ (Prod.mk x ⁻¹' A) ∂θ :=
      lintegral_const_mul D (measurable_measure_prodMk_left hA)

/-- The actual joint control/time transition is bounded by the product
palette/time law, with no normalization of the retained transition. This
bound can be imposed for each complete past history. -/
theorem joint_control_time_transition_le {X C T : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace T]
    (θ : Measure X) [SFinite θ] (π : Measure C) [SFinite π]
    (τ : Measure T) [SFinite τ] (κ : Kernel X T) [IsSFiniteKernel κ]
    (control : X → C) (hcontrol : Measurable control) (K D : ENNReal)
    (hpalette : Measure.map control θ ≤ K • π)
    (hκ : ∀ x, κ x ≤ D • τ) :
    Measure.map (Prod.map control id) (θ ⊗ₘ κ) ≤ (K * D) • π.prod τ := by
  have hmap := Measure.map_mono (compProd_le_of_endpoint_ceiling θ τ κ D hκ)
    (hcontrol.prodMap measurable_id)
  rw [Measure.map_smul D (hcontrol.prodMap measurable_id).aemeasurable] at hmap
  have hprod : Measure.map (Prod.map control id) (θ.prod τ) =
      (Measure.map control θ).prod τ := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map θ τ hcontrol measurable_id).symm
  rw [hprod] at hmap
  have hp := Measure.prod_mono hpalette (le_refl τ)
  rw [Measure.prod_smul_left K] at hp
  calc
    Measure.map (Prod.map control id) (θ ⊗ₘ κ) ≤
        D • (Measure.map control θ).prod τ := hmap
    _ ≤ D • (K • π.prod τ) := smul_le_smul_left D hp
    _ = (K * D) • π.prod τ := by
      rw [smul_smul, mul_comm D K]

noncomputable def conditionalFiberDensity {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) (F : X × T → ENNReal) (p : X × T) : ENNReal :=
  if (∫⁻ t, F (p.1, t) ∂τ) = 0 then 1 else (∫⁻ t, F (p.1, t) ∂τ)⁻¹ * F p

theorem measurable_conditionalFiberDensity {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [SFinite τ]
    (F : X × T → ENNReal) (hF : Measurable F) :
    Measurable (conditionalFiberDensity τ F) := by
  have hd : Measurable (fun x => ∫⁻ t, F (x, t) ∂τ) :=
    Measurable.lintegral_prod_right (f := fun x t => F (x, t)) hF
  have hz : MeasurableSet {p : X × T | (∫⁻ t, F (p.1, t) ∂τ) = 0} :=
    measurableSet_eq_fun (hd.comp measurable_fst) measurable_const
  exact measurable_const.piecewise hz ((hd.inv.comp measurable_fst).mul hF)

noncomputable def normalizedFiberKernel {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [SFinite τ]
    (F : X × T → ENNReal) : Kernel X T :=
  (Kernel.const X τ).withDensity (fun x t => conditionalFiberDensity τ F (x, t))

theorem normalizedFiberKernel_apply {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [SFinite τ]
    (F : X × T → ENNReal) (hF : Measurable F) (x : X) :
    normalizedFiberKernel τ F x =
      if (∫⁻ t, F (x, t) ∂τ) = 0 then τ else
        (∫⁻ t, F (x, t) ∂τ)⁻¹ • τ.withDensity (fun t => F (x, t)) := by
  rw [normalizedFiberKernel,
    Kernel.withDensity_apply (f := fun x t => conditionalFiberDensity τ F (x, t)) _
      (measurable_conditionalFiberDensity τ F hF), Kernel.const_apply]
  by_cases hx : (∫⁻ t, F (x, t) ∂τ) = 0
  · simp [conditionalFiberDensity, hx]
  · simp only [conditionalFiberDensity, hx, ite_false]
    rw [← withDensity_smul (μ := τ) (f := fun t : T => F (x, t))
      (∫⁻ t, F (x, t) ∂τ)⁻¹
      (hF.comp measurable_prodMk_left)]
    congr 1

theorem normalizedFiberKernel_markov {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) (hF : Measurable F)
    (hfinite : ∀ x, (∫⁻ t, F (x, t) ∂τ) ≠ ∞) :
    IsMarkovKernel (normalizedFiberKernel τ F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [normalizedFiberKernel_apply τ F hF]
  by_cases hx : (∫⁻ t, F (x, t) ∂τ) = 0
  · simp [hx]
  · rw [ite_eq_right hx, Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ENNReal.inv_mul_cancel hx (hfinite x)

theorem normalizedFiberKernel_le_of_duration_floor {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [SFinite τ]
    (F : X × T → ENNReal) (hF : Measurable F) (K q : ENNReal) (hq : 0 < q)
    (x : X) (hbound : (fun t => F (x, t)) ≤ᵐ[τ] fun _ => K)
    (hfloor : q ≤ ∫⁻ t, F (x, t) ∂τ) :
    normalizedFiberKernel τ F x ≤ (K / q) • τ := by
  rw [normalizedFiberKernel_apply τ F hF,
    ite_eq_right (ne_of_gt (hq.trans_le hfloor))]
  exact normalized_fiber_measure_le τ (fun t => F (x, t)) K q hbound hfloor

/-- The explicit normalized time fibers disintegrate the original incidence
density. Zero-duration rows use the reference probability law and carry
zero marginal weight. -/
theorem normalizedFiberKernel_joint_law {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) (hF : Measurable F)
    (hfinite : ∀ x, (∫⁻ t, F (x, t) ∂τ) ≠ ∞) :
    (ν.withDensity (fun x => ∫⁻ t, F (x, t) ∂τ)) ⊗ₘ normalizedFiberKernel τ F =
      (ν.prod τ).withDensity F := by
  letI : IsMarkovKernel ((Kernel.const X τ).withDensity
      (fun x t => conditionalFiberDensity τ F (x, t))) :=
    normalizedFiberKernel_markov τ F hF hfinite
  have hd : Measurable (fun x => ∫⁻ t, F (x, t) ∂τ) :=
    Measurable.lintegral_prod_right (f := fun x t => F (x, t)) hF
  have hg := measurable_conditionalFiberDensity τ F hF
  change (ν.withDensity (fun x => ∫⁻ t, F (x, t) ∂τ)) ⊗ₘ
    ((Kernel.const X τ).withDensity (fun x t => conditionalFiberDensity τ F (x, t))) = _
  rw [Measure.withDensity_compProd_withDensity (κ := Kernel.const X τ)
    (g := fun x t => conditionalFiberDensity τ F (x, t)) hd hg, Measure.compProd_const]
  apply withDensity_congr_ae
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((hd.comp measurable_fst).mul hg) hF)).mpr
  refine ae_of_all ν (fun x => ?_)
  by_cases hx : (∫⁻ t, F (x, t) ∂τ) = 0
  · have hz := (lintegral_eq_zero_iff (hF.comp measurable_prodMk_left)).mp hx
    filter_upwards [hz] with t ht
    change F (x, t) = 0 at ht
    simp [conditionalFiberDensity, hx, ht]
  · refine ae_of_all τ ?_
    intro t
    change (∫⁻ s, F (x, s) ∂τ) * conditionalFiberDensity τ F (x, t) = F (x, t)
    rw [conditionalFiberDensity, ite_eq_right hx, ← mul_assoc,
      ENNReal.mul_inv_cancel hx (hfinite x), one_mul]

theorem conditional_time_kernel_eq_normalized {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) [IsFiniteMeasure ((ν.prod τ).withDensity F)]
    (hF : Measurable F) (hfinite : ∀ x, (∫⁻ t, F (x, t) ∂τ) ≠ ∞) :
    condDistrib Prod.snd Prod.fst ((ν.prod τ).withDensity F) =ᵐ[
        ((ν.prod τ).withDensity F).fst] normalizedFiberKernel τ F := by
  letI : IsMarkovKernel (normalizedFiberKernel τ F) :=
    normalizedFiberKernel_markov τ F hF hfinite
  have hjoint := normalizedFiberKernel_joint_law ν τ F hF hfinite
  have hmarg := congrArg Measure.fst hjoint
  rw [Measure.fst_compProd] at hmarg
  apply condDistrib_ae_eq_of_measure_eq_compProd
    measurable_fst.aemeasurable measurable_snd.aemeasurable
  change Measure.map (id : X × T → X × T) ((ν.prod τ).withDensity F) = _
  rw [Measure.map_id]
  change (ν.prod τ).withDensity F =
    ((ν.prod τ).withDensity F).fst ⊗ₘ normalizedFiberKernel τ F
  rw [← hmarg]
  exact hjoint.symm

/-- The genuine conditional endpoint-time law on every retained long line
has the density ceiling used by the switched-path transition estimate. -/
theorem conditional_time_kernel_le_on_long_lines {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) [IsFiniteMeasure ((ν.prod τ).withDensity F)]
    (hF : Measurable F) (hfinite : ∀ x, (∫⁻ t, F (x, t) ∂τ) ≠ ∞)
    (K q : ENNReal) (hq : 0 < q) (hbound : ∀ x, (fun t => F (x, t)) ≤ᵐ[τ] fun _ => K) :
    ∀ᵐ x ∂((ν.prod τ).withDensity F).fst, q ≤ (∫⁻ t, F (x, t) ∂τ) →
      condDistrib Prod.snd Prod.fst ((ν.prod τ).withDensity F) x ≤ (K / q) • τ := by
  filter_upwards [conditional_time_kernel_eq_normalized ν τ F hF hfinite] with x hx hlong
  rw [hx]
  exact normalizedFiberKernel_le_of_duration_floor τ F hF K q hq x (hbound x) hlong

theorem conditional_time_kernel_le_of_bounded_density {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) [IsFiniteMeasure ((ν.prod τ).withDensity F)]
    (hF : Measurable F) (K q : ENNReal) (hK : K ≠ ∞) (hq : 0 < q)
    (hbound : ∀ x, (fun t => F (x, t)) ≤ᵐ[τ] fun _ => K) :
    ∀ᵐ x ∂((ν.prod τ).withDensity F).fst, q ≤ (∫⁻ t, F (x, t) ∂τ) →
      condDistrib Prod.snd Prod.fst ((ν.prod τ).withDensity F) x ≤ (K / q) • τ := by
  have hfinite (x : X) : (∫⁻ t, F (x, t) ∂τ) ≠ ∞ := by
    have hx : (∫⁻ t, F (x, t) ∂τ) ≤ K := by
      calc
        (∫⁻ t, F (x, t) ∂τ) ≤ ∫⁻ _t, K ∂τ := lintegral_mono_ae (hbound x)
        _ = K := by simp
    exact ne_of_lt (hx.trans_lt (lt_top_iff_ne_top.mpr hK))
  exact conditional_time_kernel_le_on_long_lines ν τ F hF hfinite K q hq hbound

end Submission.Lib.K4ScalarSwitching
