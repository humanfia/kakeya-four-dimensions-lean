/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Submission.Lib.K4PolynomialNorming

/-- A history law dominated by one reference law and a next-step kernel
dominated at every history give product domination without any independence
assumption on the actual path law. -/
theorem compProd_le_smul_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P μ : Measure X) [SFinite P] [SFinite μ] (ν : Measure Y) [SFinite ν]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (a b : ENNReal)
    (hP : P ≤ a • μ) (hκ : ∀ x, κ x ≤ b • ν) :
    P ⊗ₘ κ ≤ (a * b) • (μ.prod ν) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.compProd_apply hE, Measure.smul_apply, smul_eq_mul, Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, b * ν (Prod.mk x ⁻¹' E) ∂P := by
      apply lintegral_mono
      intro x
      exact hκ x (Prod.mk x ⁻¹' E)
    _ ≤ ∫⁻ x, b * ν (Prod.mk x ⁻¹' E) ∂(a • μ) := lintegral_mono' hP le_rfl
    _ = _ := by
      rw [lintegral_smul_measure, lintegral_const_mul _ (measurable_measure_prodMk_left hE)]
      simp only [smul_eq_mul, mul_assoc]


/-- Full-past domination survives forgetting unobserved state information.
The actual next-step law and the observation may both depend on the
entire history; the observed law is only assumed dominated almost everywhere
under the actual past law. This includes durations relative to refreshed starts. -/
theorem history_observed_compProd_le_smul_prod {X Y U V : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure X) [SFinite P] (μ : Measure U) [SFinite μ] (ν : Measure V) [SFinite ν]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (g : X → U) (obs : X × Y → V)
    (hg : Measurable g) (hobs : Measurable obs) (a b : ENNReal)
    (hP : P.map g ≤ a • μ) (hκ : ∀ᵐ x ∂P, (κ x).map (fun y => obs (x,y)) ≤ b • ν) :
    (P ⊗ₘ κ).map (fun z : X × Y => (g z.1, obs z)) ≤ (a * b) • (μ.prod ν) := by
  apply Measure.le_iff.mpr
  intro E hE
  have hmeas : Measurable (fun z : X × Y => (g z.1, obs z)) :=
    (hg.comp measurable_fst).prodMk hobs
  rw [Measure.map_apply hmeas hE,
    Measure.compProd_apply (hmeas hE), Measure.smul_apply, smul_eq_mul,
    Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, b * ν (Prod.mk (g x) ⁻¹' E) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hκ] with x hx
      have hs : MeasurableSet (Prod.mk (g x) ⁻¹' E) :=
        hE.preimage (measurable_const.prodMk measurable_id)
      have hobsx : Measurable (fun y : Y => obs (x,y)) :=
        hobs.comp ((measurable_const : Measurable (fun _ : Y => x)).prodMk measurable_id)
      have hb := hx (Prod.mk (g x) ⁻¹' E)
      rw [Measure.map_apply hobsx hs, Measure.smul_apply, smul_eq_mul] at hb
      exact hb
    _ = ∫⁻ u, b * ν (Prod.mk u ⁻¹' E) ∂P.map g :=
      (lintegral_map ((measurable_measure_prodMk_left hE).const_mul b) hg).symm
    _ ≤ ∫⁻ u, b * ν (Prod.mk u ⁻¹' E) ∂(a • μ) := lintegral_mono' hP le_rfl
    _ = _ := by
      rw [lintegral_smul_measure, lintegral_const_mul _ (measurable_measure_prodMk_left hE)]
      simp only [smul_eq_mul, mul_assoc]


/-- Special case of the full-past observation bound when the next
observation is a function only of the newly sampled state. -/
theorem observed_compProd_le_smul_prod {X Y U V : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure X) [SFinite P] (μ : Measure U) [SFinite μ] (ν : Measure V) [SFinite ν]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (g : X → U) (obs : Y → V)
    (hg : Measurable g) (hobs : Measurable obs) (a b : ENNReal)
    (hP : P.map g ≤ a • μ) (hκ : ∀ᵐ x ∂P, (κ x).map obs ≤ b • ν) :
    (P ⊗ₘ κ).map (fun z : X × Y => (g z.1, obs z.2)) ≤ (a * b) • (μ.prod ν) := by
  exact history_observed_compProd_le_smul_prod P μ ν κ g
    (fun z : X × Y => obs z.2) hg (hobs.comp measurable_snd) a b hP hκ

/-- Refresh from the original finite law conditioned on the currently known
state. This is Mathlib's posterior of a deterministic observation, followed
by that observation; no finite-atom assumption is used. -/
noncomputable def conditionalRefresh {Ω S : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g) : Kernel Ω Ω :=
  (Kernel.deterministic g hg)†P ∘ₖ Kernel.deterministic g hg

theorem conditionalRefresh_isMarkov {Ω S : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g) :
    IsMarkovKernel (conditionalRefresh P g hg) := by
  unfold conditionalRefresh
  infer_instance

/-- Conditional refresh preserves the ORIGINAL law, even when it is a finite
subprobability law rather than a normalized probability law. -/
theorem conditionalRefresh_stationary {Ω S : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g) :
    conditionalRefresh P g hg ∘ₘ P = P := by
  rw [conditionalRefresh, ← Measure.comp_assoc, posterior_comp_self]

/-- Alternating two conditional refreshes, for example state then line,
still preserves the original law. -/
theorem conditionalRefresh_pair_stationary {Ω S T : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g)
    (line : Ω → T) (hline : Measurable line) :
    (conditionalRefresh P line hline ∘ₖ conditionalRefresh P g hg) ∘ₘ P = P := by
  letI := conditionalRefresh_isMarkov P g hg
  letI := conditionalRefresh_isMarkov P line hline
  rw [← Measure.comp_assoc, conditionalRefresh_stationary, conditionalRefresh_stationary]


/-- Refreshing conditional on an observation preserves that observation
almost surely under the unchanged prior law. -/
theorem conditionalRefresh_preserves_code {Ω S : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S] [MeasurableSpace.CountablyGenerated S]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g) :
    ∀ᵐ x ∂P, (conditionalRefresh P g hg x).map g = Measure.dirac (g x) := by
  have hcode := deterministic_comp_posterior (μ := P) hg
  rw [Kernel.deterministic_comp_eq_map hg] at hcode
  filter_upwards [ae_of_ae_map hg.aemeasurable hcode] with x hx
  simpa only [conditionalRefresh, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
    Kernel.map_apply _ hg, Kernel.id_apply] using hx

end Submission.Lib.K4PolynomialNorming
