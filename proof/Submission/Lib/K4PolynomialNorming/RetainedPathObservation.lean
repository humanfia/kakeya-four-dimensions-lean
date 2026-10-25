/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.KernelDomination

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Weighting by an observable commutes with taking its distribution. -/
theorem map_withDensity_pullback {Ω H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace H] (Q : Measure Ω)
    (f : Ω → H) (hf : Measurable f) (w : H → ENNReal) (hw : Measurable w) :
    (Q.withDensity (fun x => w (f x))).map f = (Q.map f).withDensity w := by
  ext E hE
  rw [Measure.map_apply hf hE, withDensity_apply _ (hE.preimage hf),
    withDensity_apply _ hE, setLIntegral_map hE hw hf]

/-- A causal retained step is the original path law weighted by the past
retention and the next-step retention. Neither measure is normalized. -/
theorem retainedTrajectory_step_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Ω) Ω)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ)
    (w : ((i : Finset.Iic n) → Ω) → ENNReal) (hw : Measurable w)
    (α : ((i : Finset.Iic n) → Ω) → Ω → ENNReal)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ h y, α h y ≤ 1) :
    ((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).withDensity (fun x =>
      w (Preorder.frestrictLe n x) * α (Preorder.frestrictLe n x) (x (n + 1)))).map
        (fun x => (Preorder.frestrictLe n x, x (n + 1))) =
      (((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n)).withDensity w) ⊗ₘ
        (κ n).withDensity α := by
  letI : IsFiniteKernel ((κ n).withDensity α) :=
    Kernel.isFiniteKernel_withDensity_of_bounded (κ n) (by simp : (1 : ENNReal) ≠ ∞) hα1
  rw [Measure.withDensity_compProd_withDensity hw hα,
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => Ω)]
  exact map_withDensity_pullback
    (Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ)
    (fun x : ℕ → Ω => (Preorder.frestrictLe n x, x (n + 1))) (by fun_prop)
    (fun z : (((i : Finset.Iic n) → Ω) × Ω) => w z.1 * α z.1 z.2)
    ((hw.comp measurable_fst).mul hα)

/-- Full-past domination and next-step observed domination bound the joint
observations of the actual causally retained path law. A past-dependent
observation includes a duration measured from a refreshed start. -/
theorem retainedTrajectory_observation_le {Ω U V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Ω) Ω)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ)
    (w : ((i : Finset.Iic n) → Ω) → ENNReal) (hw : Measurable w)
    (hw1 : ∀ h, w h ≤ 1)
    (α : ((i : Finset.Iic n) → Ω) → Ω → ENNReal)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ h y, α h y ≤ 1)
    (μ : Measure U) [SFinite μ] (ν : Measure V) [SFinite ν]
    (g : ((i : Finset.Iic n) → Ω) → U) (hg : Measurable g)
    (obs : (((i : Finset.Iic n) → Ω) × Ω) → V) (hobs : Measurable obs)
    (a b : ENNReal)
    (hPast : ((((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n)).withDensity w).map g)
      ≤ a • μ)
    (hNext : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n)).withDensity w,
      (((κ n).withDensity α) h).map (fun y => obs (h,y)) ≤ b • ν) :
    ((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).withDensity (fun x =>
      w (Preorder.frestrictLe n x) * α (Preorder.frestrictLe n x) (x (n + 1)))).map
        (fun x => (g (Preorder.frestrictLe n x), obs (Preorder.frestrictLe n x, x (n + 1))))
      ≤ (a * b) • (μ.prod ν) := by
  let Q := (Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n)
  have hQ : Q.withDensity w ≤ Q := by
    calc
      _ ≤ Q.withDensity (fun _ => 1) :=
        withDensity_mono (Filter.Eventually.of_forall hw1)
      _ = Q := by simp
  letI : IsFiniteMeasure (Q.withDensity w) := isFiniteMeasure_of_le Q hQ
  letI : IsFiniteKernel ((κ n).withDensity α) :=
    Kernel.isFiniteKernel_withDensity_of_bounded (κ n) (by simp : (1 : ENNReal) ≠ ∞) hα1
  have h := history_observed_compProd_le_smul_prod (Q.withDensity w) μ ν
    ((κ n).withDensity α) g obs hg hobs a b hPast hNext
  rw [← retainedTrajectory_step_law P κ n w hw α hα hα1,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end Submission.Lib.K4PolynomialNorming

