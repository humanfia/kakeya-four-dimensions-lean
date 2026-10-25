import Mathlib
import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Kernel.MutualInfo

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy

open Set MeasureTheory ProbabilityTheory

/-- Data processing for a finite law. The kernel entropy module imports
cleanly beside Mathlib, unlike lean-pool's random-variable facade. -/
theorem measure_entropy_map_le {S U : Type*}
    [MeasurableSpace S] [MeasurableSpace U] [Countable S] [Countable U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure S) [IsProbabilityMeasure μ] [FiniteSupport μ] (f : S → U) :
    measureEntropy (μ.map f) ≤ measureEntropy μ := by
  have h := Kernel.entropy_map_le f (κ := Kernel.const Unit μ)
    (μ := Measure.dirac ())
    ((Kernel.finiteKernelSupport_of_const μ).aefiniteKernelSupport (Measure.dirac ()))
  simpa [Kernel.map_const μ (measurable_of_countable f)] using h

/-- Submodularity for a finitely supported law, with no finite assumption on
the underlying trajectory space that generated the law. -/
theorem measure_entropy_submodular {A B Z : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [Countable Z]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass Z]
    (μ : Measure (A × B × Z)) [IsProbabilityMeasure μ] [FiniteSupport μ] :
    measureEntropy μ + measureEntropy (μ.map (fun p => p.2.2)) ≤
      measureEntropy (μ.map (fun p => (p.1, p.2.2))) + measureEntropy (μ.map Prod.snd) := by
  have hAZ : Measurable (fun p : A × B × Z => (p.1, p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have h := Kernel.entropy_triple_add_entropy_le (Kernel.const Unit μ) (Measure.dirac ())
    ((Kernel.finiteKernelSupport_of_const μ).aefiniteKernelSupport (Measure.dirac ()))
  simp only [Kernel.snd_eq, Kernel.deleteMiddle_eq] at h
  simp only [Kernel.map_const μ measurable_snd,
    Kernel.map_const (μ.map Prod.snd) measurable_snd,
    Kernel.map_const μ hAZ] at h
  simpa only [Kernel.entropy_const, measure_univ, ENNReal.toReal_one, one_mul,
    Measure.map_map measurable_snd measurable_snd, Function.comp_def] using h

/-- Common information is controlled by either encoding error and the
dependence of the two encoders. This form can be applied inside every
conditional law, including laws indexed by continuous times. -/
theorem common_information {A B Z : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [Countable Z]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass Z]
    (μ : Measure (A × B × Z)) [IsProbabilityMeasure μ] [FiniteSupport μ] :
    measureEntropy (μ.map (fun p => p.2.2)) ≤
      (measureEntropy (μ.map (fun p => (p.1, p.2.2))) - measureEntropy (μ.map Prod.fst)) +
      (measureEntropy (μ.map Prod.snd) - measureEntropy (μ.map (fun p => p.2.1))) +
      (measureEntropy (μ.map Prod.fst) + measureEntropy (μ.map (fun p => p.2.1)) -
        measureEntropy (μ.map (fun p => (p.1, p.2.1)))) := by
  have hsub := measure_entropy_submodular μ
  have hmap := measure_entropy_map_le μ (fun p => (p.1, p.2.1))
  linarith

/-- The common-information bound applies anew inside arbitrary conditional
laws. The conditioning space may include continuous presampled times. -/
theorem integrated_common_information {T A B Z : Type*}
    [MeasurableSpace T] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [Countable Z]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass Z]
    (ν : Measure T) (P : T → Measure (A × B × Z))
    [∀ t, IsProbabilityMeasure (P t)] [∀ t, FiniteSupport (P t)]
    (hZ : Integrable (fun t => measureEntropy ((P t).map (fun p => p.2.2))) ν)
    (hAB : Integrable (fun t => measureEntropy ((P t).map (fun p => (p.1, p.2.1)))) ν)
    (hAZ : Integrable (fun t => measureEntropy ((P t).map (fun p => (p.1, p.2.2)))) ν)
    (hBZ : Integrable (fun t => measureEntropy ((P t).map Prod.snd)) ν) :
    (∫ t, measureEntropy ((P t).map (fun p => p.2.2)) ∂ν) +
      (∫ t, measureEntropy ((P t).map (fun p => (p.1, p.2.1))) ∂ν) ≤
    (∫ t, measureEntropy ((P t).map (fun p => (p.1, p.2.2))) ∂ν) +
      (∫ t, measureEntropy ((P t).map Prod.snd) ∂ν) := by
  have hpoint (t : T) := common_information (P t)
  have hle (t : T) : measureEntropy ((P t).map (fun p => p.2.2)) +
      measureEntropy ((P t).map (fun p => (p.1, p.2.1))) ≤
      measureEntropy ((P t).map (fun p => (p.1, p.2.2))) +
        measureEntropy ((P t).map Prod.snd) := by linarith [hpoint t]
  simpa only [Pi.add_apply, integral_add hZ hAB, integral_add hAZ hBZ] using
    integral_mono (hZ.add hAB) (hAZ.add hBZ) hle

/-- A uniform atom ceiling gives the corresponding Shannon entropy floor. -/
theorem entropy_lower_bound_of_atom_bound {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ]
    [FiniteSupport μ] {b : ℝ} (_hb : 0 < b) (hcap : ∀ x, μ.real {x} ≤ b) :
    -Real.log b ≤ measureEntropy μ := by
  classical
  let s := μ.finiteSupport
  have hs : μ (s : Set S)ᶜ = 0 := measure_compl_support μ
  have hmass : μ (s : Set S) = 1 := by
    have ht := measure_add_measure_compl (μ := μ) s.measurableSet
    simpa only [hs, add_zero, measure_univ] using ht
  have hsum : ∑ x ∈ s, μ.real {x} = 1 := by
    rw [sum_measureReal_singleton, Measure.real, hmass, ENNReal.toReal_one]
  rw [measureEntropy_of_isProbabilityMeasure_finite hs]
  calc
    -Real.log b = ∑ x ∈ s, μ.real {x} * (-Real.log b) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ x ∈ s, Real.negMulLog (μ.real {x}) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hzero : μ.real {x} = 0
      · simp [hzero]
      have hpos : 0 < μ.real {x} := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      have hlog := Real.log_le_log hpos (hcap x)
      calc
        μ.real {x} * (-Real.log b) ≤ μ.real {x} * (-Real.log (μ.real {x})) :=
          mul_le_mul_of_nonneg_left (neg_le_neg hlog) hpos.le
        _ = Real.negMulLog (μ.real {x}) := by rw [Real.negMulLog]; ring

/-- Support counts for the two observations, together with a joint atom
ceiling, give the information-independence error used after every dense
restriction. The actual marginal laws need not be uniform. -/
theorem mutual_information_of_support_bounds {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure (A × B)) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (sA : Finset A) (sB : Finset B)
    (hA : (μ.map Prod.fst) (sA : Set A)ᶜ = 0)
    (hB : (μ.map Prod.snd) (sB : Set B)ᶜ = 0)
    {b : ℝ} (hb : 0 < b) (hcap : ∀ x, μ.real {x} ≤ b) :
    measureMutualInfo μ ≤ Real.log sA.card + Real.log sB.card + Real.log b := by
  have h₁ := measureEntropy_le_log_card_of_mem (μ.map Prod.fst) hA
  have h₂ := measureEntropy_le_log_card_of_mem (μ.map Prod.snd) hB
  have h₃ := entropy_lower_bound_of_atom_bound μ hb hcap
  rw [measureMutualInfo_def]
  linarith

/-- A direct common-information bound from the scalar and coefficient
support counts and their joint atom cap. It may be applied separately in
every conditional law on the current dense event. -/
theorem common_information_of_support_bounds {A B Z : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [Countable Z]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass Z]
    (μ : Measure (A × B × Z)) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (sA : Finset A) (sB : Finset B)
    (hA : (μ.map Prod.fst) (sA : Set A)ᶜ = 0)
    (hB : (μ.map (fun p => p.2.1)) (sB : Set B)ᶜ = 0)
    {b : ℝ} (hb : 0 < b)
    (hcap : ∀ x, (μ.map (fun p => (p.1, p.2.1))).real {x} ≤ b) :
    measureEntropy (μ.map (fun p => p.2.2)) ≤
      (measureEntropy (μ.map (fun p => (p.1, p.2.2))) - measureEntropy (μ.map Prod.fst)) +
      (measureEntropy (μ.map Prod.snd) - measureEntropy (μ.map (fun p => p.2.1))) +
      (Real.log sA.card + Real.log sB.card + Real.log b) := by
  have : FiniteSupport (μ.map (fun p : A × B × Z => (p.1, p.2.1))) :=
    finiteSupport_of_comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h₁ := measureEntropy_le_log_card_of_mem (μ.map Prod.fst) hA
  have h₂ := measureEntropy_le_log_card_of_mem (μ.map (fun p => p.2.1)) hB
  have h₃ := entropy_lower_bound_of_atom_bound
    (μ.map (fun p : A × B × Z => (p.1, p.2.1))) hb hcap
  have h₄ := common_information μ
  linarith

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy
