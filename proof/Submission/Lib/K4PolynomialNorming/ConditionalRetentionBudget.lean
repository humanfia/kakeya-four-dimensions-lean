/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RetainedObservedTrajectories
import Submission.Lib.K4PolynomialNorming.StationaryKernelPaths
import Submission.Lib.K4PolynomialNorming.TrajectoryGoodSteps

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Short next states are charged to their original stationary marginal;
full-history pencil choices are charged to the prepared palette. Their
sum bounds the loss of the complete causally retained trajectory. -/
theorem stationary_causal_retention_mass_bound_of_pencil_mass {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (W : Set X) (hW : MeasurableSet W)
    (obs : X → V) (hobs : Measurable obs)
    (A : (n : ℕ) → Set ((((i : Finset.Iic n) → X)) × V))
    (hA : ∀ n, MeasurableSet (A n)) (p : ℕ → ENNReal)
    (hpenmass : ∀ n, (kernelPathMeasure P (fun _ => S))
      {x | (Preorder.frestrictLe n x,obs (x (n+1))) ∈ A n} ≤ p n)
    (hdefect : ∀ n h y, 1 - α n h y ≤
      Wᶜ.indicator (fun _ => 1) y + (A n).indicator (fun _ => 1) (h,obs y)) (N : ℕ) :
    (P.withDensity w₀) univ ≤
      ((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
        causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))) univ +
      ∑ n ∈ Finset.range N, (P Wᶜ + p n) := by
  classical
  let Q := kernelPathMeasure P (fun _ => S)
  have hloss (n : ℕ) : (Q.withDensity (fun x =>
      1 - α n (Preorder.frestrictLe n x) (x (n+1)))) univ ≤ P Wᶜ + p n := by
    let badShort : Set (ℕ → X) := {x | x (n+1) ∉ W}
    let badPencil : Set (ℕ → X) := {x | (Preorder.frestrictLe n x,obs (x (n+1))) ∈ A n}
    have hs : MeasurableSet badShort := hW.compl.preimage (measurable_pi_apply (n+1))
    have hp : MeasurableSet badPencil := (hA n).preimage (by fun_prop)
    have hm : Q badShort = P Wᶜ := by
      have hh := congrArg (fun μ : Measure X => μ Wᶜ)
        (kernelPathMeasure_stationary_marginal P (fun _ => S) (fun _ => hS) (n+1))
      rw [Measure.map_apply (by fun_prop) hW.compl] at hh
      exact hh
    have hpen : Q badPencil ≤ p n := hpenmass n
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      _ ≤ ∫⁻ x, (badShort.indicator (fun _ => (1 : ENNReal)) x +
          badPencil.indicator (fun _ => 1) x) ∂Q := by
        apply lintegral_mono
        intro x
        simpa only [badShort, badPencil, Set.indicator_apply, Set.mem_ofPred_eq,
          Set.mem_compl_iff] using hdefect n (Preorder.frestrictLe n x) (x (n+1))
      _ = Q badShort + Q badPencil := by
        rw [lintegral_add_left (measurable_const.indicator hs),
          lintegral_indicator hs, lintegral_indicator hp]
        simp
      _ ≤ _ := add_le_add (le_of_eq hm) hpen
  have hb := trajectory_causal_retention_mass_budget P (fullHistoryMarkovKernel (fun _ => S))
    w₀ hw₀ hw₀1 α hα hα1 N
  exact hb.trans (add_le_add le_rfl (Finset.sum_le_sum (fun n _ => hloss n)))


theorem trajectory_pencil_mass_of_conditional {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    [∀ n, IsMarkovKernel (κ n)] (obs : X → V) (hobs : Measurable obs) (n : ℕ)
    (A : Set ((((i : Finset.Iic n) → X)) × V)) (hA : MeasurableSet A) (p : ENNReal)
    (hpen : ∀ᵐ h ∂(Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).map (Preorder.frestrictLe n),
      κ n h {y | (h,obs y) ∈ A} ≤ p) :
    (Kernel.trajMeasure (X := fun _ : ℕ => X) P κ)
      {x | (Preorder.frestrictLe n x,obs (x (n+1))) ∈ A} ≤ p := by
  let B : Set ((((i : Finset.Iic n) → X)) × X) := {z | (z.1,obs z.2) ∈ A}
  have hB : MeasurableSet B := hA.preimage (measurable_fst.prodMk (hobs.comp measurable_snd))
  have h := trajectory_bad_step_mass_le P κ n Bᶜ hB.compl p
    (by simpa only [compl_compl, B, Set.preimage_setOf_eq] using hpen)
  simpa only [B, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using h

/-- The pencil budget can be supplied by the actual full-past conditional
draw, independently of the palette reference used for density ceilings. -/
theorem stationary_causal_retention_mass_bound_of_conditional_pencils {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (W : Set X) (hW : MeasurableSet W) (obs : X → V) (hobs : Measurable obs)
    (A : (n : ℕ) → Set ((((i : Finset.Iic n) → X)) × V))
    (hA : ∀ n, MeasurableSet (A n)) (p : ℕ → ENNReal)
    (hpen : ∀ n, ∀ᵐ h ∂(kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n),
      fullHistoryMarkovKernel (fun _ => S) n h {y | (h,obs y) ∈ A n} ≤ p n)
    (hdefect : ∀ n h y, 1 - α n h y ≤
      Wᶜ.indicator (fun _ => 1) y + (A n).indicator (fun _ => 1) (h,obs y)) (N : ℕ) :
    (P.withDensity w₀) univ ≤
      ((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
        causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))) univ +
      ∑ n ∈ Finset.range N, (P Wᶜ + p n) := by
  exact stationary_causal_retention_mass_bound_of_pencil_mass P S hS w₀ hw₀ hw₀1 α hα hα1
    W hW obs hobs A hA p (fun n => trajectory_pencil_mass_of_conditional P
      (fullHistoryMarkovKernel (fun _ => S)) obs hobs n (A n) (hA n) (p n) (hpen n)) hdefect N


/-- A uniform original conditional bound can be evaluated at a pencil
selected from the entire actual past. The original exceptional set is
pulled back through its stationary current marginal. -/
theorem stationary_history_pencil_cap_of_uniform_original {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (obs : X → V) (hobs : Measurable obs) (n : ℕ)
    (A : Set ((((i : Finset.Iic n) → X)) × V)) (hA : MeasurableSet A) (p : ENNReal)
    (hcap : ∀ᵐ x ∂P, ∀ h : (i : Finset.Iic n) → X,
      (S x).map obs (Prod.mk h ⁻¹' A) ≤ p) :
    ∀ᵐ h ∂(kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n),
      fullHistoryMarkovKernel (fun _ => S) n h {y | (h,obs y) ∈ A} ≤ p := by
  let θ := (kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n)
  let last : ((i : Finset.Iic n) → X) → X := fun h => h ⟨n, by simp⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hmarg : θ.map last = P := by
    rw [show θ = (kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n) from rfl,
      Measure.map_map hlast (by fun_prop)]
    exact kernelPathMeasure_stationary_marginal P (fun _ => S) (fun _ => hS) n
  have ha : ∀ᵐ x ∂θ.map last, ∀ h : (i : Finset.Iic n) → X,
      (S x).map obs (Prod.mk h ⁻¹' A) ≤ p := by
    rw [hmarg]
    exact hcap
  have hpull := ae_of_ae_map hlast.aemeasurable ha
  filter_upwards [hpull] with h hh
  have hz := hh h
  rw [Measure.map_apply hobs (hA.preimage measurable_prodMk_left)] at hz
  exact hz


end Submission.Lib.K4PolynomialNorming
