/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RetainedObservedTrajectories
import Submission.Lib.K4PolynomialNorming.StationaryKernelPaths

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- An original-law conditional cap lifts to every causally retained
full prefix of a stationary trajectory. Restrictions do not change the
reference incidence law. -/
theorem stationary_retained_history_observation_cap {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (w₀ : X → ENNReal) (hw₀ : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n)))
    (W : Set X) (hW : MeasurableSet W)
    (hretain : ∀ n h x, α n h x ≤ W.indicator (fun _ => 1) x)
    (obs : X → V) (hobs : Measurable obs) (ν : Measure V) (K : ENNReal)
    (hcap : ∀ᵐ x ∂P, ((S x).restrict W).map obs ≤ K • ν) (n : ℕ) :
    ∀ᵐ h ∂((kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n)).withDensity
        (causalRetentionWeights w₀ α n),
      (((fullHistoryMarkovKernel (fun _ => S) n).withDensity (α n)) h).map obs ≤ K • ν := by
  let Q := kernelPathMeasure P (fun _ => S)
  let θ := (Q.map (Preorder.frestrictLe n)).withDensity (causalRetentionWeights w₀ α n)
  let last : ((i : Finset.Iic n) → X) → X := fun h => h ⟨n, by simp⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hα1 : ∀ k h x, α k h x ≤ 1 := by
    intro k h x
    apply (hretain k h x).trans
    by_cases hx : x ∈ W <;> simp [hx]
  have hθ : θ ≤ Q.map (Preorder.frestrictLe n) := by
    calc
      _ ≤ (Q.map (Preorder.frestrictLe n)).withDensity (fun _ => 1) :=
        withDensity_mono (Filter.Eventually.of_forall
          (causalRetentionWeights_le_one w₀ hw₀ α hα1 n))
      _ = _ := by simp
  have hmarg : θ.map last ≤ P := by
    calc
      _ ≤ (Q.map (Preorder.frestrictLe n)).map last := Measure.map_mono hθ hlast
      _ = Q.map (fun x => x n) := by
        rw [Measure.map_map hlast (by fun_prop)]
        rfl
      _ = P := kernelPathMeasure_stationary_marginal P (fun _ => S) (fun _ => hS) n
  have hpull : ∀ᵐ h ∂θ, ((S (last h)).restrict W).map obs ≤ K • ν :=
    ae_of_ae_map hlast.aemeasurable (ae_mono hmarg hcap)
  filter_upwards [hpull] with h hh
  have hdom : (S (last h)).withDensity (α n h) ≤ (S (last h)).restrict W := by
    calc
      _ ≤ (S (last h)).withDensity (W.indicator (fun _ => 1)) :=
        withDensity_mono (Filter.Eventually.of_forall (hretain n h))
      _ = _ := withDensity_indicator_one hW
  rw [Kernel.withDensity_apply _ (hα n)]
  exact (Measure.map_mono hdom hobs).trans hh

/-- Original-law caps suffice throughout an arbitrary number of actual
retained stationary steps; they are not assumptions on independent draws. -/
theorem stationary_retained_observed_process_domination {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n)))
    (W : Set X) (hW : MeasurableSet W)
    (hretain : ∀ n h x, α n h x ≤ W.indicator (fun _ => 1) x)
    (start : X → Ω) (hstart : Measurable start)
    (obs : X → V) (hobs : Measurable obs)
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) [SigmaFinite ν] (K : ENNReal)
    (hzero : (P.withDensity w₀).map start ≤ μ)
    (hcap : ∀ᵐ x ∂P, ((S x).restrict W).map obs ≤ K • ν) (N : ℕ) :
    ((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
      causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))).map
        (fun x => causalObservedHistory start (fun _ z => obs z.2) N
          (Preorder.frestrictLe N x)) ≤
      K ^ N • (μ.prod (Measure.pi (fun _ : Fin N => ν))) := by
  have hα1 : ∀ n h x, α n h x ≤ 1 := by
    intro n h x
    apply (hretain n h x).trans
    by_cases hx : x ∈ W <;> simp [hx]
  apply retained_trajectory_observed_history_domination P (fullHistoryMarkovKernel (fun _ => S))
    w₀ hw₀ hw₀1 α hα hα1 start hstart (fun _ z => obs z.2)
    (fun _ => hobs.comp measurable_snd) μ ν K hzero N
  intro n _
  exact stationary_retained_history_observation_cap P S hS w₀ hw₀1 α hα W hW hretain obs hobs ν K hcap n


/-- Uniform palette bounds control a pencil selected from the complete
past of the actual stationary trajectory. -/
theorem stationary_trajectory_history_pencil_mass {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (obs : X → V) (hobs : Measurable obs) (π : Measure V) (K p : ENNReal)
    (hcap : ∀ᵐ x ∂P, (S x).map obs ≤ K • π) (n : ℕ)
    (A : Set ((((i : Finset.Iic n) → X)) × V)) (hA : MeasurableSet A)
    (hthin : ∀ h, π (Prod.mk h ⁻¹' A) ≤ p) :
    (kernelPathMeasure P (fun _ => S))
      {x | (Preorder.frestrictLe n x, obs (x (n+1))) ∈ A} ≤ K * p := by
  let Q := kernelPathMeasure P (fun _ => S)
  letI : IsProbabilityMeasure Q := kernelPathMeasure_isProbability P (fun _ => S)
  let θ := Q.map (Preorder.frestrictLe n)
  letI : IsProbabilityMeasure θ := by
    apply Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr
    infer_instance
  let last : ((i : Finset.Iic n) → X) → X := fun h => h ⟨n, by simp⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hmarg : θ.map last = P := by
    rw [show θ = Q.map (Preorder.frestrictLe n) from rfl,
      Measure.map_map hlast (by fun_prop)]
    exact kernelPathMeasure_stationary_marginal P (fun _ => S) (fun _ => hS) n
  have hpull : ∀ᵐ h ∂θ, (S (last h)).map obs ≤ K • π := by
    have hmap : ∀ᵐ x ∂θ.map last, (S x).map obs ≤ K • π := by
      rw [hmarg]
      exact hcap
    exact ae_of_ae_map hlast.aemeasurable hmap
  let B : Set ((((i : Finset.Iic n) → X)) × X) :=
    {z | (z.1, obs z.2) ∈ A}
  have hB : MeasurableSet B := hA.preimage (measurable_fst.prodMk (hobs.comp measurable_snd))
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := P) (κ := fullHistoryMarkovKernel (fun _ => S)) (a := n)
  calc
    _ = (θ ⊗ₘ fullHistoryMarkovKernel (fun _ => S) n) B := by
      change Q {x | (Preorder.frestrictLe n x, obs (x (n+1))) ∈ A} =
        ((Q.map (Preorder.frestrictLe n)) ⊗ₘ fullHistoryMarkovKernel (fun _ => S) n) B
      have hj : (Q.map (Preorder.frestrictLe n)) ⊗ₘ fullHistoryMarkovKernel (fun _ => S) n =
          Q.map (fun x => (Preorder.frestrictLe n x, x (n+1))) := hjoint
      rw [hj, Measure.map_apply (by fun_prop) hB]
      rfl
    _ = ∫⁻ h, fullHistoryMarkovKernel (fun _ => S) n h (Prod.mk h ⁻¹' B) ∂θ :=
      Measure.compProd_apply hB
    _ ≤ ∫⁻ _h, K * p ∂θ := by
      apply lintegral_mono_ae
      filter_upwards [hpull] with h hh
      have hsec : MeasurableSet (Prod.mk h ⁻¹' A) := hA.preimage measurable_prodMk_left
      have hc := Measure.le_iff.mp hh _ hsec
      rw [Measure.map_apply hobs hsec, Measure.smul_apply, smul_eq_mul] at hc
      exact hc.trans (mul_le_mul' le_rfl (hthin h))
    _ = _ := by simp [θ, Q, kernelPathMeasure]


/-- Short next states are charged to their original stationary marginal;
full-history pencil choices are charged to the prepared palette. Their
sum bounds the loss of the complete causally retained trajectory. -/
theorem stationary_causal_retention_mass_bound {X V : Type*}
    [MeasurableSpace X] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (W : Set X) (hW : MeasurableSet W)
    (obs : X → V) (hobs : Measurable obs) (π : Measure V) (K : ENNReal)
    (hcap : ∀ᵐ x ∂P, (S x).map obs ≤ K • π)
    (A : (n : ℕ) → Set ((((i : Finset.Iic n) → X)) × V))
    (hA : ∀ n, MeasurableSet (A n)) (p : ℕ → ENNReal)
    (hthin : ∀ n h, π (Prod.mk h ⁻¹' A n) ≤ p n)
    (hdefect : ∀ n h y, 1 - α n h y ≤
      Wᶜ.indicator (fun _ => 1) y + (A n).indicator (fun _ => 1) (h,obs y)) (N : ℕ) :
    (P.withDensity w₀) univ ≤
      ((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
        causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))) univ +
      ∑ n ∈ Finset.range N, (P Wᶜ + K * p n) := by
  classical
  let Q := kernelPathMeasure P (fun _ => S)
  have hloss (n : ℕ) : (Q.withDensity (fun x =>
      1 - α n (Preorder.frestrictLe n x) (x (n+1)))) univ ≤ P Wᶜ + K * p n := by
    let badShort : Set (ℕ → X) := {x | x (n+1) ∉ W}
    let badPencil : Set (ℕ → X) := {x | (Preorder.frestrictLe n x,obs (x (n+1))) ∈ A n}
    have hs : MeasurableSet badShort := hW.compl.preimage (measurable_pi_apply (n+1))
    have hp : MeasurableSet badPencil := (hA n).preimage (by fun_prop)
    have hm : Q badShort = P Wᶜ := by
      have hh := congrArg (fun μ : Measure X => μ Wᶜ)
        (kernelPathMeasure_stationary_marginal P (fun _ => S) (fun _ => hS) (n+1))
      rw [Measure.map_apply (by fun_prop) hW.compl] at hh
      exact hh
    have hpen : Q badPencil ≤ K * p n :=
      stationary_trajectory_history_pencil_mass P S hS obs hobs π K (p n) hcap n
        (A n) (hA n) (hthin n)
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


end Submission.Lib.K4PolynomialNorming
