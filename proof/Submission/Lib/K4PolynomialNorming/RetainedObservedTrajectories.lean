/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RetainedPathObservation
import Submission.Lib.K4PolynomialNorming.ObservedProcessDomination

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

noncomputable def causalObservedHistory {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (start : X → Ω)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V) :
    (n : ℕ) → ((i : Finset.Iic n) → X) → Ω × (Fin n → V)
  | 0, h => (start (h ⟨0, by simp⟩), fun i => Fin.elim0 i)
  | n+1, h => appendObservedCoordinate n
      (causalObservedHistory start obs n (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n) h),
        obs n (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n) h, h ⟨n+1, by simp⟩))

theorem causalObservedHistory_measurable {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (start : X → Ω) (hstart : Measurable start)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V)
    (hobs : ∀ n, Measurable (obs n)) (n : ℕ) :
    Measurable (causalObservedHistory start obs n) := by
  induction n with
  | zero => exact (hstart.comp (measurable_pi_apply _)).prodMk measurable_const
  | succ n ih =>
    have hr : Measurable (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n)) :=
      measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
    apply (appendObservedCoordinate n).measurable.comp
    exact (ih.comp hr).prodMk ((hobs n).comp (hr.prodMk (measurable_pi_apply _)))

noncomputable def causalRetentionWeights {X : Type*}
    (w₀ : X → ENNReal)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal) :
    (n : ℕ) → ((i : Finset.Iic n) → X) → ENNReal
  | 0, h => w₀ (h ⟨0, by simp⟩)
  | n+1, h => causalRetentionWeights w₀ α n (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n) h) *
      α n (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n) h) (h ⟨n+1, by simp⟩)

theorem causalRetentionWeights_measurable {X : Type*} [MeasurableSpace X]
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (n : ℕ) :
    Measurable (causalRetentionWeights w₀ α n) := by
  induction n with
  | zero => exact hw₀.comp (measurable_pi_apply _)
  | succ n ih =>
    have hr : Measurable (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ n)) :=
      measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
    exact (ih.comp hr).mul ((hα n).comp (hr.prodMk (measurable_pi_apply _)))

theorem causalRetentionWeights_le_one {X : Type*}
    (w₀ : X → ENNReal) (hw₀ : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n h x, α n h x ≤ 1) (n : ℕ) :
    ∀ h, causalRetentionWeights w₀ α n h ≤ 1 := by
  induction n with
  | zero => intro h; exact hw₀ _
  | succ n ih =>
    intro h
    exact (mul_le_mul' (ih _) (hα n _ _)).trans_eq (one_mul 1)

theorem trajectory_initial_state_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    [∀ n, IsMarkovKernel (κ n)] :
    (Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).map (fun x => x 0) = P := by
  have hprefix : (Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).map
      (Preorder.frestrictLe (π := fun _ : ℕ => X) 0) =
      P.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm := by
    rw [Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have hfun : (fun x : ℕ → X => x 0) =
      (fun h : (i : Finset.Iic 0) → X => h ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hprefix,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change P.map id = P
  simp

/-- A finite string of actual trajectory observations has the product
ceiling when each causally retained transition has its conditional ceiling
on the full retained past. The measure is the original trajectory law
weighted by the complete product of retention factors. -/
theorem retained_trajectory_observed_history_domination {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    [∀ n, IsMarkovKernel (κ n)]
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (start : X → Ω) (hstart : Measurable start)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V)
    (hobs : ∀ n, Measurable (obs n))
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) [SigmaFinite ν] (K : ENNReal)
    (hzero : (P.withDensity w₀).map start ≤ μ) (N : ℕ)
    (hstep : ∀ n < N, ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).map
        (Preorder.frestrictLe n)).withDensity (causalRetentionWeights w₀ α n),
      (((κ n).withDensity (α n)) h).map (fun y => obs n (h,y)) ≤ K • ν) :
    ((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).withDensity (fun x =>
      causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))).map
        (fun x => causalObservedHistory start obs N (Preorder.frestrictLe N x)) ≤
      K ^ N • (μ.prod (Measure.pi (fun _ : Fin N => ν))) := by
  let Q := Kernel.trajMeasure (X := fun _ : ℕ => X) P κ
  have hw n := causalRetentionWeights_measurable w₀ hw₀ α hα n
  have hw1 n := causalRetentionWeights_le_one w₀ hw₀1 α hα1 n
  have hg n := causalObservedHistory_measurable start hstart obs hobs n
  have hall : ∀ n, n ≤ N →
      (Q.withDensity (fun x => causalRetentionWeights w₀ α n (Preorder.frestrictLe n x))).map
        (fun x => causalObservedHistory start obs n (Preorder.frestrictLe n x)) ≤
      K ^ n • (μ.prod (Measure.pi (fun _ : Fin n => ν))) := by
    intro n
    induction n with
    | zero =>
      intro _
      have hi := initialObservedLaw_le (P.withDensity w₀) start hstart μ ν hzero
      have hm : Measurable (fun x : X => (start x, fun i : Fin 0 => (Fin.elim0 i : V))) :=
        hstart.prodMk measurable_const
      have hmap := map_withDensity_pullback Q (fun x : ℕ → X => x 0)
        (by fun_prop) w₀ hw₀
      rw [show Q.map (fun x => x 0) = P from trajectory_initial_state_law P κ] at hmap
      rw [← hmap, Measure.map_map hm (by fun_prop)] at hi
      simpa only [pow_zero, one_smul, causalObservedHistory, causalRetentionWeights,
        Preorder.frestrictLe_apply, Function.comp_def] using hi
    | succ n ih =>
      intro hn
      have hpast : ((((Q.map (Preorder.frestrictLe n)).withDensity
          (causalRetentionWeights w₀ α n)).map (causalObservedHistory start obs n))) ≤
          K ^ n • (μ.prod (Measure.pi (fun _ : Fin n => ν))) := by
        rw [← map_withDensity_pullback Q (Preorder.frestrictLe n) (by fun_prop)
          (causalRetentionWeights w₀ α n) (hw n), Measure.map_map (hg n) (by fun_prop)]
        exact ih (Nat.le_of_succ_le hn)
      have h := retainedTrajectory_observation_le P κ n
        (causalRetentionWeights w₀ α n) (hw n) (hw1 n) (α n) (hα n) (hα1 n)
        (μ.prod (Measure.pi (fun _ : Fin n => ν))) ν
        (causalObservedHistory start obs n) (hg n) (obs n) (hobs n)
        (K^n) K hpast (hstep n (Nat.lt_of_succ_le hn))
      have hm : Measurable (fun x : ℕ → X =>
          (causalObservedHistory start obs n (Preorder.frestrictLe n x),
            obs n (Preorder.frestrictLe n x, x (n+1)))) := by fun_prop
      have hmap := Measure.map_mono h (appendObservedCoordinate n).measurable
      rw [Measure.map_smul _ (appendObservedCoordinate n).measurable.aemeasurable,
        (appendObservedCoordinate_measurePreserving μ ν n).map_eq,
        Measure.map_map (appendObservedCoordinate n).measurable hm, ← pow_succ] at hmap
      exact hmap
  exact hall N le_rfl


theorem appendObservedCoordinate_apply {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] (n : ℕ)
    (z : (Ω × (Fin n → V)) × V) :
    appendObservedCoordinate n z = (z.1.1, Fin.snoc z.1.2 z.2) := by
  simp [appendObservedCoordinate, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_last]
  rfl


/-- Successful paths on which all retention factors equal one keep their
original mass when compared with the retained observed law. -/
theorem original_event_le_retained_observation {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure X) (w : X → ENNReal) (f : X → Y) (hf : Measurable f)
    (G : Set X) (hG : MeasurableSet G) (E : Set Y) (hE : MeasurableSet E)
    (hweight : ∀ x ∈ G, 1 ≤ w x) (hobs : ∀ x ∈ G, f x ∈ E) :
    Q G ≤ ((Q.withDensity w).map f) E := by
  rw [Measure.map_apply hf hE, withDensity_apply _ (hE.preimage hf)]
  calc
    Q G = ∫⁻ _x in G, (1 : ENNReal) ∂Q := by simp
    _ ≤ ∫⁻ x in G, w x ∂Q := setLIntegral_mono' hG hweight
    _ ≤ ∫⁻ x in f ⁻¹' E, w x ∂Q := lintegral_mono' (Measure.restrict_mono (fun x hx => hobs x hx) le_rfl) le_rfl


/-- Unit retention along a successful path preserves its original weight. -/
theorem causalRetentionWeights_eq_one_on_path {X : Type*}
    (w₀ : X → ENNReal)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (N : ℕ) (x : ℕ → X) (hzero : w₀ (x 0) = 1)
    (hstep : ∀ k < N, α k (Preorder.frestrictLe k x) (x (k+1)) = 1) :
    causalRetentionWeights w₀ α N (Preorder.frestrictLe N x) = 1 := by
  have hall : ∀ n, (∀ k < n, α k (Preorder.frestrictLe k x) (x (k+1)) = 1) →
      causalRetentionWeights w₀ α n (Preorder.frestrictLe n x) = 1 := by
    intro n
    induction n with
    | zero => intro _; exact hzero
    | succ n ih =>
      intro hs
      change causalRetentionWeights w₀ α n (Preorder.frestrictLe n x) *
        α n (Preorder.frestrictLe n x) (x (n+1)) = 1
      rw [ih (fun k hk => hs k (Nat.lt_succ_of_lt hk)), hs n (Nat.lt_succ_self n), one_mul]
  exact hall N hstep


/-- Causal retention loses at most the sum of its defects measured under
the unrestricted original trajectory. The starting weight and all later
retentions remain unnormalized. -/
theorem trajectory_causal_retention_mass_budget {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    [∀ n, IsMarkovKernel (κ n)]
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (N : ℕ) :
    (P.withDensity w₀) univ ≤
      ((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).withDensity (fun x =>
        causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))) univ +
      ∑ n ∈ Finset.range N,
        ((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).withDensity (fun x =>
          1 - α n (Preorder.frestrictLe n x) (x (n+1)))) univ := by
  let Q := Kernel.trajMeasure (X := fun _ : ℕ => X) P κ
  let M (n : ℕ) := (Q.withDensity (fun x =>
    causalRetentionWeights w₀ α n (Preorder.frestrictLe n x))) univ
  let loss (n : ℕ) := (Q.withDensity (fun x =>
    1 - α n (Preorder.frestrictLe n x) (x (n+1)))) univ
  have hM0 : M 0 = (P.withDensity w₀) univ := by
    have h := congrArg (fun μ : Measure X => ∫⁻ z, w₀ z ∂μ) (trajectory_initial_state_law P κ)
    rw [lintegral_map hw₀ (by fun_prop)] at h
    simpa only [M, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      causalRetentionWeights, Preorder.frestrictLe_apply] using h
  have hstep (n : ℕ) : M n ≤ M (n+1) + loss n := by
    have hw := (causalRetentionWeights_measurable w₀ hw₀ α hα (n+1)).comp
      (by fun_prop : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => X) (n+1)))
    simp only [M, loss, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      _ ≤ ∫⁻ x, (causalRetentionWeights w₀ α (n+1) (Preorder.frestrictLe (n+1) x) +
          (1 - α n (Preorder.frestrictLe n x) (x (n+1)))) ∂Q := by
        apply lintegral_mono
        intro x
        let a := α n (Preorder.frestrictLe n x) (x (n+1))
        let w := causalRetentionWeights w₀ α n (Preorder.frestrictLe n x)
        have ha : a ≤ 1 := hα1 n _ _
        have hww : w ≤ 1 := causalRetentionWeights_le_one w₀ hw₀1 α hα1 n _
        change w ≤ w * a + (1-a)
        calc
          w = w * (a + (1-a)) := by rw [add_tsub_cancel_of_le ha, mul_one]
          _ = w * a + w * (1-a) := mul_add _ _ _
          _ ≤ w * a + (1-a) := add_le_add le_rfl
            (by simpa only [one_mul] using mul_le_mul' hww (le_refl (1-a)))
      _ = _ := lintegral_add_left hw _
  have hbudget : ∀ n, M 0 ≤ M n + ∑ k ∈ Finset.range n, loss k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ M n + ∑ k ∈ Finset.range n, loss k := ih
        _ ≤ (M (n+1) + loss n) + ∑ k ∈ Finset.range n, loss k :=
          add_le_add (hstep n) le_rfl
        _ = _ := by rw [Finset.sum_range_succ]; ac_rfl
  simpa only [hM0, M, loss] using hbudget N


section

attribute [local irreducible] causalObservedHistory causalRetentionWeights

/-- The endpoint law of six actual retained transitions, expressed in
start/control rows and signed duration coordinates. -/
theorem retained_trajectory_six_control_endpoint_law {X Ω C : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace C]
    (P : Measure X) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    [∀ n, IsMarkovKernel (κ n)]
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h x, α n h x ≤ 1)
    (start : X → Ω) (hstart : Measurable start)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → C × ℝ)
    (hobs : ∀ n, Measurable (obs n))
    (μ : Measure Ω) [SFinite μ] (π : Measure C) [SigmaFinite π] (K : ENNReal)
    (hzero : (P.withDensity w₀).map start ≤ μ)
    (hstep : ∀ n < 6, ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).map
        (Preorder.frestrictLe n)).withDensity (causalRetentionWeights w₀ α n),
      (((κ n).withDensity (α n)) h).map (fun y => obs n (h,y)) ≤
        K • π.prod (volume : Measure ℝ))
    (t₀ : Ω × (Fin 6 → C) → ℝ) (ht₀ : Measurable t₀) :
    ((Kernel.trajMeasure (X := fun _ : ℕ => X) P κ).withDensity (fun x =>
      causalRetentionWeights w₀ α 6 (Preorder.frestrictLe 6 x))).map
        (fun x => signedDurationEndpointCoordinates t₀
          (separateObservedCoordinates 6
            (causalObservedHistory start obs 6 (Preorder.frestrictLe 6 x)))) ≤
      K ^ 6 • ((μ.prod (Measure.pi (fun _ : Fin 6 => π))).prod
        (volume : Measure ((Fin 5 → ℝ) × ℝ))) := by
  have h := retained_trajectory_observed_history_domination P κ w₀ hw₀ hw₀1 α hα hα1
    start hstart obs hobs μ (π.prod volume) K hzero 6 hstep
  have hg := (causalObservedHistory_measurable start hstart obs hobs 6).comp
    (by fun_prop : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => X) 6))
  have hm := ((signedDurationEndpointCoordinates_measurePreserving
    (μ.prod (Measure.pi (fun _ : Fin 6 => π))) t₀ ht₀).measurable).comp
      (separateObservedCoordinates 6).measurable
  have hb := sixControlEndpointLaw_domination μ π _ (K^6) h t₀ ht₀
  rw [Measure.map_map
    (f := fun x : ℕ → X => causalObservedHistory start obs 6
      (Preorder.frestrictLe 6 x))
    (g := fun z : Ω × (Fin 6 → C × ℝ) => signedDurationEndpointCoordinates t₀
      (separateObservedCoordinates 6 z)) hm hg] at hb
  exact hb


end

end Submission.Lib.K4PolynomialNorming
