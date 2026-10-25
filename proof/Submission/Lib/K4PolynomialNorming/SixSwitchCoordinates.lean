/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RetainedTrajectorySupport
import Submission.Lib.K4PolynomialNorming.NormalizedSwitchingCoordinates
import Submission.Lib.K4PolynomialNorming.StationaryWeightedSupport

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Matrix

namespace Submission.Lib.K4PolynomialNorming

/-- Actual initial incidence and six controls, together with consecutive
normalized endpoint-time differences in the endpoint-volume coordinates. -/
noncomputable def sixSwitchCoordinates {L C : Type*} [MeasurableSpace C]
    (control : L → C) (a h : ℝ) (x : ℕ → L × ℝ) :
    ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ) :=
  ((x 0,fun i => control (x (i.1+1)).1),
    splitHeadCoordinates 5 (consecutiveTimeIncrements (((x 0).2-a)/h)
      (fun i : Fin 6 => ((x (i.1+1)).2-a)/h)))

theorem sixSwitchCoordinates_eq_observed {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C]
    (control : L → C) (a h : ℝ) (x : ℕ → L × ℝ) :
    sixSwitchCoordinates control a h x =
      signedDurationEndpointCoordinates (fun z : (L × ℝ) × (Fin 6 → C) => (z.1.2-a)/h)
        (separateObservedCoordinates 6
          (causalObservedHistory (id : L × ℝ → L × ℝ)
            (fun _ z => (control z.2.1,(z.2.2-a)/h)) 6 (Preorder.frestrictLe 6 x))) := by
  have he : causalObservedHistory (id : L × ℝ → L × ℝ)
      (fun _ z => (control z.2.1,(z.2.2-a)/h)) 6 (Preorder.frestrictLe 6 x) =
        (x 0,fun i : Fin 6 => (control (x (i.1+1)).1,((x (i.1+1)).2-a)/h)) := by
    apply Prod.ext
    · exact causalObservedHistory_on_path_fst _ _ _ _
    · funext i
      exact causalObservedHistory_on_path_snd_apply _ _ _ _ i
  rw [he,separateObservedCoordinates_apply]
  rfl

theorem sixSwitchCoordinates_measurable {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C]
    (control : L → C) (hcontrol : Measurable control) (a h : ℝ) :
    Measurable (sixSwitchCoordinates control a h) := by
  let obs (n : ℕ) : (((i : Finset.Iic n) → L × ℝ) × (L × ℝ)) → C × ℝ :=
    fun z => (control z.2.1,(z.2.2-a)/h)
  let t₀ : ((L × ℝ) × (Fin 6 → C)) → ℝ := fun z => (z.1.2-a)/h
  have ht₀ : Measurable t₀ := by fun_prop
  have hg : Measurable (fun x : ℕ → L × ℝ =>
      causalObservedHistory (id : L × ℝ → L × ℝ) obs 6 (Preorder.frestrictLe 6 x)) :=
    (causalObservedHistory_measurable (id : L × ℝ → L × ℝ) measurable_id obs
      (fun _ => by dsimp only [obs]; fun_prop) 6).comp (by fun_prop)
  have hm := ((signedDurationEndpointCoordinates_measurePreserving
    (0 : Measure ((L × ℝ) × (Fin 6 → C))) t₀ ht₀).measurable).comp
      (separateObservedCoordinates (Ω := L × ℝ) (C := C) (T := ℝ) 6).measurable
  have he : sixSwitchCoordinates control a h =
      (signedDurationEndpointCoordinates t₀ ∘
        separateObservedCoordinates (Ω := L × ℝ) (C := C) (T := ℝ) 6) ∘
          (fun x : ℕ → L × ℝ =>
            causalObservedHistory (id : L × ℝ → L × ℝ) obs 6 (Preorder.frestrictLe 6 x)) := by
    funext x
    exact sixSwitchCoordinates_eq_observed control a h x
  rw [he]
  exact hm.comp hg

theorem sixSwitchCoordinates_durations {L C : Type*} [MeasurableSpace C]
    (control : L → C) (a h : ℝ) (x : ℕ → L × ℝ) :
    (splitHeadCoordinates 5).symm (sixSwitchCoordinates control a h x).2 =
      consecutiveTimeIncrements (((x 0).2-a)/h)
        (fun i : Fin 6 => ((x (i.1+1)).2-a)/h) :=
  (splitHeadCoordinates 5).symm_apply_apply _

theorem consecutiveTimeIncrements_on_path (n : ℕ) (t : ℕ → ℝ) (i : Fin n) :
    consecutiveTimeIncrements (t 0) (fun j : Fin n => t (j.1+1)) i =
      t (i.1+1)-t i.1 := by
  have he : (Fin.cons (t 0) (fun j : Fin n => t (j.1+1)) : Fin (n+1) → ℝ) =
      fun j => t j.1 := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    simp only [Fin.cons_succ,Fin.val_succ]
  unfold consecutiveTimeIncrements
  rw [he]
  rfl

theorem sixSwitchCoordinates_durations_apply {L C : Type*} [MeasurableSpace C]
    (control : L → C) (a h : ℝ) (x : ℕ → L × ℝ) (i : Fin 6) :
    (splitHeadCoordinates 5).symm (sixSwitchCoordinates control a h x).2 i =
      (((x (i.1+1)).2-a)/h)-(((x i.1).2-a)/h) := by
  rw [sixSwitchCoordinates_durations]
  exact consecutiveTimeIncrements_on_path 6 (fun k => ((x k).2-a)/h) i

theorem sixSwitchCoordinates_unit_box {L C : Type*} [MeasurableSpace C]
    (control : L → C) (a h : ℝ) (hh : 0 < h) (x : ℕ → L × ℝ)
    (ht : ∀ k ≤ 6, (x k).2 ∈ Icc a (a+h)) :
    ∀ i, |(splitHeadCoordinates 5).symm (sixSwitchCoordinates control a h x).2 i| ≤ 1 := by
  rw [sixSwitchCoordinates_durations]
  have hb := normalized_signed_durations_mem_unit_box a h (x 0).2 hh
    (fun i : Fin 6 => (x (i.1+1)).2) (ht 0 (by decide))
    (fun i => ht (i.1+1) (by have hi := i.2; omega))
  intro i
  exact abs_le.mpr ⟨hb.1 i,hb.2 i⟩

/-- The two actual direction-column matrices determined by the six
observed control codes. -/
noncomputable def directionBlockMatrix {C : Type*}
    (v : C → EuclideanSpace ℝ (Fin 3)) (c : Fin 6 → C) (b : Fin 2) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun a i => v (c ⟨3*b.1+i.1,by have hb := b.2; have hi := i.2; omega⟩) a

theorem directionBlockMatrix_sixSwitchCoordinates {L C : Type*} [MeasurableSpace C]
    (control : L → C) (v : C → EuclideanSpace ℝ (Fin 3)) (a h : ℝ)
    (x : ℕ → L × ℝ) (b : Fin 2) :
    directionBlockMatrix v (sixSwitchCoordinates control a h x).1.2 b =
      Matrix.of (fun k i : Fin 3 => v (control (x (3*b.1+i.1+1)).1) k) := rfl

/-- Reading the two direction blocks recovers all six observed directions
in precisely the order used by the two-basis endpoint polynomial. -/
theorem directionBlockMatrix_append {C : Type*}
    (v : C → EuclideanSpace ℝ (Fin 3)) (c : Fin 6 → C) :
    Fin.append (fun i a => directionBlockMatrix v c 0 a i)
      (fun i a => directionBlockMatrix v c 1 a i) =
        fun i a => v (c i) a := by
  funext k a
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]
    apply congrArg (fun j : Fin 6 => v (c j) a)
    exact Fin.ext (by simp)
  · rw [Fin.append_right]
    apply congrArg (fun j : Fin 6 => v (c j) a)
    exact Fin.ext (by simp [Nat.add_comm])

/-- The forward base coordinate is exactly the total signed displacement
of the six observed directions. -/
theorem directionBlockMatrix_displacement {C : Type*}
    (v : C → EuclideanSpace ℝ (Fin 3)) (c : Fin 6 → C) (δ : Fin 6 → ℝ) :
    directionBlockMatrix v c 0 *ᵥ (fun i => δ (Fin.castAdd 3 i)) +
      directionBlockMatrix v c 1 *ᵥ (fun i => δ (Fin.natAdd 3 i)) =
        fun a => ∑ i : Fin 6, δ i * v (c i) a := by
  funext a
  change (∑ i, directionBlockMatrix v c 0 a i * δ (Fin.castAdd 3 i)) +
    (∑ i, directionBlockMatrix v c 1 a i * δ (Fin.natAdd 3 i)) = _
  rw [Fin.sum_univ_add (a := 3) (b := 3) (fun i : Fin 6 => δ i * v (c i) a)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h := congrFun (congrFun (directionBlockMatrix_append v c) (Fin.castAdd 3 i)) a
    simp only [Fin.append_left] at h
    rw [h,mul_comm]
  · apply Finset.sum_congr rfl
    intro i _
    have h := congrFun (congrFun (directionBlockMatrix_append v c) (Fin.natAdd 3 i)) a
    simp only [Fin.append_right] at h
    rw [h,mul_comm]

/-- Original time-block support supplies the duration box in the actual
retained six-switch coordinates. -/
theorem sixSwitchCoordinates_unit_box_ae {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C]
    (P : Measure (L × ℝ)) [IsProbabilityMeasure P]
    (K : ℕ → Kernel (L × ℝ) (L × ℝ)) [∀ n, IsMarkovKernel (K n)]
    (hK : ∀ n, K n ∘ₘ P = P) (w : (ℕ → L × ℝ) → ENNReal)
    (control : L → C) (a h : ℝ) (hh : 0 < h)
    (ht : ∀ᵐ z ∂P, z.2 ∈ Icc a (a+h)) :
    ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
      ∀ i, |(splitHeadCoordinates 5).symm (sixSwitchCoordinates control a h x).2 i| ≤ 1 := by
  filter_upwards [kernelPathMeasure_weighted_ae_states P K hK w
    (fun _ z => z.2 ∈ Icc a (a+h)) (fun _ => ht)] with x hx
  exact sixSwitchCoordinates_unit_box control a h hh x (fun k _ => hx k)

/-- The direction-entry bounds of the unchanged incidence law hold for
both observed direction matrices under the same weighted path law. -/
theorem directionBlockMatrix_sixSwitchCoordinates_abs_le_ae {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C]
    (P : Measure (L × ℝ)) [IsProbabilityMeasure P]
    (K : ℕ → Kernel (L × ℝ) (L × ℝ)) [∀ n, IsMarkovKernel (K n)]
    (hK : ∀ n, K n ∘ₘ P = P) (w : (ℕ → L × ℝ) → ENNReal)
    (control : L → C) (v : C → EuclideanSpace ℝ (Fin 3)) (a h U : ℝ)
    (hv : ∀ᵐ z ∂P, ∀ j, |v (control z.1) j| ≤ U) :
    ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
      ∀ (b : Fin 2) j i,
        |directionBlockMatrix v (sixSwitchCoordinates control a h x).1.2 b j i| ≤ U := by
  filter_upwards [kernelPathMeasure_weighted_ae_states P K hK w
    (fun _ z => ∀ j, |v (control z.1) j| ≤ U) (fun _ => hv)] with x hx
  intro b j i
  rw [directionBlockMatrix_sixSwitchCoordinates]
  exact hx (3*b.1+i.1+1) j

end Submission.Lib.K4PolynomialNorming
