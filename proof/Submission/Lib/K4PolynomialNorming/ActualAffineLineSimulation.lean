/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualSwitchedSupport
import Submission.Lib.K4PolynomialNorming.AffineLineSimulation
import Submission.Lib.K4PolynomialNorming.CodedSixSwitchEndpoint

open Set MeasureTheory ProbabilityTheory MvPolynomial
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching

/-- The assigned physical point at normalized block time. -/
noncomputable def affineIncidencePoint {L : Type*}
    (a h : ℝ) (base velocity : L → Fin 3 → ℝ) (height speed : L → ℝ)
    (z : L × ℝ) : (Fin 3 → ℝ) × ℝ :=
  affineLinePoint base velocity height speed z.1 ((z.2-a)/h)

theorem affineIncidencePoint_measurable {L : Type*} [MeasurableSpace L]
    (a h : ℝ) (base velocity : L → Fin 3 → ℝ) (height speed : L → ℝ)
    (hb : Measurable base) (hu : Measurable velocity)
    (hz : Measurable height) (hw : Measurable speed) :
    Measurable (affineIncidencePoint a h base velocity height speed) := by
  have ht : Measurable (fun z : L × ℝ => (z.2-a)/h) := by fun_prop
  exact ((hb.comp measurable_fst).add (ht.smul (hu.comp measurable_fst))).prodMk
    ((hz.comp measurable_fst).add (ht.mul (hw.comp measurable_fst)))

/-- Original whole-block fits and the geometric shared-state certificate
supply the actual six-switch polynomial simulation almost everywhere.
All original fits and bounds are transferred through the same stationary
path law before any weighting or successful-path restriction. -/
theorem actual_affine_six_switch_endpoint_error_ae {L Q C : Type*}
    [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace Q] [StandardBorelSpace Q] [MeasurableSpace C]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → C) (v : C → EuclideanSpace ℝ (Fin 3))
    (a h : ℝ) (hh : 0 < h) (Long : Set L) (hLong : MeasurableSet Long)
    (base velocity : L → Fin 3 → ℝ) (height speed : L → ℝ)
    (hb : Measurable base) (hu : Measurable velocity)
    (hz : Measurable height) (hw : Measurable speed)
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (ε η τ ζ B U A R : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a+h))
    (hvelocity : ∀ᵐ z ∂ν ⊗ₘ κ,
      ‖velocity z.1-(fun j : Fin 3 => v (control z.1) j)‖ ≤ τ)
    (hcodes : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
    (hfit : ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1,
      |speed z.1-∑ j, velocity z.1 j * MvPolynomial.eval
        (base z.1+t • velocity z.1) (T j)| ≤ ε)
    (hconf : ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, ‖base z.1+t • velocity z.1‖ ≤ R)
    (hfield : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j, |MvPolynomial.eval x (T j)| ≤ B)
    (hspace : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)),
      ∀ y ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j,
        |MvPolynomial.eval x (T j)-MvPolynomial.eval y (T j)| ≤ A*‖x-y‖)
    (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂ν ⊗ₘ κ, Valid z)
    (hshared : ∀ old redraw, state redraw = state old → Valid old → Valid redraw →
      (old.2-a)/h ∈ Icc (0:ℝ) 1 → redraw.1 ∈ Long →
      ‖(affineLinePoint base velocity height speed redraw.1 ((old.2-a)/h)).1-
        (affineIncidencePoint a h base velocity height speed old).1‖ ≤ η ∧
      |(affineLinePoint base velocity height speed redraw.1 ((old.2-a)/h)).2-
        (affineIncidencePoint a h base velocity height speed old).2| ≤ ζ)
    (w : (ℕ → L × ℝ) → ENNReal)
    (hretainedLong : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      ∀ k < 6, (x (k+1)).1 ∈ Long) :
    ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      let q := codedSixSwitchEndpoint T
        (fun z => (affineIncidencePoint a h base velocity height speed z).1) v
        (sixSwitchCoordinates control a h x)
      let p₀ := affineIncidencePoint a h base velocity height speed (x 0)
      let p₆ := affineIncidencePoint a h base velocity height speed (x 6)
      ‖q.1+p₀.1-p₆.1‖ ≤ 6*(η+τ) ∧
      |q.2+p₀.2-p₆.2| ≤ 6*(ζ+ε+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ))) ∧
      ‖q+p₀-p₆‖ ≤ max (6*(η+τ))
        (6*(ζ+ε+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ)))) := by
  classical
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : ∀ n : ℕ, S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ :=
    fun _ => stateTimeSwitch_invariant ν κ state hstate
  let point := affineIncidencePoint a h base velocity height speed
  have hp : Measurable point := affineIncidencePoint_measurable a h base velocity height speed hb hu hz hw
  let Rel : (L × ℝ) → L → Prop := fun old l => (old.2-a)/h ∈ Icc (0:ℝ) 1 → l ∈ Long →
    ‖(affineLinePoint base velocity height speed l ((old.2-a)/h)).1-(point old).1‖ ≤ η ∧
      |(affineLinePoint base velocity height speed l ((old.2-a)/h)).2-(point old).2| ≤ ζ
  have hRel : MeasurableSet {z : (L × ℝ) × L | Rel z.1 z.2} := by
    have hn : Measurable (fun z : (L × ℝ) × L =>
        affineLinePoint base velocity height speed z.2 ((z.1.2-a)/h)) := by
      unfold affineLinePoint
      fun_prop
    have ho : Measurable (fun z : (L × ℝ) × L => point z.1) := hp.comp measurable_fst
    have hraw := (measurableSet_le (continuous_norm.measurable.comp (hn.fst.sub ho.fst))
      (measurable_const (a := η))).inter
        (measurableSet_le (continuous_abs.measurable.comp (hn.snd.sub ho.snd))
          (measurable_const (a := ζ)))
    have hvalid : MeasurableSet {z : (L × ℝ) × L | (z.1.2-a)/h ∈ Icc (0:ℝ) 1} :=
      measurableSet_Icc.preimage (by fun_prop)
    have hmeas := hvalid.compl.union
      ((hLong.preimage (measurable_snd : Measurable (Prod.snd : (L × ℝ) × L → L))).compl.union hraw)
    convert hmeas using 1
    ext z
    simp only [Rel,Set.mem_setOf_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_preimage]
    tauto
  have hrel := actualSwitchedPathMeasure_weighted_ae_line_relations_of_original_support
    ν κ state hstate w Rel hRel Valid hValid hshared
  have ht₀ : ∀ᵐ z ∂ν ⊗ₘ κ, (z.2-a)/h ∈ Icc (0:ℝ) 1 := by
    filter_upwards [ht] with z hz
    exact normalized_time_mem_unit_interval hh hz
  have htimes := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => (z.2-a)/h ∈ Icc (0:ℝ) 1) (fun _ => ht₀)
  have hvels := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => ‖velocity z.1-(fun j : Fin 3 => v (control z.1) j)‖ ≤ τ) (fun _ => hvelocity)
  have hcods := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => ∀ j, |v (control z.1) j| ≤ U) (fun _ => hcodes)
  have hfits := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, |speed z.1-∑ j, velocity z.1 j *
      MvPolynomial.eval (base z.1+t • velocity z.1) (T j)| ≤ ε) (fun _ => hfit)
  have hconfs := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, ‖base z.1+t • velocity z.1‖ ≤ R) (fun _ => hconf)
  filter_upwards [htimes,hvels,hcods,hfits,hconfs,hrel,hretainedLong] with x htx hvx hcx hfx hbx hrx hlx
  let coded := fun l => fun j : Fin 3 => v (control l) j
  let F := fun u : Fin 3 → ℝ => fun y : Fin 3 → ℝ => ∑ j, u j*MvPolynomial.eval y (T j)
  have hF (l : L) : Continuous (F (coded l)) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (MvPolynomial.continuous_eval (T j))
  have hsim := assigned_affine_line_path_simulation 6 (fun k => (x k).1)
    (fun k => ((x k).2-a)/h) base velocity coded height speed F hF
    ε η τ ζ (3*B) (3*U*A) R hε hη hτ (by positivity) (by positivity)
    (fun k _ => htx k) (fun k hk => (hrx k (htx k) (hlx k hk)).1) (fun k hk => (hrx k (htx k) (hlx k hk)).2)
    (fun k _ => hvx (k+1)) (fun k hk => hfx (k+1) (hlx k hk)) (fun k hk => hbx (k+1) (hlx k hk))
    (fun k hk y hy => by
      have hy' : y ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hy
      simpa only [F,Fintype.card_fin,Nat.cast_ofNat] using
        finite_field_velocity_difference_le (velocity (x (k+1)).1) (coded (x (k+1)).1)
          (fun j => MvPolynomial.eval y (T j)) B (hfield y hy'))
    (fun k hk y hy z hz => by
      have hy' : y ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hy
      have hz' : z ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hz
      simpa only [F,Fintype.card_fin,Nat.cast_ofNat] using
        finite_field_spatial_difference_le (fun j y => MvPolynomial.eval y (T j))
          (coded (x (k+1)).1) y z U A hU (hcx (k+1)) (hspace y hy' z hz'))
  rw [codedSixSwitchEndpoint_on_path]
  simpa only [affineIncidencePoint,coded,F,Nat.cast_ofNat,sub_add_cancel] using hsim

/-- The native physical point has an affine base and a quadratic hidden coordinate. -/
noncomputable def quadraticIncidencePoint {L : Type*}
    (a h : ℝ) (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
    (z : L × ℝ) : (Fin 3 → ℝ) × ℝ :=
  quadraticLinePoint base velocity height₀ height₁ height₂ z.1 ((z.2-a)/h)

theorem quadraticIncidencePoint_measurable {L : Type*} [MeasurableSpace L]
    (a h : ℝ) (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
    (hb : Measurable base) (hu : Measurable velocity)
    (hz₀ : Measurable height₀) (hz₁ : Measurable height₁) (hz₂ : Measurable height₂) :
    Measurable (quadraticIncidencePoint a h base velocity height₀ height₁ height₂) := by
  unfold quadraticIncidencePoint quadraticLinePoint quadraticHeight
  fun_prop

/-- Original whole-block fits and the geometric shared-state certificate
supply the actual six-switch polynomial simulation almost everywhere.
All original fits and bounds are transferred through the same stationary
path law before any weighting or successful-path restriction. -/
theorem actual_quadratic_six_switch_endpoint_error_ae {L Q C : Type*}
    [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace Q] [StandardBorelSpace Q] [MeasurableSpace C]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → C) (v : C → EuclideanSpace ℝ (Fin 3))
    (a h : ℝ) (hh : 0 < h) (Long : Set L) (hLong : MeasurableSet Long)
    (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
    (hb : Measurable base) (hu : Measurable velocity)
    (hz₀ : Measurable height₀) (hz₁ : Measurable height₁) (hz₂ : Measurable height₂)
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (ε η τ ζ B U A R : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a+h))
    (hvelocity : ∀ᵐ z ∂ν ⊗ₘ κ,
      ‖velocity z.1-(fun j : Fin 3 => v (control z.1) j)‖ ≤ τ)
    (hcodes : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
    (hfit : ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1,
      |quadraticHeightSpeed (height₁ z.1) (height₂ z.1) t-∑ j, velocity z.1 j * MvPolynomial.eval
        (base z.1+t • velocity z.1) (T j)| ≤ ε)
    (hconf : ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, ‖base z.1+t • velocity z.1‖ ≤ R)
    (hfield : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j, |MvPolynomial.eval x (T j)| ≤ B)
    (hspace : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)),
      ∀ y ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j,
        |MvPolynomial.eval x (T j)-MvPolynomial.eval y (T j)| ≤ A*‖x-y‖)
    (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂ν ⊗ₘ κ, Valid z)
    (hshared : ∀ old redraw, state redraw = state old → Valid old → Valid redraw →
      (old.2-a)/h ∈ Icc (0:ℝ) 1 → redraw.1 ∈ Long →
      ‖(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2-a)/h)).1-
        (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).1‖ ≤ η ∧
      |(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2-a)/h)).2-
        (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).2| ≤ ζ)
    (w : (ℕ → L × ℝ) → ENNReal)
    (hretainedLong : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      ∀ k < 6, (x (k+1)).1 ∈ Long) :
    ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      let q := codedSixSwitchEndpoint T
        (fun z => (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1) v
        (sixSwitchCoordinates control a h x)
      let p₀ := quadraticIncidencePoint a h base velocity height₀ height₁ height₂ (x 0)
      let p₆ := quadraticIncidencePoint a h base velocity height₀ height₁ height₂ (x 6)
      ‖q.1+p₀.1-p₆.1‖ ≤ 6*(η+τ) ∧
      |q.2+p₀.2-p₆.2| ≤ 6*(ζ+ε+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ))) ∧
      ‖q+p₀-p₆‖ ≤ max (6*(η+τ))
        (6*(ζ+ε+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ)))) := by
  classical
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : ∀ n : ℕ, S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ :=
    fun _ => stateTimeSwitch_invariant ν κ state hstate
  let point := quadraticIncidencePoint a h base velocity height₀ height₁ height₂
  have hp : Measurable point := quadraticIncidencePoint_measurable a h base velocity height₀ height₁ height₂ hb hu hz₀ hz₁ hz₂
  let Rel : (L × ℝ) → L → Prop := fun old l => (old.2-a)/h ∈ Icc (0:ℝ) 1 → l ∈ Long →
    ‖(quadraticLinePoint base velocity height₀ height₁ height₂ l ((old.2-a)/h)).1-(point old).1‖ ≤ η ∧
      |(quadraticLinePoint base velocity height₀ height₁ height₂ l ((old.2-a)/h)).2-(point old).2| ≤ ζ
  have hRel : MeasurableSet {z : (L × ℝ) × L | Rel z.1 z.2} := by
    have hn : Measurable (fun z : (L × ℝ) × L =>
        quadraticLinePoint base velocity height₀ height₁ height₂ z.2 ((z.1.2-a)/h)) := by
      unfold quadraticLinePoint quadraticHeight
      fun_prop
    have ho : Measurable (fun z : (L × ℝ) × L => point z.1) := hp.comp measurable_fst
    have hraw := (measurableSet_le (continuous_norm.measurable.comp (hn.fst.sub ho.fst))
      (measurable_const (a := η))).inter
        (measurableSet_le (continuous_abs.measurable.comp (hn.snd.sub ho.snd))
          (measurable_const (a := ζ)))
    have hvalid : MeasurableSet {z : (L × ℝ) × L | (z.1.2-a)/h ∈ Icc (0:ℝ) 1} :=
      measurableSet_Icc.preimage (by fun_prop)
    have hmeas := hvalid.compl.union
      ((hLong.preimage (measurable_snd : Measurable (Prod.snd : (L × ℝ) × L → L))).compl.union hraw)
    convert hmeas using 1
    ext z
    simp only [Rel,Set.mem_setOf_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_preimage]
    tauto
  have hrel := actualSwitchedPathMeasure_weighted_ae_line_relations_of_original_support
    ν κ state hstate w Rel hRel Valid hValid hshared
  have ht₀ : ∀ᵐ z ∂ν ⊗ₘ κ, (z.2-a)/h ∈ Icc (0:ℝ) 1 := by
    filter_upwards [ht] with z hz
    exact normalized_time_mem_unit_interval hh hz
  have htimes := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => (z.2-a)/h ∈ Icc (0:ℝ) 1) (fun _ => ht₀)
  have hvels := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => ‖velocity z.1-(fun j : Fin 3 => v (control z.1) j)‖ ≤ τ) (fun _ => hvelocity)
  have hcods := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => ∀ j, |v (control z.1) j| ≤ U) (fun _ => hcodes)
  have hfits := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, |quadraticHeightSpeed (height₁ z.1) (height₂ z.1) t-∑ j, velocity z.1 j *
      MvPolynomial.eval (base z.1+t • velocity z.1) (T j)| ≤ ε) (fun _ => hfit)
  have hconfs := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ) (fun _ => S) hs w
    (fun _ z => z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, ‖base z.1+t • velocity z.1‖ ≤ R) (fun _ => hconf)
  filter_upwards [htimes,hvels,hcods,hfits,hconfs,hrel,hretainedLong] with x htx hvx hcx hfx hbx hrx hlx
  let coded := fun l => fun j : Fin 3 => v (control l) j
  let F := fun u : Fin 3 → ℝ => fun y : Fin 3 → ℝ => ∑ j, u j*MvPolynomial.eval y (T j)
  have hF (l : L) : Continuous (F (coded l)) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (MvPolynomial.continuous_eval (T j))
  have hsim := assigned_quadratic_line_path_simulation 6 (fun k => (x k).1)
    (fun k => ((x k).2-a)/h) base velocity coded height₀ height₁ height₂ F hF
    ε η τ ζ (3*B) (3*U*A) R hε hη hτ (by positivity) (by positivity)
    (fun k _ => htx k) (fun k hk => (hrx k (htx k) (hlx k hk)).1) (fun k hk => (hrx k (htx k) (hlx k hk)).2)
    (fun k _ => hvx (k+1)) (fun k hk => hfx (k+1) (hlx k hk)) (fun k hk => hbx (k+1) (hlx k hk))
    (fun k hk y hy => by
      have hy' : y ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hy
      simpa only [F,Fintype.card_fin,Nat.cast_ofNat] using
        finite_field_velocity_difference_le (velocity (x (k+1)).1) (coded (x (k+1)).1)
          (fun j => MvPolynomial.eval y (T j)) B (hfield y hy'))
    (fun k hk y hy z hz => by
      have hy' : y ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hy
      have hz' : z ∈ Metric.closedBall 0 (R+7*(η+τ)) := by
        simpa only [Nat.cast_ofNat,show (6:ℝ)+1=7 by norm_num] using hz
      simpa only [F,Fintype.card_fin,Nat.cast_ofNat] using
        finite_field_spatial_difference_le (fun j y => MvPolynomial.eval y (T j))
          (coded (x (k+1)).1) y z U A hU (hcx (k+1)) (hspace y hy' z hz'))
  rw [codedSixSwitchEndpoint_on_path]
  simpa only [quadraticIncidencePoint,coded,F,Nat.cast_ofNat,sub_add_cancel] using hsim


end Submission.Lib.K4PolynomialNorming
