/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.SixSwitchCoordinates
import Submission.Lib.K4PolynomialNorming.SwitchedIntegralContinuity
import Submission.Lib.K4PolynomialNorming.FullEndpointCoordinates
import Submission.Lib.K4PolynomialNorming.PublishedSwitchedPath
import Submission.Lib.K4CubicTests.SwitchedSkew

open Set MeasureTheory MvPolynomial
open scoped Matrix Interval

namespace Submission.Lib.K4PolynomialNorming

/-- Joint continuity concerns the actual published endpoint polynomial,
including its dependence on the original start and both direction bases. -/
theorem continuous_published_switched_height_data {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) :
    Continuous (fun z : ((σ → ℝ) × (κ → σ → ℝ)) × (κ → ℝ) =>
      MvPolynomial.eval z.2
        (Submission.Lib.K4CubicTests.switchedEndpointHeight T z.1.1 z.1.2)) := by
  have he : (fun z : ((σ → ℝ) × (κ → σ → ℝ)) × (κ → ℝ) =>
      MvPolynomial.eval z.2
        (Submission.Lib.K4CubicTests.switchedEndpointHeight T z.1.1 z.1.2)) =
      (fun z => ∑ k : κ, ∫ s in (0:ℝ)..z.2 k, ∑ a, z.1.2 k a * MvPolynomial.eval
        (fun b => z.1.1 b + ∑ l : κ,
          if l ≤ k then z.1.2 l b * Function.update z.2 k s l else 0) (T a)) := by
    funext z
    exact Submission.Lib.K4CubicTests.eval_switchedEndpointHeight_eq_integral T z.1.1 z.1.2 z.2
  rw [he]
  exact continuous_switched_integral_data T

/-- The constructed physical displacement and polynomial height in the
explicit observed start/control/signed-duration coordinates. -/
noncomputable def codedSixSwitchEndpoint {L C : Type*} [MeasurableSpace C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (v : C → EuclideanSpace ℝ (Fin 3))
    (z : ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)) : (Fin 3 → ℝ) × ℝ :=
  let δ := (splitHeadCoordinates 5).symm z.2
  let dirs := fun i : Fin 6 => fun a : Fin 3 => v (z.1.2 i) a
  ((fun a => ∑ i : Fin 6, δ i * dirs i a),
    MvPolynomial.eval δ
      (Submission.Lib.K4CubicTests.switchedEndpointHeight T (base z.1.1) dirs))

theorem codedSixSwitchEndpoint_measurable {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (hbase : Measurable base) (v : C → EuclideanSpace ℝ (Fin 3)) :
    Measurable (codedSixSwitchEndpoint T base v) := by
  let Z := ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)
  have hc : Measurable (fun z : Z => z.1.2) := by fun_prop
  have hw : Measurable (fun z : Z => fun i : Fin 6 => fun a : Fin 3 => v (z.1.2 i) a) :=
    (measurable_of_countable (fun c : Fin 6 → C =>
      fun i : Fin 6 => fun a : Fin 3 => v (c i) a)).comp hc
  have hδ : Measurable (fun z : Z => (splitHeadCoordinates 5).symm z.2) :=
    (splitHeadCoordinates 5).symm.measurable.comp measurable_snd
  have hp := ((hbase.comp (by fun_prop : Measurable (fun z : Z => z.1.1))).prodMk hw).prodMk hδ
  have hh := (continuous_published_switched_height_data (κ := Fin 6) T).measurable.comp hp
  have hl : Continuous (fun y : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ) =>
      fun a => ∑ i : Fin 6, y.2 i * y.1 i a) := by fun_prop
  exact (hl.measurable.comp (hw.prodMk hδ)).prodMk hh

theorem codedSixSwitchEndpoint_target_measurable {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (hbase : Measurable base) (v : C → EuclideanSpace ℝ (Fin 3))
    (start : (L × ℝ) × (Fin 6 → C) → (Fin 3 → ℝ) × ℝ) (hstart : Measurable start)
    (U : Set ((Fin 3 → ℝ) × ℝ)) (hU : MeasurableSet U) :
    MeasurableSet {z | codedSixSwitchEndpoint T base v z + start z.1 ∈ U} :=
  hU.preimage ((codedSixSwitchEndpoint_measurable T base hbase v).add
    (hstart.comp measurable_fst))

/-- The constructed height is the exact two-basis height consumed by the
endpoint-volume theorem, with the two actual observed direction blocks. -/
theorem codedSixSwitchEndpoint_height {L C : Type*} [MeasurableSpace C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (v : C → EuclideanSpace ℝ (Fin 3))
    (z : ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)) :
    (codedSixSwitchEndpoint T base v z).2 =
      MvPolynomial.eval ((splitHeadCoordinates 5).symm z.2)
        (Submission.Lib.K4CubicTests.twoBasisEndpointHeight T (base z.1.1)
          (directionBlockMatrix v z.1.2 0) (directionBlockMatrix v z.1.2 1)) := by
  unfold codedSixSwitchEndpoint Submission.Lib.K4CubicTests.twoBasisEndpointHeight
  rw [directionBlockMatrix_append]

/-- Its base displacement is the physical part of the constructed full
linear endpoint coordinates; the inverse is used only to define that map. -/
theorem codedSixSwitchEndpoint_base {L C : Type*} [MeasurableSpace C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (v : C → EuclideanSpace ℝ (Fin 3))
    (z : ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ))
    (Ai : Matrix (Fin 3) (Fin 3) ℝ) (hA : directionBlockMatrix v z.1.2 0 * Ai = 1) :
    (fun a => fullLinearEndpointCoordinates (directionBlockMatrix v z.1.2 0) Ai
      (directionBlockMatrix v z.1.2 1) hA ((splitHeadCoordinates 5).symm z.2)
        (Fin.castAdd 3 a)) = (codedSixSwitchEndpoint T base v z).1 := by
  rw [fullLinearEndpointCoordinates_apply]
  simp only [Fin.append_left]
  exact directionBlockMatrix_displacement v z.1.2 ((splitHeadCoordinates 5).symm z.2)

/-- On an actual path this polynomial endpoint is exactly the ideal
base displacement and the sum of its signed field integrals. -/
theorem codedSixSwitchEndpoint_on_path {L C : Type*} [MeasurableSpace C]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : L × ℝ → Fin 3 → ℝ)
    (v : C → EuclideanSpace ℝ (Fin 3)) (control : L → C) (a h : ℝ)
    (x : ℕ → L × ℝ) :
    let δ := fun k => (((x (k+1)).2-a)/h)-(((x k).2-a)/h)
    let V := fun k => fun j : Fin 3 => v (control (x (k+1)).1) j
    codedSixSwitchEndpoint T base v (sixSwitchCoordinates control a h x) =
      (pathBasePrefix (base (x 0)) δ V 6-base (x 0),
        ∑ k ∈ Finset.range 6, ∫ s in (0:ℝ)..δ k,
          ∑ j, V k j * MvPolynomial.eval
            (pathBasePrefix (base (x 0)) δ V k+s • V k) (T j)) := by
  let δ := fun k => (((x (k+1)).2-a)/h)-(((x k).2-a)/h)
  let V := fun k => fun j : Fin 3 => v (control (x (k+1)).1) j
  have hd : (splitHeadCoordinates 5).symm (sixSwitchCoordinates control a h x).2 =
      fun i : Fin 6 => δ i := by
    funext i
    exact sixSwitchCoordinates_durations_apply control a h x i
  apply Prod.ext
  · dsimp only [codedSixSwitchEndpoint]
    rw [hd]
    change (fun j => ∑ i : Fin 6, δ i * V i j) =
      (base (x 0)+(∑ k ∈ Finset.range 6, δ k • V k))-base (x 0)
    rw [Finset.sum_range (n := 6) (fun k => δ k • V k)]
    funext j
    simp only [Pi.sub_apply,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    ring
  · dsimp only [codedSixSwitchEndpoint]
    rw [hd]
    change MvPolynomial.eval (fun i : Fin 6 => δ i)
      (Submission.Lib.K4CubicTests.switchedEndpointHeight T (base (x 0)) (fun i : Fin 6 => V i)) = _
    exact published_switched_height_eq_nat_integral 6 T (base (x 0)) V δ

end Submission.Lib.K4PolynomialNorming
