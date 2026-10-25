/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.SixSwitchCoordinates

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- A joint measurable event containing the geometric data used by the
endpoint estimate. Its sections do not require a measurable path image. -/
def sixSwitchCertificates {L C : Type*} [MeasurableSpace C]
    (Good : Set (L × ℝ)) (v : C → EuclideanSpace ℝ (Fin 3)) (d U : ℝ) :
    Set (((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)) :=
  {z | z.1.1 ∈ Good ∧
    (∀ b : Fin 2, d ≤ |(directionBlockMatrix v z.1.2 b).det|) ∧
    (∀ (b : Fin 2) j i, |directionBlockMatrix v z.1.2 b j i| ≤ U) ∧
    ∀ i, |(splitHeadCoordinates 5).symm z.2 i| ≤ 1}

theorem sixSwitchCertificates_measurable {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (Good : Set (L × ℝ)) (hGood : MeasurableSet Good)
    (v : C → EuclideanSpace ℝ (Fin 3)) (d U : ℝ) :
    MeasurableSet (sixSwitchCertificates Good v d U) := by
  let Z := ((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)
  have hcodes : Measurable (fun z : Z => z.1.2) := by fun_prop
  have hdet (b : Fin 2) : Measurable (fun z : Z =>
      |(directionBlockMatrix v z.1.2 b).det|) :=
    (measurable_of_countable (fun c : Fin 6 → C =>
      |(directionBlockMatrix v c b).det|)).comp hcodes
  have hentry (b : Fin 2) (j i : Fin 3) : Measurable (fun z : Z =>
      |directionBlockMatrix v z.1.2 b j i|) :=
    (measurable_of_countable (fun c : Fin 6 → C =>
      |directionBlockMatrix v c b j i|)).comp hcodes
  have hduration (i : Fin 6) : Measurable (fun z : Z =>
      |(splitHeadCoordinates 5).symm z.2 i|) :=
    continuous_abs.measurable.comp ((measurable_pi_apply i).comp
      ((splitHeadCoordinates 5).symm.measurable.comp measurable_snd))
  unfold sixSwitchCertificates
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (hGood.preimage (by fun_prop)).inter
    ((MeasurableSet.iInter (fun b => measurableSet_le measurable_const (hdet b))).inter
      ((MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun j =>
        MeasurableSet.iInter (fun i => measurableSet_le (hentry b j i) measurable_const)))).inter
        (MeasurableSet.iInter (fun i => measurableSet_le (hduration i) measurable_const))))

end Submission.Lib.K4PolynomialNorming
