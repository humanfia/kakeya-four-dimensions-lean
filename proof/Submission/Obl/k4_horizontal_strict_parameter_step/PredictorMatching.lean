/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PredictorMatching.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface
import Submission.Obl.k4_horizontal_strict_parameter_step.AffineUpgrade
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingApply
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetJets
import Submission.Obl.k4_seven_direction_local_degree_restoration.Quadratic

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- The given univariate matching input already supplies the accepted
three-dimensional algebraic graph-matching estimate. -/
theorem algebraic_matching_of_input (hM : MatchingInput) : Matching :=
  Submission.k4_local_algebraic_graph_matching hM

theorem unnormalized_matching_of_input (hM : MatchingInput) {d : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ MatchBound d ε₀ R₀ :=
  matching_unnormalized (algebraic_matching_of_input hM) d hd hd1

/-- The complex polynomial graph of a full-time parameter predictor. -/
def predictorSheet (h : Fin 6 → ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  h 0 + (h 1 : ℂ) * z 0 + ((h 2 : ℂ) + (h 3 : ℂ) * z 0) * z 1 +
    ((h 4 : ℂ) + (h 5 : ℂ) * z 0) * z 2

def predictorGraph (h : Fin 6 → ℝ) : MvPolynomial (Fin 4) ℂ :=
  (Submission.Obl.k4_seven_direction_local_degree_restoration.quadraticGraph
    (h 0) ![h 1, h 2, h 4] ![![0, h 3, h 5], ![0, 0, 0], ![0, 0, 0]]).map
      (algebraMap ℝ ℂ)

theorem predictorSheet_real (h : Fin 6 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    predictorSheet h (emb x) = (predictor h (x 0) (x 1) (x 2) : ℂ) := by
  simp [predictorSheet, predictor, emb]

theorem predictorSheet_isMatchSheet (h : Fin 6 → ℝ) : IsMatchSheet (predictorSheet h) := by
  let G := Submission.Obl.k4_seven_direction_local_degree_restoration.quadraticGraph
    (h 0) ![h 1, h 2, h 4] ![![0, h 3, h 5], ![0, 0, 0], ![0, 0, 0]]
  have hG : G ≠ 0 := by
    intro heq
    have hp := Submission.Obl.k4_seven_direction_local_degree_restoration.quadraticGraph_pderiv
      (h 0) ![h 1, h 2, h 4] ![![0, h 3, h 5], ![0, 0, 0], ![0, 0, 0]]
    change MvPolynomial.pderiv (3 : Fin 4) G = 1 at hp
    rw [heq] at hp
    simpa using hp
  have hm : predictorGraph h ≠ 0 := by
    intro heq
    have hinj : Function.Injective (MvPolynomial.map (σ := Fin 4) (algebraMap ℝ ℂ)) :=
      MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℝ ℂ)
    apply hG
    apply hinj
    exact heq.trans (map_zero _).symm
  refine ⟨⟨predictorGraph h, hm, ?_, ?_⟩, ?_, ?_⟩
  · exact (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      (Submission.Obl.k4_seven_direction_local_degree_restoration.quadraticGraph_totalDegree
        (h 0) ![h 1, h 2, h 4] ![![0, h 3, h 5], ![0, 0, 0], ![0, 0, 0]])
  · intro z _
    have hz : Fin.snoc (fun i : Fin 3 => z i) (predictorSheet h z) =
        ![z 0, z 1, z 2, predictorSheet h z] := by
      ext i
      fin_cases i <;> rfl
    rw [hz]
    simp [predictorGraph,
      Submission.Obl.k4_seven_direction_local_degree_restoration.quadraticGraph,
      Fin.sum_univ_succ, predictorSheet]
    <;> ring
  · unfold predictorSheet
    fun_prop
  · intro x _
    rw [predictorSheet_real]
    exact Complex.ofReal_im _

/-- Changing the time and static parameter coordinates preserves the six-coefficient
predictor form, so it remains a degree-two algebraic matching sheet. -/
def predictorRechart (h : Fin 6 → ℝ) (t₀ H p₀ q₀ D : ℝ) : Fin 6 → ℝ :=
  ![predictor h t₀ p₀ q₀, H * (h 1 + h 3 * p₀ + h 5 * q₀),
    D * (h 2 + h 3 * t₀), D * H * h 3,
    D * (h 4 + h 5 * t₀), D * H * h 5]

theorem predictor_rechart (h : Fin 6 → ℝ) (t₀ H p₀ q₀ D t p q : ℝ) :
    predictor (predictorRechart h t₀ H p₀ q₀ D) t p q =
      predictor h (t₀ + H * t) (p₀ + D * p) (q₀ + D * q) := by
  simp [predictorRechart, predictor]
  ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
