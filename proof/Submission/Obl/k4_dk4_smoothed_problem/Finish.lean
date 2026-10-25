import Submission.Obl.k4_dk4_smoothed_problem.LargeBadScales
import Submission.Obl.k4_dk4_smoothed_problem.Output
import Submission.Obl.k4_dk4_smoothed_problem.Spread.Eventual
import Submission.Obl.k4_dk4_smoothed_problem.NativeSpreadTransport

open MeasureTheory Set Filter

namespace Submission.Obl.k4_dk4_smoothed_problem

open Framework

theorem smoothed_problem_of_not_DK4 (hMULT : Spread.MultiplicityBound)
    (hnot : ¬ Submission.Lib.KakeyaCovering.DiscreteKakeyaEstimate) : SmoothedOutput := by
  classical
  obtain ⟨σ, c, R, hσ, hσ1, hc, hR, κ, hκ, hlarge, hbad⟩ :=
    exists_large_bad_sequence hnot
  let A : (j : ℕ) → BadConfiguration c R σ (κ j) := fun j => Classical.choice (hbad j)
  have ht : Tendsto κ atTop atTop := tendsto_atTop_mono (fun j => (hκ j).2) tendsto_id
  have hpair := Spread.smoothedPrior_spread_eventually hMULT hc hR κ ht
    (fun j => (A j).n) (fun j => (A j).x) (fun j => (A j).v)
    (fun j => configurationIntercept (A j)) (fun j => configurationSlope (A j))
    (fun j i => ⟨rfl, rfl⟩) (fun j i => ⟨rfl, rfl⟩)
    (fun j => (A j).count_lower) (fun j => (A j).coordinates)
    (fun j => (A j).separated) (fun j => (A j).bounded)
  apply output_of_bad_sequence hσ hc hR κ hκ hlarge A
  intro α hα
  obtain ⟨θ, hθ, hspread⟩ := hpair α hα
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [hspread] with j hj
  intro U hU
  rw [configurationPrior,
    nativePrior_base_mass_eq (A j).n_pos (smoothingRadius_pos (κ j))]
  exact hj U hU

end Submission.Obl.k4_dk4_smoothed_problem
