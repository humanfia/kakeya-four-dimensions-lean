import Submission.Obl.k4_raw_earlier_witness_normalization.Assembly
import Submission.Obl.k4_raw_earlier_witness_normalization.Poly

namespace Submission.Obl.k4_raw_earlier_witness_normalization

/-- Inverse affine substitution supplies the polynomial part of normalization. -/
theorem polynomial_normalization : PolynomialNormalization normPoly := by
  intro t₀ q B c u D
  refine ⟨totalDegree_normPoly_le t₀ q B c u D, ?_⟩
  intro hq hB hD
  refine ⟨?_, ?_⟩
  · intro P p
    exact eval_normPoly t₀ q B c u D hq.ne' hB.ne' hD
      (earlierCoordinates t₀ q B c u D) (fun _ => rfl) P p
  · intro K δ P S p h
    exact normalized_tests t₀ q B c u D hq.ne' hB hD
      (earlierCoordinates t₀ q B c u D) (fun _ => rfl) P S K δ _ p h

end Submission.Obl.k4_raw_earlier_witness_normalization
