import Submission.Obl.k4_finite_positive_prepared_models.Cut
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Exists

/-!
# `SyntheticModels`

The data-free prepared stage models of `Synthetic.exists_stageGood` supply the interface
`SyntheticModels` of `Cut`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

/-- **`SyntheticModels`.** -/
theorem syntheticModels : SyntheticModels :=
  fun d₁ κ₁ ℓ S hd₁ hd₁' hκ hκ' hℓ _ hS n _ =>
    exists_stageGood d₁ κ₁ ℓ S n hd₁ hd₁' hκ hκ' hℓ hS

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
