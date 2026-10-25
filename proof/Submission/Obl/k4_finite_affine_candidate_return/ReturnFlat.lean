-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ReturnFlat.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.FlatCut
import Submission.Obl.k4_finite_affine_candidate_return.UniformReturn

namespace Submission.Obl.k4_finite_affine_candidate_return

/-- The uniform return proof in the literal field-by-field interface
used to freeze a return obligation. -/
theorem flat_source_return_of_sourceReturn (h : SourceReturn) : FlatSourceReturn := by
  intro n M
  obtain ⟨Mc, h⟩ := h n M
  refine ⟨Mc, ?_⟩
  intro d₁ κ₁ ℓ ρ gain ε unit Nk L W ω ν E B f m s δ₀ Mp Dp σ
    r T nw κ C lev par γ j c u Q R A F lst H
    sN sK sν sμ sρ sπ sb sP sT sn sj sA sB sc sF hp hH hs
  exact h d₁ κ₁ ℓ ρ gain ε unit Nk L W ω ν E B f m s δ₀ Mp Dp σ
    ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst⟩ H
    ⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF⟩ hp hH hs

theorem flat_uniform_source_return : FlatSourceReturn :=
  flat_source_return_of_sourceReturn uniform_source_return

end Submission.Obl.k4_finite_affine_candidate_return
