-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/EntropyWindow.lean.
import Mathlib
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-!
# The information window of paper Prop. 4.7

`entropy_window`: among `n` successive windows of nested histories, one has conditional
information increment at most `H(V | H 0) / n` (finite conditional entropies of the accepted
o081 module).
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- **Entropy window** (paper Prop. 4.7, the information window). For histories `H 0, …, H n`
and a discrete variable `V`, one of the `n` successive windows has conditional information
increment `H(V | H i) - H(V | H (i+1))` at most `H(V | H 0) / n`; here
`H(V | G) = -negCondEnt P V G`. -/
theorem entropy_window {Ω α β : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β]
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (V : Ω → α) (H : ℕ → Ω → β) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, negCondEnt P V (H (i + 1)) - negCondEnt P V (H i) ≤
      -negCondEnt P V (H 0) / n := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ i ∈ Finset.range n, (negCondEnt P V (H (i + 1)) - negCondEnt P V (H i)) =
      negCondEnt P V (H n) - negCondEnt P V (H 0) :=
    Finset.sum_range_sub (fun i => negCondEnt P V (H i)) n
  have hlt : ∑ _i ∈ Finset.range n, (-negCondEnt P V (H 0) / n) <
      ∑ i ∈ Finset.range n, (negCondEnt P V (H (i + 1)) - negCondEnt P V (H i)) :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne')
      fun i hi => hcon i (Finset.mem_range.mp hi)
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_div_cancel₀ _ hn'.ne'] at hlt
  have := negCondEnt_nonpos hP V (H n)
  linarith

end Submission.Obl.k4_finite_affine_parent_sources
