-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.CartesianProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.IndexedKaufmanCount

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- A Cartesian product with total Frostman exponent at least one has a
large projection in every one-dimensional Frostman family of directions. -/
theorem cartesian_projection_count (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C D E σ τ : ℝ,
      0 < δ → δ ≤ δ₀ → 1 ≤ C → 1 ≤ D → 1 ≤ E → 1 ≤ σ + τ →
      ∀ (A B : Finset ℝ), A.Nonempty → B.Nonempty →
        RealFiniteFrostman δ C σ A → RealFiniteFrostman δ D τ B →
        ∀ (I : Type) [Fintype I] [Nonempty I] (f : I → Plane),
          IndexedFrostman δ E f → (∀ i, ‖f i‖ = 1) →
          ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
            Covers δ ((fun p : ℝ × ℝ => f i 0 * p.1 + f i 1 * p.2) ''
              (↑(A ×ˢ B) : Set (ℝ × ℝ))) cc →
            δ ^ (ε - 1) ≤ (max (C * D) E) ^ 2 * (m : ℝ) := by
  classical
  obtain ⟨δ₀, hδ₀, hcount⟩ := indexed_kaufman_projection_count ε hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ C D E σ τ hδ hsmall hC hD hE hs A B hA hB hAF hBF I _ _ f hf hunit
  let F := (A ×ˢ B).image cartesianPoint
  have hFp : F.Nonempty := (hA.product hB).image _
  have hFr : ClosedFiniteFrostman δ (max (C * D) E) F :=
    (cartesian_frostman hδ hC hD hs hAF hBF).mono_constant hδ.le (le_max_left _ _)
  have hf' := IndexedFrostman.mono_constant hf hδ.le (le_max_right (C * D) E)
  obtain ⟨i, hi⟩ := hcount δ (max (C * D) E) 1 hδ hsmall (hE.trans (le_max_right _ _))
    zero_lt_one I f F (fun _ => F) hFr hf' hunit (fun _ => Finset.Subset.refl _)
    ⟨Classical.arbitrary I, hFp⟩ (by simp)
  refine ⟨i, ?_⟩
  intro m cc hcov
  have hcov' : Covers δ ((fun x => inner ℝ (f i) x) '' (↑F : Set Plane)) cc := by
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply hcov
    refine ⟨p, hp, ?_⟩
    simp [plane_inner, cartesianPoint]
  simpa only [one_pow, one_mul] using hi m cc hcov'

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
