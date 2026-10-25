-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DenseSlopeProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DenseSlopes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.SlopeProjection

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- A sufficiently dense family of slopes contains one giving a nearly
one-dimensional projection of a Cartesian product. -/
theorem dense_slope_projection_count (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C D σ τ : ℝ,
      0 < δ → δ ≤ δ₀ → 1 ≤ C → 1 ≤ D → 1 ≤ σ + τ →
      ∀ (A B : Finset ℝ), A.Nonempty → B.Nonempty →
        RealFiniteFrostman δ C σ A → RealFiniteFrostman δ D τ B →
        ∀ T : Set ℝ,
          (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ δ) →
          ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ (m : ℕ) (cc : Fin m → ℝ),
            Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) ''
              (↑(A ×ˢ B) : Set (ℝ × ℝ))) cc →
            δ ^ (ε - 1) ≤ (max (C * D) 40) ^ 2 * (m : ℝ) := by
  obtain ⟨δ₀, hδ₀, hcount⟩ := slope_projection_count ε hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ C D σ τ hδ hsmall hC hD hs A B hA hB hAF hBF T hdense
  obtain ⟨N, t, hN, ht, hf⟩ := exists_frostman_slopes_of_dense hδ T hdense
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi⟩ := hcount δ C D 5 σ τ hδ hsmall hC hD (by norm_num) hs
    A B hA hB hAF hBF (Fin N) t hf
    (fun i => by rw [abs_of_nonneg (ht i).2.1]; exact (ht i).2.2)
  refine ⟨t i, (ht i).1, (ht i).2, ?_⟩
  simpa only [show (8 : ℝ) * 5 = 40 by norm_num] using hi

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
