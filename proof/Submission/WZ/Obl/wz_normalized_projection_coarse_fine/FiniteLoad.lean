-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.FiniteLoad.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_finite_load_selection.Moment

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

/-- The accepted finite-load selection theorem with arbitrary finite index types. -/
lemma finite_load_selection_fintype {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    [Fintype σ] [Nonempty σ] {N : ℕ} {a : ℝ} (X : ι → κ → σ → ℝ)
    (hX : ∀ i k s, 0 ≤ X i k s ∧ X i k s ≤ 1)
    (havg : ∀ i k, (N : ℝ) * ∑ s, X i k s ≤ a * Fintype.card σ) :
    ∃ f : Fin N → σ, ∀ i k,
      (∑ j, X i k (f j)) ≤ (Real.exp 1 - 1) * a +
        Real.log ((Fintype.card ι : ℝ) + 1) + Real.log ((Fintype.card κ : ℝ) + 1) := by
  classical
  let eι := (Fintype.equivFin ι).symm
  let eκ := (Fintype.equivFin κ).symm
  let eσ := (Fintype.equivFin σ).symm
  obtain ⟨f, hf⟩ := WangZahlLot.Obl.wz_nsp_finite_load_selection.finite_load_selection_log
    (Fintype.card_pos : 0 < Fintype.card σ)
    (fun i k s => X (eι i) (eκ k) (eσ s)) (fun i k s => hX _ _ _)
    (by
      intro i k
      rw [eσ.sum_comp (fun s => X (eι i) (eκ k) s)]
      exact havg _ _)
  refine ⟨fun j => eσ (f j), ?_⟩
  intro i k
  simpa only [Equiv.apply_symm_apply] using hf (eι.symm i) (eκ.symm k)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
