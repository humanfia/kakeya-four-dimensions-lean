/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/PaletteData.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.UniformPalette
import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The frozen simultaneous palette event, in a form with measurable
whole-block fit sets. -/
def dataPaletteSource {α H : Type} [MeasurableSpace α] [Fintype H] (D : Data α) (k : ℕ)
    (σ : H → ℝ) (M : H → ℕ)
    (L : (h : H) → Fin (D.n k (σ h)) → Fin (M h) → Fin 4 → ℝ) (C : ℝ) : Set (α × ℝ) :=
  finitePaletteSource (D.b k) (fun h => D.n k (σ h)) M (fun h => D.B k (σ h)) L
    (fun h i => ((D.j k (σ h) i : ℕ) : ℝ) / (2 : ℝ) ^ D.T k (σ h))
    (fun h i => (((D.j k (σ h) i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T k (σ h))
    (fun h => C * D.N k ^ (-σ h))

theorem dataPaletteSource_eq_raw {α H : Type} [MeasurableSpace α] [Fintype H]
    (D : Data α) (k : ℕ) (σ : H → ℝ) (M : H → ℕ)
    (L : (h : H) → Fin (D.n k (σ h)) → Fin (M h) → Fin 4 → ℝ) (C : ℝ) :
    dataPaletteSource D k σ M L C =
      {p | ∀ h, ∃ (i : Fin (D.n k (σ h))) (u : Fin (M h)),
        p.1 ∈ D.B k (σ h) i ∧ p.2 ∈ Data.I (D.T k (σ h)) (D.j k (σ h) i) ∧
        ∀ t ∈ Data.I (D.T k (σ h)) (D.j k (σ h) i),
          |(D.x k p.1 t) 3 - (L h i u 0 + L h i u 1 * t +
            L h i u 2 * (D.x k p.1 t) 1 + L h i u 3 * (D.x k p.1 t) 2)| ≤
              C * D.N k ^ (-σ h)} := by
  ext p
  simp only [dataPaletteSource, finitePaletteSource, mem_iInter, mem_iUnion, mem_prod,
    mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro hp h
    obtain ⟨i, u, ⟨hpB, hpfit⟩, hpt⟩ := hp h
    refine ⟨i, u, hpB, hpt, ?_⟩
    intro t ht
    have hv := hpfit t ht
    change |eval (D.x k p.1 t) (affineBase (L h i u)) - (D.x k p.1 t) 3| ≤
      C * D.N k ^ (-σ h) at hv
    simp only [affineBase, eval_add, eval_mul, eval_C, eval_X] at hv
    have hx0 : (D.x k p.1 t) 0 = t := rfl
    rw [hx0, abs_sub_comm] at hv
    exact hv
  · intro hp h
    obtain ⟨i, u, hpB, hpt, hpfit⟩ := hp h
    refine ⟨i, u, ⟨hpB, ?_⟩, hpt⟩
    intro t ht
    have hv := hpfit t ht
    change |eval (D.x k p.1 t) (affineBase (L h i u)) - (D.x k p.1 t) 3| ≤
      C * D.N k ^ (-σ h)
    simp only [affineBase, eval_add, eval_mul, eval_C, eval_X]
    have hx0 : (D.x k p.1 t) 0 = t := rfl
    rw [hx0, abs_sub_comm]
    exact hv

theorem measurableSet_dataPaletteSource {α H : Type} [MeasurableSpace α] [Fintype H]
    (D : Data α) (k : ℕ) (hb : Measurable (D.b k)) (σ : H → ℝ) (M : H → ℕ)
    (hB : ∀ h i, MeasurableSet (D.B k (σ h) i))
    (L : (h : H) → Fin (D.n k (σ h)) → Fin (M h) → Fin 4 → ℝ) (C : ℝ) :
    MeasurableSet (dataPaletteSource D k σ M L C) := by
  apply measurableSet_finitePaletteSource _ hb _ _ _ hB _ _ _ _
  intro h i
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
