import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualTarget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepVariation

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s R : ℝ}

/-- The physical interval of the frozen frame is the original atlas interval. -/
theorem blockFrame_interval (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) :
    Icc (blockFrame cfg k s i L).t₀
      ((blockFrame cfg k s i L).t₀ + (blockFrame cfg k s i L).q) =
      Data.I (cfg.T k s) (cfg.j k s i) := by
  dsimp only [blockFrame, Data.I]
  congr 1
  field_simp

/-- The geometric bounds hold on the whole original true block, independently of
which projected witnesses or retained law were used later. -/
theorem whole_block_bounds (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L)
    {l : α} {t : ℝ} (hl : l ∈ cfg.B k s i)
    (ht : t ∈ Icc (blockFrame cfg k s i L).t₀
      ((blockFrame cfg k s i L).t₀ + (blockFrame cfg k s i L).q)) :
    |(blockFrame cfg k s i L).zZ (cfg.b k l) t| ≤ cfg.K k ∧
    |(blockFrame cfg k s i L).tr (cfg.b k l) t| ≤ cfg.K k ∧
    |(blockFrame cfg k s i L).resid (cfg.b k l) t| ≤ cfg.K k := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
  have hg : 0 < cfg.N k ^ (-cfg.κ * s) := Real.rpow_pos_of_pos hN _
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  rw [blockFrame_interval] at ht
  obtain ⟨hx, hy, -⟩ := hB.geom i l ((hB.sets i).2.2 hl) t ht
  simp only [x_one, x_two] at hx hy
  have hfit := (hB.fit i l hl t ht).1
  rw [eval_horizontalForm hL] at hfit
  simp only [Data.x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hfit
  refine ⟨?_, ?_, ?_⟩
  · simp only [Frame.zZ, blockFrame]
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    exact hx
  · simp only [Frame.tr, blockFrame]
    rw [abs_div, abs_of_pos (mul_pos hq hg), div_le_iff₀ (mul_pos hq hg)]
    exact hy.trans_eq (by ring)
  · simp only [Frame.resid, blockFrame]
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    exact hfit

namespace ComparedBlock

variable {u v χ H : ℝ} (CB : ComparedBlock cfg k s u v χ H)

/-- The exact frozen per-index output follows from a restriction carrying the
residual table. The chosen set is the entire original `B_i`. -/
theorem extractionAt_of_residual_table (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    {θ m J : ℝ} (lam : Measure (α × ℝ)) (hlam : lam ≤ CB.lam)
    (C : Fin 4 → ℝ)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-θ)) *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s CB.i)) ≤ lam univ)
    (hL : H * cfg.N k ^ (2 * s) ≤ cfg.N k ^ J)
    (hC : ∀ e, |C e| ≤ cfg.N k ^ θ) (hK : cfg.K k ≤ cfg.N k ^ θ)
    (Fs : Finset ((Fin 2 → ℤ) × ℤ))
    (hcard : (Fs.card : ℝ) * (cfg.N k ^ (-m)) ^ 2 ≤
      cfg.N k ^ θ * (cfg.N k ^ (-v)) ^ (-cfg.d))
    (hsupport : ∀ᵐ p ∂lam,
      outBins (blockFrame cfg k s CB.i CB.L) C (cfg.N k ^ (-m)) (cfg.N k ^ (-v))
        (cfg.b k p.1) p.2 ∈ Fs) :
    Submission.Obl.k4_wide_three_layer_scalar_inputs.Data.ExtractionAt cfg k θ s v m J := by
  refine ⟨CB.i, lam, cfg.B k s CB.i, CB.L, C, (hB.sets CB.i).2.1, subset_rfl,
    hlam.trans CB.lam_le, ae_mono hlam CB.lam_supp, hmass,
    fun e => (CB.L_bd e).trans hL, hC, ?_, Fs, hcard, ?_⟩
  · intro l hl t ht
    obtain ⟨hz, htr, hres⟩ := whole_block_bounds hB hN CB.i CB.L CB.hL hl ht
    exact ⟨hz.trans hK, htr.trans hK, hres.trans hK⟩
  · exact hsupport

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
