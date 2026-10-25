-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_twisted_extraction.Monotonicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_sticky_twisted_extraction.Frostman

namespace WangZahlLot.Obl.wz_sticky_twisted_extraction

open Set Metric MeasureTheory
open scoped ENNReal

theorem DenseFamily.mono_error {η η' δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : DenseFamily η δ n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    DenseFamily η' δ n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  apply le_trans (b := ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2)) _ h.2.2.2.2.2.2
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη) (Nat.cast_nonneg _))
    (sq_nonneg _)

theorem AllScales.mono_error {η η' δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : AllScales η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    AllScales η' δ n x v := by
  have hm : δ ^ (-η) ≤ δ ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρ, k, hk, z, w, hw, hd, hp, ho, hb, hc⟩ := h r hδr hr1
  refine ⟨ρ, hrρ, hρ1, hρ.trans ?_, k, hk, z, w, hw, hd, hp, ho, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right hm (hδ.le.trans hδr)
  · intro j j'
    exact (hb j j').trans (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))
  · intro j W hW
    apply (hc j W hW).trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))) le_rfl

theorem GlobalFrostman.mono_error {η η' δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : GlobalFrostman η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    GlobalFrostman η' δ n x v := by
  intro W hW
  apply (h W hW).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)) (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_sticky_twisted_extraction
