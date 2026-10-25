-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PieceMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Extraction
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-! Uniform positive mass for the residual iteration. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal

/-- Density and the minimum prism side give a uniform positive mass increment. -/
lemma PrismPiece.Good.incidence_mass {n N J : ℕ} {ω ζ d h a c s : ℝ} {ρ : Fin J → ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {B : PrismPiece n N J}
    (hd : 0 < d) (hB : B.Good ω ζ d h a c s ρ x v y w) :
    d ^ h * d ^ 3 ≤ ∑ i, volume.real (B.piece i) := by
  have ha : 0 < a := hd.trans_le hB.1
  have hb : 0 < ρ B.scale * c := ha.trans_le hB.2.1
  have hc : 0 < c := hb.trans_le hB.2.2.1
  have hvol : μ (P a (ρ B.scale * c) c B.center B.frame) = O (a * (ρ B.scale * c) * c) :=
    wz_two_scale_flat_box_estimate.box_volume ha.le hb.le hc.le B.center B.frame
  have hvol₀ : d ^ 3 ≤ a * (ρ B.scale * c) * c := by
    calc
      d ^ 3 = d * d * d := by ring
      _ ≤ a * (ρ B.scale * c) * c :=
        mul_le_mul (mul_le_mul hB.1 (hB.1.trans hB.2.1) hd.le ha.le)
          (hB.1.trans (hB.2.1.trans hB.2.2.1)) hd.le (mul_nonneg ha.le hb.le)
  have hBfin (i : Fin n) : volume (B.piece i) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (measure_mono (hB.2.2.2.2.1 i).2).trans_eq hvol
  have hmass : O (d ^ h * d ^ 3) ≤ ∑ i, μ (B.piece i) := by
    calc
      _ ≤ O (d ^ h * (a * (ρ B.scale * c) * c)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hvol₀ (Real.rpow_nonneg hd.le _))
      _ = O (d ^ h) * μ (P a (ρ B.scale * c) c B.center B.frame) := by
        rw [hvol]
        exact ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)
      _ ≤ μ (⋃ i, B.piece i) := hB.2.2.2.2.2.1
      _ ≤ ∑ i, μ (B.piece i) := by simpa only [tsum_fintype] using measure_iUnion_le B.piece
  have hreal := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.sum_ne_top.mpr (fun i _ => hBfin i))).mp hmass
  simpa only [Measure.real, ENNReal.toReal_sum (fun i _ => hBfin i)] using hreal

/-- The local selector only has to produce a dense prism; its dimensions supply
the mass increment required for termination automatically. -/
theorem stage_zero_of_selector {n N J : ℕ} (hJ : 0 < J)
    {ω ζ d h τ a c s : ℝ} {ρ : Fin J → ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V}
    (hd : 0 < d)
    (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hYpos : 0 < ∑ i, volume.real (Y i))
    (hretain : d ^ τ * ∑ i, volume.real (Y i) ≤ ∑ i, volume.real (Z i))
    (hbudget : 2 * J * d ^ h ≤ d ^ τ)
    (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1)
    (hselect : ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) →
      (∀ i, R i ⊆ Z i) →
      (∑ i, volume.real (Z i)) / 2 ≤ ∑ i, volume.real (R i) →
      ∃ B : PrismPiece n N J, B.Good ω ζ d h a c s ρ x v y w ∧
        ∀ i, B.piece i ⊆ R i) :
    ∃ k : Fin J, G ω ζ d h (ρ k) c n x v Y 0 := by
  apply stage_zero_of_residual_selector hJ hd
    (mul_pos (Real.rpow_pos_of_pos hd h) (pow_pos hd 3)) hYfin hZm hZY hYpos hretain hbudget hX hw
  intro R hRm hRZ hRmass
  obtain ⟨B, hB, hBR⟩ := hselect R hRm hRZ hRmass
  exact ⟨B, hB, hBR, hB.incidence_mass hd⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
