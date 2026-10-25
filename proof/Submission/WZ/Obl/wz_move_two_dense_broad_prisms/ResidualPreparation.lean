-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.ResidualPreparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Preparation

/-! A convenient density form of residual preparation. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- A dense old shading supplies both a dense stem shading and local regular
mass after arbitrary half-mass removal. -/
theorem prepare_dense_residual {n N : ℕ} {d L R lam : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hL1 : L/8 ≤ 1) (hdL : d ≤ L/64)
    (hdR : d ≤ R) (hendpoint : 4608*R ≤ lam) (hlam : 0 < lam)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (f : Fin n → Fin N)
    (Z Y : Fin n → Set V) (hZm : ∀ i, MeasurableSet (Z i))
    (hYm : ∀ i, MeasurableSet (Y i)) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (hYZ : ∀ i, Y i ⊆ Z i)
    (hretain : (1/2 : ENNReal) * (∑ i, volume (Z i)) ≤ ∑ i, volume (Y i))
    (hmin : O (32*lam*(n : ℝ)*d^2) ≤ ∑ i, volume (Z i)) :
    ∃ U W : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ Y i) ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ U i) ∧
      (∀ i p, p ∈ U i → R < dist p (x i) ∧ R < dist p (x i+v i)) ∧
      (∀ i p, p ∈ U i → O (lam*L*d^2/256) ≤ volume (U i ∩ ball p (L/8))) ∧
      O (lam*(n : ℝ)*d^2) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ≤
          32*wz_clustered_cover_volume_gain.fiberBodyCount f W k p := by
  have hhalf : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hYmass : O (16*lam*(n : ℝ)*d^2) ≤ ∑ i, volume (Y i) := by
    calc
      _ = (1/2 : ENNReal) * O (32*lam*(n : ℝ)*d^2) := by
        rw [← hhalf, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ (1/2 : ENNReal) * ∑ i, volume (Z i) := mul_le_mul_right hmin _
      _ ≤ _ := hretain
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod : 0 ≤ lam*(n : ℝ)*d^2 := by positivity
  obtain ⟨U, W, hU, hW, hends, hreg, hmass, hcount⟩ := prepare_residual_shading
    hd (by positivity : 0 < L/8) hL1 (by linarith : d ≤ (L/8)/8) hdR hendpoint
    (by positivity : 0 ≤ lam*d^2) x v hv f Z Y hZm hYm hZT hYZ hretain
    ((ENNReal.ofReal_le_ofReal (show 4*(n : ℝ)*(lam*d^2) ≤ 16*lam*(n : ℝ)*d^2 by nlinarith)).trans hYmass)
    ((ENNReal.ofReal_le_ofReal (show lam*(n : ℝ)*d^2 ≤ 16*lam*(n : ℝ)*d^2 by nlinarith)).trans hYmass)
  refine ⟨U, W, hU, hW, hends, ?_, ?_, hcount⟩
  · intro i p hp
    convert hreg i p hp using 1 <;> congr 1 <;> ring
  · calc
      _ = O (1/32) * O (32*lam*(n : ℝ)*d^2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ O (1/32) * ∑ i, volume (Z i) := mul_le_mul_right hmin _
      _ ≤ _ := hmass

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
