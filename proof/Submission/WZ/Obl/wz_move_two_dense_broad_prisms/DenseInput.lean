-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DenseInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

/-! Data passed from the old-grain brush to angular packet extraction. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory

/-- A locally supported family with large incidence density inside one prism.
All participating whole fine tubes cross this prism and retain endpoint room. -/
structure DensePrismInput (ω d lam a b L s : ℝ) {n N : ℕ}
    (x v : Fin n → V) (y w : Fin N → V) (Y : Fin n → Set V) where
  coarse : Fin N
  center : V
  frame : V ≃ₗᵢ[ℝ] V
  shading : Fin n → Set V
  delta_le_thickness : d ≤ a
  thickness_le_width : a ≤ b
  width_le_length : b ≤ L
  length_le_one : L ≤ 1
  ten_length_le_one : 10*L ≤ 1
  thickness_small : a ≤ L/1000000
  width_small : b ≤ L/100
  measurable : ∀ i, MeasurableSet (shading i)
  subset : ∀ i, shading i ⊆ Y i ∩ P a b L center frame
  in_tube : ∀ i, shading i ⊆ T d (x i) (v i)
  in_ball : ∀ i, shading i ⊆ ball center (L/2)
  endpoints : ∀ i p, p ∈ shading i →
    1000000000000*L < dist p (x i) ∧ 1000000000000*L < dist p (x i+v i)
  incidence : O (d^(-ω/2))*volume (P a b L center frame) ≤ ∑ i, volume (shading i)
  tube_mass : ∀ i, (shading i).Nonempty → O (lam*L*d^2/256) ≤ volume (shading i)
  crossing : ∀ i, (shading i).Nonempty →
    T d (x i) (v i) ⊆ T s (y coarse) (w coarse) ∧ Crosses d a b L (x i) (v i) center frame

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
