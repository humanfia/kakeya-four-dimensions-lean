-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ThickGrainDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

/-- A dense grain whose shortest side exceeds twice the common ball radius
forces a comparable density in that ball class. -/
theorem thick_grain_forces_ball_density {a b c r D lam : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hr : 0 < r) (hra : r ≤ a / 2)
    (hD : 0 ≤ D) (hlam : 0 ≤ lam) (z : V) (e : V ≃ₗᵢ[ℝ] V) (H U : Set V)
    (hHU : H ⊆ U) (hHP : H ⊆ P a b c z e)
    (hdense : ENNReal.ofReal D * volume (P a b c z e) ≤ volume H)
    (hupper : ∀ p ∈ H, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lam * r ^ 3)) :
    D ≤ 512 * lam := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hTB : TotallyBounded H :=
    (frozen_prism_compact ha.le hab hbc z e).totallyBounded.subset hHP
  have hbox : H ⊆ (AffineEquiv.refl ℝ V) ''
      orthogonalBox ![a / 2, b / 2, c / 2] z (frozenBasis e) := by
    simpa only [AffineEquiv.coe_refl, image_id, ← frozen_prism_box] using hHP
  have hh := affine_ball_density_mass_in_box hr (by norm_num : (0 : ℝ) ≤ 1) hTB hHU
    (AffineEquiv.refl ℝ V) ![a / 2, b / 2, c / 2] z (frozenBasis e)
    (fun p q => by simp) hbox hupper
  simp only [AffineEquiv.coe_refl, image_id] at hh
  have hsub : orthogonalBox (fun j => (![a / 2, b / 2, c / 2] : Fin 3 → ℝ) j + 1 * r)
      z (frozenBasis e) ⊆ orthogonalBox ![a, b, c] z (frozenBasis e) := by
    intro p hp j
    have hj := hp j
    fin_cases j <;> norm_num at hj ⊢ <;> linarith
  have hvol : volume (orthogonalBox ![a, b, c] z (frozenBasis e)) = ENNReal.ofReal (8 * (a * b * c)) := by
    rw [volume_orthogonalBox]
    · congr 1
      norm_num [Fin.prod_univ_three]
    · intro j
      fin_cases j <;> simp <;> positivity
  have hmass : ENNReal.ofReal (D * (a * b * c)) ≤ ENNReal.ofReal (512 * lam * (a * b * c)) := by
    calc
      _ = ENNReal.ofReal D * volume (P a b c z e) := by
        rw [frozen_prism_volume ha.le hb.le hc.le, ENNReal.ofReal_mul hD]
      _ ≤ volume H := hdense
      _ ≤ _ := hh
      _ ≤ ENNReal.ofReal (64 * lam) * volume (orthogonalBox ![a, b, c] z (frozenBasis e)) :=
        mul_le_mul' le_rfl (measure_mono hsub)
      _ = _ := by rw [hvol, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * lam)]; congr 1; ring
  have hre := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 512 * lam * (a * b * c))).mp hmass
  exact (mul_le_mul_iff_left₀ (show 0 < a * b * c by positivity)).mp hre

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
