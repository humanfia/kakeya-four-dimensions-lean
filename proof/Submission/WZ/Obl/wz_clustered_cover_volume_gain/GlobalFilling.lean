-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GlobalFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularFilling
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.LocalToGlobal
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Net

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- An angular annulus fills a thin neighbourhood of an entire regular anchor
prism. The lower bound has the same single angular factor as the neighbourhood. -/
theorem angular_global_filling {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B)
    {a b h h₀ θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hh₀ : 0 < h₀) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ : V) (u₀ : Fin 3 → V) (H₀ : Set V)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hHm : ∀ i, MeasurableSet (H i))
    (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hH₀ : H₀ ⊆ prism a b c₀ u₀)
    (hdense₀ : O h₀ * μ (prism a b c₀ u₀) ≤ μ H₀)
    (hregular₀ : ∀ p ∈ H₀,
      O h₀ * μ (prism a b c₀ u₀ ∩ ball p b) ≤ μ (H₀ ∩ ball p b))
    (hcover : H₀ ⊆ ⋃ i, H i)
    (hangle : ∀ i, θ ≤ pd (u i 0) (u₀ 0) ∧ pd (u i 0) (u₀ 0) ≤ B * θ) :
    O (h₀ ^ 2 * h ^ 2 * θ * b ^ 2 /
      (52428800000000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a)))) ≤
      μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b} ∩
        (cTube b c₀ u₀ ∩ ⋃ i, H i)) := by
  have hb0 : 0 < b := ha.trans_le hab
  let S : Set V := {p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b}
  let E : Set V := S ∩ (cTube b c₀ u₀ ∩ ⋃ i, H i)
  have hSm : MeasurableSet S :=
    (isClosed_le ((continuous_const.inner (continuous_id.sub continuous_const)).abs)
      continuous_const).measurableSet
  have hEm : MeasurableSet E := hSm.inter
    (isOpen_thickening.measurableSet.inter (MeasurableSet.iUnion hHm))
  let D : ℝ := 409600000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a))
  have hD : 0 < D := by
    have hl := Real.log_nonneg ((one_le_div ha).mpr hab)
    dsimp [D]
    positivity
  let q : ℝ := (h₀ / 8) * h ^ 2 * θ * b ^ 3 / D
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlocal : ∀ x ∈ H₀, O q ≤ μ (E ∩ ball x (2 * b)) := by
    intro x hx
    have hpatch : O ((h₀ / 8) * a * b ^ 2) ≤ μ (H₀ ∩ ball x b) := by
      convert loc_regular_lower ha hab hb hh₀.le hu₀ (hH₀ hx) (hregular₀ x hx) using 1
      congr 1
      ring
    have hhx := angular_slab_filling hn hB ha hab hb hh hθ hθ1 (by positivity : 0 < h₀ / 8)
      c u H c₀ x u₀ (H₀ ∩ ball x b) hu hHm hHU hregular hu₀
      (inter_subset_inter_left _ hH₀) (inter_subset_left.trans hcover) hpatch hangle
    apply hhx.trans
    apply measure_mono
    intro p hp
    exact ⟨⟨hp.1, ball_subset_cTube ha.le hab hu₀ (hH₀ hx) hp.2.1, hp.2.2⟩, hp.2.1⟩
  have hupper : ∀ x ∈ H₀, μ (H₀ ∩ closedBall x (4 * b)) ≤ O (128 * a * b ^ 2) := by
    intro x _
    calc
      _ ≤ μ (prism a b c₀ u₀ ∩ closedBall x (4 * b)) :=
        measure_mono (inter_subset_inter_left _ hH₀)
      _ ≤ O (8 * a * (4 * b) ^ 2) := prism_ball_volume_upper a b (4 * b) c₀ x hu₀
      _ = _ := by congr 1; ring
  have hwhole := local_mass_to_global hb0 ((prism_totallyBounded a b c₀ hu₀).subset hH₀)
    hEm hupper hlocal
  let t : ℝ := h₀ ^ 2 * h ^ 2 * θ * b ^ 2 /
    (52428800000000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a)))
  have ht : t = h₀ ^ 2 * h ^ 2 * θ * b ^ 2 / (128000 * D) := by
    dsimp [t, D]
    congr 1
    ring
  have hbound : O (128 * a * b ^ 2) * O t ≤ O (128 * a * b ^ 2) * μ E := by
    calc
      _ = O q * (O h₀ * μ (prism a b c₀ u₀)) := by
        change ENNReal.ofReal (128 * a * b ^ 2) * ENNReal.ofReal t =
          ENNReal.ofReal q * (ENNReal.ofReal h₀ * volume (prism a b c₀ u₀))
        rw [volume_prism ha.le hb0.le c₀ hu₀]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 128 * a * b ^ 2),
          ← ENNReal.ofReal_mul hh₀.le, ← ENNReal.ofReal_mul hq]
        congr 1
        rw [ht]
        dsimp [q]
        field_simp [hD.ne']
        ring
      _ ≤ O q * μ H₀ := mul_le_mul' (le_refl (O q)) hdense₀
      _ ≤ _ := hwhole
  have hm0 : O (128 * a * b ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hh' := mul_le_mul' (le_refl (O (128 * a * b ^ 2))⁻¹) hbound
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, one_mul] using hh'

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
