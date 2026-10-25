-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CapsBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedEndpoint
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P bodyCount frozen_prism_volume)

/-- The density clause forces every cap in the frozen statement to be positive. -/
theorem PrismData.hasCaps_of_frozen {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (H : D.Valid ω ζ δ h ρ c x v Y o)
    (m : Fin D.L → ℝ)
    (hm : ∀ j, (∀ p, bodyCount (fun i => D.W i j) p ≤ m j) ∧
      O (δ ^ h * m j) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
        ∑ i, volume (D.W i j)) :
    D.HasCaps δ h ρ c := by
  refine ⟨m, ?_, fun j => (hm j).1, fun j => (hm j).2⟩
  intro j
  have ha : 0 < D.a := hδ.trans_le H.1
  have hb : 0 < ρ * c := ha.trans_le H.2.1
  have hc : 0 < c := hb.trans_le H.2.2.1
  have hvol : 0 < volume (P D.a (ρ * c) c (D.z j) (D.e j)) := by
    rw [frozen_prism_volume ha.le hb.le hc.le]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hmass : 0 < volume (⋃ i, D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne'
      hvol.ne').trans_le (H.2.2.2.2.2.2.1 j)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hmass.ne'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hcount : 0 < bodyCount (fun i => D.W i j) p := by
    exact Nat.cast_pos.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hi⟩)
  exact hcount.trans_le ((hm j).1 p)

/-- A larger error parameter preserves the same geometric witnesses. -/
theorem PrismData.valid_mono {ω ζ δ h h' ρ c : ℝ} {n o o' : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hoo : o' ≤ o)
    (H : D.Valid ω ζ δ h ρ c x v Y o) :
    D.Valid ω ζ δ h' ρ c x v Y o' := by
  rcases H with ⟨ha, hab, hbc, hc, hW, hmass, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh
  have hn := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
  refine ⟨ha, hab, hbc, hc, hW,
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl).trans hmass,
    fun j => (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl).trans (hdense j),
    hcross, ?_, hX, hw, fun ho => hcover (ho.trans hoo), fun ho => hdisj (ho.trans hoo)⟩
  intro j p u r hu hdr hrρ
  have hc0 : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  exact (hbroad j p u r hu hdr hrρ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ0.le) _))
      (Nat.cast_nonneg _))

theorem PrismData.hasCaps_mono {δ h h' ρ c : ℝ} {n : ℕ} (D : PrismData n)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (H : D.HasCaps δ h ρ c) :
    D.HasCaps δ h' ρ c := by
  obtain ⟨m, hm, hcount, havg⟩ := H
  refine ⟨m, hm, hcount, fun j => ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh)
      (hm j).le)) le_rfl).trans (havg j)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
