-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.Monotone.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Defs

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, Monotone.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V μ O q T X P)

/-- Increasing the error and lowering the stage weakens the prism predicate. -/
theorem G_mono {ω ζ δ h h' ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {o o' : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hoo : o' ≤ o)
    (H : G ω ζ δ h ρ c n x v Y o) : G ω ζ δ h' ρ c n x v Y o' := by
  obtain ⟨a, s, L, N, z, e, W, y, w, γ, ha, hab, hbc, hc,
    hW, hmass, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩ := H
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh
  have hn := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
  refine ⟨a, s, L, N, z, e, W, y, w, γ, ha, hab, hbc, hc, hW,
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

/-- The ordering of the prism sides forces the radius and length to be positive. -/
theorem G_scales {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {o : ℕ} (hδ : 0 < δ)
    (H : G ω ζ δ h ρ c n x v Y o) :
    δ ≤ ρ ∧ 0 < ρ ∧ ρ ≤ 1 ∧ δ ≤ c ∧ 0 < c ∧ c ≤ 1 := by
  obtain ⟨a, s, L, N, z, e, W, y, w, γ, ha, hab, hbc, hc, _⟩ := H
  have hdc : δ ≤ c := ha.trans (hab.trans hbc)
  have hc0 : 0 < c := hδ.trans_le hdc
  have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hc0).mp (by simpa using hbc)
  exact ⟨ha.trans (hab.trans (by nlinarith)), hρ0, hρ1, hdc, hc0, hc⟩

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
