-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PrismSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseEnlarge

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, PrismSelect.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O)

/-- Retaining whole prisms preserves every local condition. Only the
global incidence-mass requirement needs a separate budget. -/
theorem valid_select_prisms {ω ζ δ h h' ρ c : ℝ} {n L o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h')
    (H : D.Valid ω ζ δ h ρ c x v Y o)
    (f : Fin L → Fin D.L) (hf : Function.Injective f)
    (hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j))) :
    (D.select D.s f id (D.γ ∘ f)).Valid ω ζ δ h' ρ c x v Y o := by
  rcases H with ⟨ha, hab, hbc, hc, hW, _, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩
  have hpow := ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh)
  have hpow' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
  have hc0 := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  dsimp only [PrismData.Valid, PrismData.select, Function.comp_apply, id_eq]
  refine ⟨ha, hab, hbc, hc, ?_, hmass, ?_, fun i j => hcross i (f j), ?_, hX, hw, ?_, ?_⟩
  · intro i j
    exact ⟨(hW i (f j)).1, (hW i (f j)).2.1,
      fun j' hne => (hW i (f j)).2.2 (f j') (fun he => hne (hf he))⟩
  · intro j
    exact (mul_le_mul' hpow le_rfl).trans (hdense (f j))
  · intro j p u r hu hdr hrρ
    exact (hbroad (f j) p u r hu hdr hrρ).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow'
          (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ0.le) _))
        (Nat.cast_nonneg _))
  · intro ho
    exact ⟨(hcover ho).1, fun j => (hcover ho).2 (f j)⟩
  · intro ho j j' hne he
    exact hdisj ho (f j) (f j') (fun hh => hne (hf hh)) he

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
