-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.RelativePieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RelativeCap

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, RelativePieces.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P)
open WangZahlLot.Obl.wz_extremal_lipschitz_grains (incidence incidence_eq_ncard)

/-- Replace only the fine incidence pieces of a prism family. -/
def PrismData.refinePieces {n : ℕ} (D : PrismData n)
    (U : Fin n → Fin D.L → Set V) : PrismData n := { D with W := U }

/-- Relative retention of the old pointwise fine counts is enough to pass
broadness through arbitrary incidence cuts. Geometry is unchanged. -/
theorem valid_relative_pieces {ω ζ δ h h' ρ c t : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (ht : 0 < t) (H : D.Valid ω ζ δ h ρ c x v Y o)
    (U : Fin n → Fin D.L → Set V)
    (hU : ∀ i j, MeasurableSet (U i j) ∧ U i j ⊆ D.W i j)
    (hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (U i j))
    (hdense : ∀ j, O (δ ^ h') * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      volume (⋃ i, U i j))
    (hrelative : ∀ j p, p ∈ ⋃ i, U i j →
      t * incidence (fun i => D.W i j) p ≤ incidence (fun i => U i j) p)
    (hbudget : δ ^ (-h) ≤ t * δ ^ (-h')) :
    (D.refinePieces U).Valid ω ζ δ h' ρ c x v Y o := by
  classical
  rcases H with ⟨ha, hab, hbc, hc, hW, _, _, hcross, hbroad, hX, hw, hcover, hdisj⟩
  have hc0 : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  change D.a ≥ δ ∧ _
  refine ⟨ha, hab, hbc, hc, ?_, hmass, hdense, ?_, ?_, hX, hw, hcover, ?_⟩
  · intro i j
    exact ⟨(hU i j).1, (hU i j).2.trans (hW i j).2.1,
      fun j' hne => ((hW i j).2.2 j' hne).mono (hU i j).2 (hU i j').2⟩
  · intro i j hne
    exact hcross i j (hne.mono (hU i j).2)
  · intro j p u r hu hdr hrρ
    have hf : 0 ≤ (r / ρ) ^ (ω * ζ / 100) :=
      Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _
    have hcap : ∀ p u, ‖u‖ = 1 →
        ({i | p ∈ D.W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r}.ncard : ℝ) ≤
          (δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100)) * incidence (fun i => D.W i j) p := by
      intro p u hu
      simpa only [incidence_eq_ncard] using hbroad j p u r hu hdr hrρ
    have hh := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity.angular_cap_bound_of_relative_incidence
      v (b := r) ht (mul_nonneg (Real.rpow_nonneg hδ.le (-h)) hf)
      (fun i => (hU i j).2) (hrelative j) hcap p u hu
    have hcoef : (δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100)) / t ≤
        δ ^ (-h') * (r / ρ) ^ (ω * ζ / 100) := by
      calc
        _ = (δ ^ (-h) / t) * (r / ρ) ^ (ω * ζ / 100) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ ht).mpr (by simpa [mul_comm] using hbudget)) hf
    exact hh.trans (by
      rw [incidence_eq_ncard]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  · intro ho j j' hne he
    apply (hdisj ho j j' hne he).mono
    · exact iUnion_mono fun i => (hU i j).2
    · exact iUnion_mono fun i => (hU i j').2

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
