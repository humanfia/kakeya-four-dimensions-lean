-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.AngularScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Defs

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, AngularScale.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V q)

/-- Enlarging the angular scale only costs its power in the broadness
constant; above the old scale the trivial cardinality bound suffices. -/
theorem angular_bound_enlarge {n : ℕ} (v : Fin n → V) (S : Set (Fin n))
    {δ ρ ρ' β C C' : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρρ : ρ ≤ ρ')
    (hβ : 0 ≤ β) (hC : 1 ≤ C) (hscale : C * (ρ' / ρ) ^ β ≤ C')
    (hbroad : ∀ (u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        C * (r / ρ) ^ β * q n S) :
    ∀ (u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ' →
      q n {i | i ∈ S ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        C' * (r / ρ') ^ β * q n S := by
  have hρ' : 0 < ρ' := hρ.trans_le hρρ
  intro u r hu hdr hrρ'
  have hr : 0 < r := hδ.trans_le hdr
  have hfactor : C * (r / ρ) ^ β ≤ C' * (r / ρ') ^ β := by
    have he : r / ρ = (r / ρ') * (ρ' / ρ) := by field_simp
    calc
      C * (r / ρ) ^ β = (C * (ρ' / ρ) ^ β) * (r / ρ') ^ β := by
        rw [he, Real.mul_rpow (by positivity) (by positivity)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
  by_cases hrρ : r ≤ ρ
  · exact (hbroad u r hu hdr hrρ).trans
      (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _))
  · have hρr : ρ ≤ r := (lt_of_not_ge hrρ).le
    have hratio : 1 ≤ (r / ρ) ^ β :=
      Real.one_le_rpow ((one_le_div hρ).mpr hρr) hβ
    have hcoeff : 1 ≤ C' * (r / ρ') ^ β := by
      calc
        1 ≤ C * (r / ρ) ^ β := by nlinarith
        _ ≤ _ := hfactor
    have hcount : q n {i | i ∈ S ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤ q n S :=
      Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hi => hi.1))
    exact hcount.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hcoeff)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
