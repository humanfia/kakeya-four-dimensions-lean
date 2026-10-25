-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactMesh.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set

/-- A mesh of a closed interval can have step between half and all of a
prescribed scale, with every center still inside the interval. -/
theorem exists_interval_contact_mesh {a b h : ℝ}
    (hab : a < b) (hh : 0 < h) (hsize : h ≤ b - a) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ h / 2 ≤ ℓ ∧ ℓ ≤ h ∧ ∃ T : Finset ℤ,
      (∀ k ∈ T, a + k * ℓ ∈ Icc a b) ∧
      (∀ x ∈ Icc a b, ∃ k ∈ T, |x - (a + k * ℓ)| ≤ ℓ) := by
  classical
  let N : ℕ := ⌈(b - a) / h⌉₊
  have hratio : 0 < (b - a) / h := div_pos (sub_pos.mpr hab) hh
  have hNpos : 0 < N := Nat.ceil_pos.mpr hratio
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hNlo : (b - a) / h ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) < (b - a) / h + 1 := Nat.ceil_lt_add_one hratio.le
  have hlow : b - a ≤ N * h := (div_le_iff₀ hh).mp hNlo
  have hupp : (N : ℝ) * h ≤ 2 * (b - a) := by
    have hmul := mul_lt_mul_of_pos_right hNhi hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at hmul
    linarith
  let ℓ := (b - a) / N
  have hℓ : 0 < ℓ := div_pos (sub_pos.mpr hab) hNr
  have hℓN : ℓ * N = b - a := div_mul_cancel₀ _ hNr.ne'
  have hhℓ : h / 2 ≤ ℓ := by
    apply (le_div_iff₀ hNr).mpr
    nlinarith
  have hℓh : ℓ ≤ h := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith
  let T := Finset.Icc (0 : ℤ) N
  refine ⟨ℓ, hℓ, hhℓ, hℓh, T, ?_, ?_⟩
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk'.1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk'.2
    constructor
    · nlinarith
    · nlinarith
  · intro x hx
    let k : ℤ := ⌊(x - a) / ℓ⌋
    have hr0 : 0 ≤ (x - a) / ℓ := div_nonneg (sub_nonneg.mpr hx.1) hℓ.le
    have hk0 : 0 ≤ k := Int.floor_nonneg.mpr hr0
    have hkle : (k : ℝ) ≤ (x - a) / ℓ := Int.floor_le _
    have hklt : (x - a) / ℓ < k + 1 := Int.lt_floor_add_one _
    have hrN : (x - a) / ℓ ≤ N := by
      apply (div_le_iff₀ hℓ).mpr
      nlinarith [hx.2]
    have hkN : k ≤ N := by exact_mod_cast hkle.trans hrN
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkN⟩, ?_⟩
    have hklo := (le_div_iff₀ hℓ).mp hkle
    have hkhi := (div_lt_iff₀ hℓ).mp hklt
    apply abs_le.mpr
    constructor <;> nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
