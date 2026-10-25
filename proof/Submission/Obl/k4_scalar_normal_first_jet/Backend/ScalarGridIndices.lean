/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridIndices.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridIndices.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry
import Mathlib.Data.Int.Interval

/-! Finite occupied integer grids with original representatives. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem bounded_scalar_grid_indices {Λ : Type*} (A : Set Λ) (v : Λ → ℝ) {B p : ℝ}
    (hB : 0 ≤ B) (hp : 0 < p) (hv : ∀ l ∈ A, |v l| ≤ B) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 2 * B / p + 3 ∧
      (∀ l ∈ A, ⌊v l / p⌋ ∈ J) ∧ ∀ j ∈ J, ∃ l ∈ A, ⌊v l / p⌋ = j := by
  classical
  let J := (Finset.Icc ⌊-B / p⌋ ⌊B / p⌋).filter (fun j => ∃ l ∈ A, ⌊v l / p⌋ = j)
  have hindex : ∀ l ∈ A, ⌊-B / p⌋ ≤ ⌊v l / p⌋ ∧ ⌊v l / p⌋ ≤ ⌊B / p⌋ := by
    intro l hl
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hv l hl)
    exact ⟨Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr hlo),
      Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr hhi)⟩
  have hcard : (J.card : ℝ) ≤ 2 * B / p + 3 := by
    have horder : ⌊-B / p⌋ ≤ ⌊B / p⌋ :=
      Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr (by linarith))
    have hcountZ := Int.card_Icc_of_le (a := ⌊-B / p⌋) (b := ⌊B / p⌋) (by omega)
    have hcountR : ((Finset.Icc ⌊-B / p⌋ ⌊B / p⌋).card : ℝ) =
        (⌊B / p⌋ : ℝ) + 1 - ⌊-B / p⌋ := by exact_mod_cast hcountZ
    have hfilter : (J.card : ℝ) ≤ ((Finset.Icc ⌊-B / p⌋ ⌊B / p⌋).card : ℝ) := by
      exact_mod_cast (Finset.card_filter_le (s := Finset.Icc ⌊-B / p⌋ ⌊B / p⌋)
        (p := fun j => ∃ l ∈ A, ⌊v l / p⌋ = j))
    rw [hcountR] at hfilter
    have hlo := Int.lt_floor_add_one (-B / p)
    have hhi := Int.floor_le (B / p)
    simp only [neg_div] at hlo hfilter
    rw [show 2 * B / p = 2 * (B / p) by ring]
    linarith
  refine ⟨J, hcard, ?_, ?_⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hindex l hl), l, hl, rfl⟩
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
