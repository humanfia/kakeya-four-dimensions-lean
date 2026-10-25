/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDyadicTimeGrid.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDyadicTimeGrid.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarTimeGrid
import Submission.Obl.k4_matching_homogeneous_records.Encoding

/-! The actual half-open scalar time code respects dyadic refinement. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem scalarTimeBlockCode_val {J : ℕ} (hJ : 0 < J) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (scalarTimeBlockCode J hJ t).val = ⌊t * (J : ℝ)⌋₊ := by
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hfloor : ⌊t * (J : ℝ)⌋₊ < J :=
    (Nat.floor_lt (mul_nonneg ht.1 hJpos.le)).mpr (by nlinarith [ht.2])
  exact Nat.mod_eq_of_lt hfloor

theorem scalarTimeBlockCode_time_close {J : ℕ} (hJ : 0 < J) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (he : scalarTimeBlockCode J hJ s = scalarTimeBlockCode J hJ t) :
    |s - t| ≤ 1 / (J : ℝ) := by
  let j := scalarTimeBlockCode J hJ s
  have hsCell := (scalarTimeBlockCode_eq_iff hJ j hs).mp rfl
  have htCell := (scalarTimeBlockCode_eq_iff hJ j ht).mp he.symm
  have hwidth : (((j : ℕ) : ℝ) + 1) / (J : ℝ) = (j : ℕ) / (J : ℝ) + 1 / (J : ℝ) := by ring
  exact abs_le.mpr ⟨by linarith [hsCell.1, hsCell.2, htCell.1, htCell.2],
    by linarith [hsCell.1, hsCell.2, htCell.1, htCell.2]⟩

theorem scalarTimeBlockCode_dyadic_nesting {a b : ℕ} (hab : a ≤ b) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (he : scalarTimeBlockCode (2 ^ b) (by positivity) s =
      scalarTimeBlockCode (2 ^ b) (by positivity) t) :
    scalarTimeBlockCode (2 ^ a) (by positivity) s = scalarTimeBlockCode (2 ^ a) (by positivity) t := by
  have hf := congrArg Fin.val he
  rw [scalarTimeBlockCode_val (by positivity) hs, scalarTimeBlockCode_val (by positivity) ht] at hf
  have hnat : ⌊s * (2 : ℝ) ^ b⌋₊ = ⌊t * (2 : ℝ) ^ b⌋₊ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hf
  have hint : ⌊s * (2 : ℝ) ^ b⌋ = (⌊t * (2 : ℝ) ^ b⌋ : ℤ) := by
    rw [← Int.natCast_floor_eq_floor (mul_nonneg hs.1 (by positivity)),
      ← Int.natCast_floor_eq_floor (mul_nonneg ht.1 (by positivity)), hnat]
  have hcoarse := Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_eq_of_finer_eq hab hint
  apply Fin.ext
  rw [scalarTimeBlockCode_val (by positivity) hs, scalarTimeBlockCode_val (by positivity) ht]
  simpa only [Int.floor_toNat, Nat.cast_pow, Nat.cast_ofNat] using congrArg Int.toNat hcoarse

/-- The stored finite time code agrees on any original half-open
dyadic interval, even when its index is presented as an integer. -/
theorem scalarTimeBlockCode_eq_of_common_dyadic_interval {T : ℕ} {j : ℤ} {s t : ℝ}
    (hs0 : s ∈ Ico (0 : ℝ) 1) (ht0 : t ∈ Ico (0 : ℝ) 1)
    (hs : s ∈ Ico ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T))
    (ht : t ∈ Ico ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)) :
    scalarTimeBlockCode (2 ^ T) (by positivity) s =
      scalarTimeBlockCode (2 ^ T) (by positivity) t := by
  have hpos : 0 < (2 : ℝ) ^ T := by positivity
  have hfloor (u : ℝ)
      (hu : u ∈ Ico ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)) :
      ⌊u * (2 : ℝ) ^ T⌋ = j := by
    exact Int.floor_eq_iff.mpr
      ⟨(div_le_iff₀ hpos).mp hu.1, (lt_div_iff₀ hpos).mp hu.2⟩
  apply Fin.ext
  rw [scalarTimeBlockCode_val (by positivity) hs0, scalarTimeBlockCode_val (by positivity) ht0]
  have hnat := congrArg Int.toNat ((hfloor s hs).trans (hfloor t ht).symm)
  simpa only [Int.floor_toNat, Nat.cast_pow, Nat.cast_ofNat] using hnat

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
