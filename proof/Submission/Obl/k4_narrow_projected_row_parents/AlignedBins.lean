import Mathlib

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set
open scoped ENNReal

/-- Coarse and fine floors agree under an integer subdivision of the width. -/
theorem floor_aligned_refinement (x χ : ℝ) {J : ℕ} (hJ : 0 < J) :
    ⌊x / χ⌋ = ⌊x / (χ / J)⌋ / (J : ℤ) := by
  rw [← Int.floor_div_natCast]
  congr 1
  have hJ' : (J : ℝ) ≠ 0 := by positivity
  simp only [div_div, div_mul_cancel₀ _ hJ']

/-- An old bin is the disjoint union of its `J` aligned finer bins. -/
theorem aligned_bin_union (χ : ℝ) {J : ℕ} (hJ : 0 < J) (j : ℤ) :
    {x : ℝ | ⌊x / χ⌋ = j} =
      ⋃ a : Fin J, {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * j + (a : ℕ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  rw [floor_aligned_refinement x χ hJ]
  let q : ℤ := ⌊x / (χ / J)⌋
  change q / (J : ℤ) = j ↔ ∃ a : Fin J, q = (J : ℤ) * j + (a : ℕ)
  have hJz : (0 : ℤ) < J := by exact_mod_cast hJ
  constructor
  · intro hq
    have hmod0 : 0 ≤ q % (J : ℤ) := Int.emod_nonneg q (by omega)
    have hmodJ : q % (J : ℤ) < J := Int.emod_lt_of_pos q hJz
    let a : Fin J := ⟨(q % (J : ℤ)).toNat, by omega⟩
    refine ⟨a, ?_⟩
    have ha : ((a : ℕ) : ℤ) = q % (J : ℤ) := Int.toNat_of_nonneg hmod0
    rw [ha, ← hq]
    simpa only [add_comm, mul_comm] using (Int.emod_add_mul_ediv q (J : ℤ)).symm
  · rintro ⟨a, ha⟩
    rw [ha]
    rw [Int.mul_add_ediv_left _ _ (by omega : (J : ℤ) ≠ 0)]
    have ha0 : (0 : ℤ) ≤ (a : ℕ) := by positivity
    have haJ : ((a : ℕ) : ℤ) < J := by exact_mod_cast a.2
    rw [Int.ediv_eq_zero_of_lt ha0 haJ]
    ring

/-- Aligned refinement preserves the palette mass of every original bin. -/
theorem sum_aligned_palette (π : Measure ℝ) (χ : ℝ) {J : ℕ} (hJ : 0 < J) (j : ℤ) :
    (∑ a : Fin J, π {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * j + (a : ℕ)}) =
      π {x : ℝ | ⌊x / χ⌋ = j} := by
  rw [aligned_bin_union χ hJ j]
  symm
  let bin : Fin J → Set ℝ := fun a =>
    {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * j + (a : ℕ)}
  have hd : Pairwise (fun a a' : Fin J => Disjoint (bin a) (bin a')) := by
    intro a a' haa'
    apply disjoint_left.mpr
    intro x hx hx'
    have hval : ((a : ℕ) : ℤ) = (a' : ℕ) := by
      change ⌊x / (χ / J)⌋ = (J : ℤ) * j + (a : ℕ) at hx
      change ⌊x / (χ / J)⌋ = (J : ℤ) * j + (a' : ℕ) at hx'
      linarith
    exact haa' (Fin.ext (by exact_mod_cast hval))
  have hm : ∀ a, MeasurableSet (bin a) := by
    intro a
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  simpa only [tsum_fintype] using (measure_iUnion (μ := π) hd hm)

/-- The fine intercept count cancels the smaller mesh width, while the fine
velocity palette masses add to the original velocity bin. -/
theorem sum_aligned_reference {ι : Type*} [Fintype ι]
    (π : Measure ℝ) (χ : ℝ) {J : ℕ} (hJ : 0 < J)
    (tag : ι → ℤ) (weight : ι → ℝ) :
    (∑ i, ∑ a : Fin J, ∑ _b : Fin J,
      ENNReal.ofReal ((χ / J) * weight i) *
        π {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * tag i + (a : ℕ)}) =
      ∑ i, ENNReal.ofReal (χ * weight i) * π {x : ℝ | ⌊x / χ⌋ = tag i} := by
  apply Finset.sum_congr rfl
  intro i hi
  have hcancel : (J : ℝ≥0∞) * ENNReal.ofReal ((χ / J) * weight i) =
      ENNReal.ofReal (χ * weight i) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg J)]
    congr 1
    have hJne : (J : ℝ) ≠ 0 := by positivity
    field_simp
  calc (∑ a : Fin J, ∑ _b : Fin J, ENNReal.ofReal ((χ / J) * weight i) *
          π {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * tag i + (a : ℕ)})
      = ∑ a : Fin J, ENNReal.ofReal (χ * weight i) *
          π {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * tag i + (a : ℕ)} := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, hcancel]
    _ = ENNReal.ofReal (χ * weight i) *
        (∑ a : Fin J, π {x : ℝ | ⌊x / (χ / J)⌋ = (J : ℤ) * tag i + (a : ℕ)}) :=
      (Finset.mul_sum ..).symm
    _ = _ := by rw [sum_aligned_palette π χ hJ]

end Submission.Obl.k4_narrow_projected_row_parents
