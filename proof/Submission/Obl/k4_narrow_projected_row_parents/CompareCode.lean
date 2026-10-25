import Mathlib

/-!
# Comparison codes and their menus

The common domains of the comparison of true and projected labels (paper,
Lemma 8.3) are indexed by a code recording, for an incidence `(b, t)`:
the time bin, the major velocity and intercept bins, the transverse velocity
bin, and the transverse position bin at the left end of the time bin.
This is the same code as `CommonDomain.code` of o200 (session x0934).

If the incidence is only known up to explicit radii (a centre and a radius
for time, major velocity, major intercept, transverse velocity and transverse
position), its code lies in an explicit finite menu, whose size is bounded by
the ratios of the radii to the bin widths.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open Set

noncomputable section

/-- The comparison code of an incidence `(b, t)`: time bin (width `q`), major
velocity and intercept bins (width `χ`), transverse velocity bin (width `g`), and
transverse position bin (width `m`) at the left end of the time bin. -/
def ccode (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 5 → ℤ :=
  ![⌊t / q⌋, ⌊b 3 / χ⌋, ⌊b 0 / χ⌋, ⌊b 4 / g⌋,
    ⌊(b 1 + ((⌊t / q⌋ : ℤ) : ℝ) * q * b 4) / m⌋]

/-- The bins of width `δ` met by the points within `ρ` of `x`. -/
def binMenu (δ x ρ : ℝ) : Finset ℤ := Finset.Icc ⌊(x - ρ) / δ⌋ ⌊(x + ρ) / δ⌋

theorem floor_mem_binMenu {δ x ρ y : ℝ} (hδ : 0 < δ) (h : |y - x| ≤ ρ) :
    ⌊y / δ⌋ ∈ binMenu δ x ρ := by
  rw [abs_le] at h
  rw [binMenu, Finset.mem_Icc]
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le)

theorem card_binMenu_le {δ x ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    ((binMenu δ x ρ).card : ℝ) ≤ 2 * ρ / δ + 2 := by
  rw [binMenu, Int.card_Icc]
  have h1 := Int.floor_le ((x + ρ) / δ)
  have h2 := Int.lt_floor_add_one ((x - ρ) / δ)
  have hsub : (x + ρ) / δ - (x - ρ) / δ = 2 * ρ / δ := by ring
  have hle : ((⌊(x + ρ) / δ⌋ + 1 - ⌊(x - ρ) / δ⌋ : ℤ) : ℝ) ≤ 2 * ρ / δ + 2 := by
    push_cast
    linarith
  have hnn : (0 : ℝ) ≤ 2 * ρ / δ + 2 := by positivity
  rcases le_or_gt 0 (⌊(x + ρ) / δ⌋ + 1 - ⌊(x - ρ) / δ⌋) with h | h
  · rw [show ((Int.toNat (⌊(x + ρ) / δ⌋ + 1 - ⌊(x - ρ) / δ⌋) : ℕ) : ℝ) =
        ((⌊(x + ρ) / δ⌋ + 1 - ⌊(x - ρ) / δ⌋ : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]]
    exact hle
  · rw [Int.toNat_of_nonpos h.le]
    simpa using hnn

/-- The time component of the code. -/
theorem ccode_zero (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ccode q χ g m b t 0 = ⌊t / q⌋ := rfl
theorem ccode_one (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ccode q χ g m b t 1 = ⌊b 3 / χ⌋ := rfl
theorem ccode_two (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ccode q χ g m b t 2 = ⌊b 0 / χ⌋ := rfl
theorem ccode_three (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ccode q χ g m b t 3 = ⌊b 4 / g⌋ :=
  rfl
theorem ccode_four (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    ccode q χ g m b t 4 = ⌊(b 1 + ((⌊t / q⌋ : ℤ) : ℝ) * q * b 4) / m⌋ := rfl

/-- The code menu of an incidence known up to the given radii: time `tc ± ρt`,
major velocity `v3 ± ρ3`, major intercept `v0 ± ρ0`, transverse velocity
`v4 ± ρ4` (with `|b 4| ≤ B4`), transverse position `y ± ρy` at the actual time. -/
def codeMenu (q χ g m tc ρt v3 ρ3 v0 ρ0 v4 ρ4 B4 y ρy : ℝ) : Finset (Fin 5 → ℤ) :=
  (binMenu q tc ρt).biUnion fun n =>
    ((binMenu χ v3 ρ3 ×ˢ binMenu χ v0 ρ0) ×ˢ
      (binMenu g v4 ρ4 ×ˢ binMenu m (y - (tc - (n : ℝ) * q) * v4)
        (ρy + ρt * B4 + (ρt + q) * ρ4))).image
      fun x => ![n, x.1.1, x.1.2, x.2.1, x.2.2]

theorem ccode_mem_codeMenu {q χ g m tc ρt v3 ρ3 v0 ρ0 v4 ρ4 B4 y ρy : ℝ}
    (hq : 0 < q) (hχ : 0 < χ) (hg : 0 < g) (hm : 0 < m)
    {b : Fin 6 → ℝ} {t : ℝ}
    (ht : |t - tc| ≤ ρt) (h3 : |b 3 - v3| ≤ ρ3) (h0 : |b 0 - v0| ≤ ρ0)
    (h4 : |b 4 - v4| ≤ ρ4) (hB4 : |b 4| ≤ B4)
    (hy : |(b 1 + t * b 4) - y| ≤ ρy) :
    ccode q χ g m b t ∈ codeMenu q χ g m tc ρt v3 ρ3 v0 ρ0 v4 ρ4 B4 y ρy := by
  rw [codeMenu, Finset.mem_biUnion]
  refine ⟨⌊t / q⌋, floor_mem_binMenu hq ht, ?_⟩
  rw [Finset.mem_image]
  refine ⟨((⌊b 3 / χ⌋, ⌊b 0 / χ⌋), (⌊b 4 / g⌋,
    ⌊(b 1 + ((⌊t / q⌋ : ℤ) : ℝ) * q * b 4) / m⌋)), ?_, ?_⟩
  · simp only [Finset.mem_product]
    refine ⟨⟨floor_mem_binMenu hχ h3, floor_mem_binMenu hχ h0⟩,
      floor_mem_binMenu hg h4, floor_mem_binMenu hm ?_⟩
    -- the transverse position at the left end of the time bin
    set n : ℤ := ⌊t / q⌋
    have hn1 : (n : ℝ) * q ≤ t := by
      have := Int.floor_le (t / q)
      rwa [le_div_iff₀ hq] at this
    have hn2 : t < ((n : ℝ) + 1) * q := by
      have := Int.lt_floor_add_one (t / q)
      rwa [div_lt_iff₀ hq] at this
    have hd : |tc - (n : ℝ) * q| ≤ ρt + q := by
      rw [abs_le] at ht ⊢
      constructor <;> nlinarith
    have hid : b 1 + (n : ℝ) * q * b 4 - (y - (tc - (n : ℝ) * q) * v4) =
        ((b 1 + t * b 4) - y) - (t - tc) * b 4 - (tc - (n : ℝ) * q) * (b 4 - v4) := by ring
    rw [hid]
    have e1 : |(t - tc) * b 4| ≤ ρt * B4 := by
      rw [abs_mul]; exact mul_le_mul ht hB4 (abs_nonneg _) (by linarith [abs_nonneg (t - tc)])
    have e2 : |(tc - (n : ℝ) * q) * (b 4 - v4)| ≤ (ρt + q) * ρ4 := by
      rw [abs_mul]; exact mul_le_mul hd h4 (abs_nonneg _) (by linarith [abs_nonneg (t - tc)])
    calc |((b 1 + t * b 4) - y) - (t - tc) * b 4 - (tc - (n : ℝ) * q) * (b 4 - v4)|
        ≤ |(b 1 + t * b 4) - y| + |(t - tc) * b 4| + |(tc - (n : ℝ) * q) * (b 4 - v4)| := by
          have := abs_sub (((b 1 + t * b 4) - y) - (t - tc) * b 4) ((tc - (n : ℝ) * q) * (b 4 - v4))
          have := abs_sub ((b 1 + t * b 4) - y) ((t - tc) * b 4)
          linarith
      _ ≤ ρy + ρt * B4 + (ρt + q) * ρ4 := by linarith
  · funext i
    fin_cases i <;> rfl

theorem card_codeMenu_le {q χ g m tc ρt v3 ρ3 v0 ρ0 v4 ρ4 B4 y ρy : ℝ}
    (hq : 0 < q) (hχ : 0 < χ) (hg : 0 < g) (hm : 0 < m)
    (hρt : 0 ≤ ρt) (hρ3 : 0 ≤ ρ3) (hρ0 : 0 ≤ ρ0) (hρ4 : 0 ≤ ρ4) (hB4 : 0 ≤ B4)
    (hρy : 0 ≤ ρy) :
    ((codeMenu q χ g m tc ρt v3 ρ3 v0 ρ0 v4 ρ4 B4 y ρy).card : ℝ) ≤
      (2 * ρt / q + 2) * ((2 * ρ3 / χ + 2) * (2 * ρ0 / χ + 2) *
        ((2 * ρ4 / g + 2) * (2 * (ρy + ρt * B4 + (ρt + q) * ρ4) / m + 2))) := by
  rw [codeMenu]
  refine (Nat.cast_le.mpr (Finset.card_biUnion_le)).trans ?_
  push_cast
  calc (∑ n ∈ binMenu q tc ρt, (((binMenu χ v3 ρ3 ×ˢ binMenu χ v0 ρ0) ×ˢ
          (binMenu g v4 ρ4 ×ˢ binMenu m (y - (tc - (n : ℝ) * q) * v4)
            (ρy + ρt * B4 + (ρt + q) * ρ4))).image
          fun x => ![n, x.1.1, x.1.2, x.2.1, x.2.2]).card : ℝ)
      ≤ ∑ _n ∈ binMenu q tc ρt, ((2 * ρ3 / χ + 2) * (2 * ρ0 / χ + 2) *
        ((2 * ρ4 / g + 2) * (2 * (ρy + ρt * B4 + (ρt + q) * ρ4) / m + 2))) := by
        refine Finset.sum_le_sum fun n _ => ?_
        refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
        rw [Finset.card_product, Finset.card_product, Finset.card_product]
        push_cast
        have a1 := card_binMenu_le (x := v3) hχ hρ3
        have a2 := card_binMenu_le (x := v0) hχ hρ0
        have a3 := card_binMenu_le (x := v4) hg hρ4
        have a4 := card_binMenu_le (x := y - (tc - (n : ℝ) * q) * v4) hm
          (show 0 ≤ ρy + ρt * B4 + (ρt + q) * ρ4 by positivity)
        have p1 : (0 : ℝ) ≤ ((binMenu χ v3 ρ3).card : ℝ) := Nat.cast_nonneg _
        have p2 : (0 : ℝ) ≤ ((binMenu χ v0 ρ0).card : ℝ) := Nat.cast_nonneg _
        have p3 : (0 : ℝ) ≤ ((binMenu g v4 ρ4).card : ℝ) := Nat.cast_nonneg _
        have p4 : (0 : ℝ) ≤ ((binMenu m (y - (tc - (n : ℝ) * q) * v4)
          (ρy + ρt * B4 + (ρt + q) * ρ4)).card : ℝ) := Nat.cast_nonneg _
        gcongr
    _ = ((binMenu q tc ρt).card : ℝ) * ((2 * ρ3 / χ + 2) * (2 * ρ0 / χ + 2) *
        ((2 * ρ4 / g + 2) * (2 * (ρy + ρt * B4 + (ρt + q) * ρ4) / m + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        exact card_binMenu_le hq hρt

end

end Submission.Obl.k4_narrow_projected_row_parents
