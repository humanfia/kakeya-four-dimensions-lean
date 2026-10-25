import Mathlib
import ChallengeDeps

open scoped BigOperators

namespace Submission.Obl.k4_scalar_lift_plank

/-- The error in replacing a real number by its floor is at most one. -/
theorem abs_floor_sub (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  rw [abs_le]
  constructor
  · have := Int.lt_floor_add_one x
    linarith
  · have := Int.floor_le x
    linarith

/-- A uniform integer interval containing the floor of a bounded coordinate. -/
noncomputable def coordinateBins (p M : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈2 * M / p⌉) ⌈2 * M / p⌉

noncomputable def errorBins (M : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈10 * M⌉) ⌈10 * M⌉

/-- A shear sends each scalar cell into this finite family of planar cells. -/
noncomputable def liftedCells (p M : ℝ) (F : Finset (ℤ × ℤ)) :
    Finset (ℤ × (Fin 2 → ℤ)) :=
  ((F ×ˢ coordinateBins p M) ×ˢ errorBins M).image
    (fun z => (z.1.1.1, ![z.1.1.2 - ⌊p * (z.1.1.1 : ℝ) * (z.1.2 : ℝ)⌋ + z.2,
      z.1.2]))

theorem mem_coordinateBins {p M y : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : 1 ≤ M) (hy : |y| ≤ M) : ⌊y / p⌋ ∈ coordinateBins p M := by
  have hMp : 1 ≤ M / p := (le_div_iff₀ hp).2 (by simpa using hp1.trans hM)
  have hf := abs_floor_sub (y / p)
  have hy' : |y / p| ≤ M / p := by
    rw [abs_div, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hy hp.le
  have hceil : 2 * M / p ≤ (⌈2 * M / p⌉ : ℝ) := Int.le_ceil _
  have habs : |(⌊y / p⌋ : ℝ)| ≤ (⌈2 * M / p⌉ : ℝ) := by
    calc
      _ ≤ |(⌊y / p⌋ : ℝ) - y / p| + |y / p| := by
        simpa using abs_add_le ((⌊y / p⌋ : ℝ) - y / p) (y / p)
      _ ≤ 1 + M / p := add_le_add hf hy'
      _ ≤ _ := by linarith [show 2 * M / p = 2 * (M / p) by ring]
  rw [coordinateBins, Finset.mem_Icc]
  have h := abs_le.mp habs
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end Submission.Obl.k4_scalar_lift_plank

namespace Submission.Obl.k4_scalar_lift_plank

theorem mem_liftedCells {p M t x y : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : 1 ≤ M) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ M)
    (F : Finset (ℤ × ℤ)) (hF : (⌊t / p⌋, ⌊(x + t * y) / p⌋) ∈ F) :
    (⌊t / p⌋, ![⌊x / p⌋, ⌊y / p⌋]) ∈ liftedCells p M F := by
  classical
  let j : ℤ := ⌊t / p⌋
  let k : ℤ := ⌊(x + t * y) / p⌋
  let m : ℤ := ⌊y / p⌋
  let r : ℤ := ⌊x / p⌋ - (k - ⌊p * (j : ℝ) * (m : ℝ)⌋)
  have hm : m ∈ coordinateBins p M := mem_coordinateBins hp hp1 hM hy
  have hr : r ∈ errorBins M := by
    have hmf := abs_floor_sub (y / p)
    have hxf := abs_floor_sub (x / p)
    have hqf := abs_floor_sub ((x + t * y) / p)
    have hjf := abs_floor_sub (t / p)
    have hcf := abs_floor_sub (p * (j : ℝ) * (m : ℝ))
    have hy' : |y / p| ≤ M / p := by
      rw [abs_div, abs_of_pos hp]
      exact div_le_div_of_nonneg_right hy hp.le
    have hmabs : |(m : ℝ)| ≤ M / p + 1 := by
      calc
        _ ≤ |(m : ℝ) - y / p| + |y / p| := by
          simpa using abs_add_le ((m : ℝ) - y / p) (y / p)
        _ ≤ 1 + M / p := add_le_add hmf hy'
        _ = _ := by ring
    have htj : |t - p * (j : ℝ)| ≤ p := by
      calc
        _ = |p * ((j : ℝ) - t / p)| := by
          rw [abs_sub_comm]
          congr 1
          field_simp
        _ = p * |(j : ℝ) - t / p| := by rw [abs_mul, abs_of_pos hp]
        _ ≤ p * 1 := mul_le_mul_of_nonneg_left hjf hp.le
        _ = p := mul_one p
    have htm : |(t - p * (j : ℝ)) * (m : ℝ)| ≤ M + p := by
      rw [abs_mul]
      calc
        _ ≤ p * (M / p + 1) := mul_le_mul htj hmabs (abs_nonneg _) hp.le
        _ = M + p := by field_simp
    have hty : |t * ((m : ℝ) - y / p)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul ht.2 hmf (abs_nonneg _) (by norm_num)).trans (by norm_num)
    have hrid : (r : ℝ) =
        ((⌊x / p⌋ : ℝ) - x / p) +
        (((x + t * y) / p) - (k : ℝ)) +
        t * ((m : ℝ) - y / p) -
        (t - p * (j : ℝ)) * (m : ℝ) +
        ((⌊p * (j : ℝ) * (m : ℝ)⌋ : ℝ) - p * (j : ℝ) * (m : ℝ)) := by
      dsimp [r]
      push_cast
      ring
    have hrabs : |(r : ℝ)| ≤ M + p + 4 := by
      rw [hrid]
      calc
        _ ≤ |((⌊x / p⌋ : ℝ) - x / p)| +
            |((x + t * y) / p) - (k : ℝ)| +
            |t * ((m : ℝ) - y / p)| +
            |(t - p * (j : ℝ)) * (m : ℝ)| +
            |(⌊p * (j : ℝ) * (m : ℝ)⌋ : ℝ) - p * (j : ℝ) * (m : ℝ)| := by
          grw [abs_add_le, abs_sub, abs_add_le, abs_add_le]
        _ ≤ 1 + 1 + 1 + (M + p) + 1 := by
          gcongr
          simpa only [abs_sub_comm] using hqf
        _ = _ := by ring
    have hceil := Int.le_ceil (10 * M)
    have hh : |(r : ℝ)| ≤ (⌈10 * M⌉ : ℝ) := hrabs.trans (by linarith)
    rw [errorBins, Finset.mem_Icc]
    constructor
    · exact_mod_cast (abs_le.mp hh).1
    · exact_mod_cast (abs_le.mp hh).2
  apply Finset.mem_image.mpr
  refine ⟨(((j, k), m), r), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hF, hm⟩, hr⟩, ?_⟩
  dsimp [j, k, m, r]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp <;> omega

end Submission.Obl.k4_scalar_lift_plank

namespace Submission.Obl.k4_scalar_lift_plank

theorem card_ceil_interval_le {L : ℝ} (hL : 0 ≤ L) :
    ((Finset.Icc (-⌈L⌉) ⌈L⌉).card : ℝ) ≤ 2 * L + 3 := by
  have hc : (0 : ℤ) ≤ ⌈L⌉ := by exact_mod_cast hL.trans (Int.le_ceil L)
  have heq := Int.card_Icc_of_le (-⌈L⌉) ⌈L⌉ (show -⌈L⌉ ≤ ⌈L⌉ + 1 by omega)
  have heq' : ((Finset.Icc (-⌈L⌉) ⌈L⌉).card : ℝ) = 2 * (⌈L⌉ : ℝ) + 1 := by
    exact_mod_cast (by omega : ((Finset.Icc (-⌈L⌉) ⌈L⌉).card : ℤ) = 2 * ⌈L⌉ + 1)
  rw [heq']
  have := Int.ceil_lt_add_one L
  linarith

theorem card_coordinateBins_le {p M : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : 1 ≤ M) : ((coordinateBins p M).card : ℝ) ≤ 7 * M / p := by
  have hMp : 1 ≤ M / p := (le_div_iff₀ hp).2 (by simpa using hp1.trans hM)
  have h := card_ceil_interval_le (show 0 ≤ 2 * M / p by positivity)
  dsimp [coordinateBins]
  linarith [show 2 * (2 * M / p) = 4 * (M / p) by ring,
    show 7 * M / p = 7 * (M / p) by ring]

theorem card_errorBins_le {M : ℝ} (hM : 1 ≤ M) :
    ((errorBins M).card : ℝ) ≤ 23 * M := by
  have := card_ceil_interval_le (show 0 ≤ 10 * M by positivity)
  dsimp [errorBins]
  linarith

theorem card_liftedCells_le {p M : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : 1 ≤ M) (F : Finset (ℤ × ℤ)) :
    ((liftedCells p M F).card : ℝ) ≤ 200 * (F.card : ℝ) * M ^ 2 / p := by
  have hcard : ((liftedCells p M F).card : ℝ) ≤
      (F.card : ℝ) * ((coordinateBins p M).card : ℝ) * ((errorBins M).card : ℝ) := by
    have := Finset.card_image_le (s := (F ×ˢ coordinateBins p M) ×ˢ errorBins M)
      (f := fun z => (z.1.1.1,
        ![z.1.1.2 - ⌊p * (z.1.1.1 : ℝ) * (z.1.2 : ℝ)⌋ + z.2, z.1.2]))
    simpa only [liftedCells, Finset.card_product, Nat.cast_mul] using
      (Nat.cast_le (α := ℝ)).mpr this
  calc
    _ ≤ (F.card : ℝ) * ((coordinateBins p M).card : ℝ) * ((errorBins M).card : ℝ) := hcard
    _ ≤ (F.card : ℝ) * (7 * M / p) * (23 * M) := by
      gcongr
      · exact card_coordinateBins_le hp hp1 hM
      · exact card_errorBins_le hM
    _ = 161 * (F.card : ℝ) * M ^ 2 / p := by ring
    _ ≤ _ := by gcongr <;> norm_num

end Submission.Obl.k4_scalar_lift_plank
