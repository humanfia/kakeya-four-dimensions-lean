import Submission.Obl.k4_raw_localized_native_systems.Choice

namespace Submission.Obl.k4_raw_localized_native_systems

/-- The concrete source choices simultaneously pay later thinness, the
relative width gain of four, and the angular extraction error. -/
theorem choice_sequence_bounds {kr S η χ w : ℝ}
    (hkr0 : 0 ≤ kr) (hkr1 : kr ≤ 1) (hS : 0 < S) (hη : 0 < η)
    (hχ : 0 < χ) (hw : 0 < w) {r : ℕ → ℝ}
    (hr : ∀ i, i < 2 → |r i - sdOf kr S η χ i| ≤ epsOf kr S η χ ∧
      0 < r i ∧ r i ≤ sdOf kr S η χ i) :
    sExp kr S η ≤ r 1 ∧ sExp kr S η ≤ r 1 - r 0 ∧
    kr * sdOf kr S η χ 0 + epsOf kr S η χ ≤ 1 ∧
    w + 3 * angU η + 1 <
      wOf kr S η w * r 1 - 2 * (tolOf kr S η χ + 2 * tolOf kr S η χ) - tolOf kr S η χ ∧
    2 * tolOf kr S η χ + 4 + 2 * (kr * sdOf kr S η χ 0 + epsOf kr S η χ) +
      (1 / 16 : ℝ) + (3 * angU η + 1) ≤
      wOf kr S η w * (r 1 - r 0) - 2 * (tolOf kr S η χ + 2 * tolOf kr S η χ) ∧
    3 * (S * angU η / 100) + 2 * (kr * sdOf kr S η χ 1 + epsOf kr S η χ) + r 1 <
      S * angU η := by
  have hs := sExp_pos hkr0 hS hη
  have hs1 : sExp kr S η < 1 := sExp_lt_one
  have hu := angU_pos hη
  have ht := laterDepth_pos hkr0 hS hη
  have hν := nuOf_pos hkr0 hS hη hχ
  have hνs : nuOf kr S η χ ≤ sExp kr S η / 8 := nuOf_le_s
  have hr0 := hr 0 (by omega)
  have hr1 := hr 1 (by omega)
  have hr1lo := (abs_le.mp hr1.1).1
  rw [sdOf_zero] at hr0
  rw [sdOf_one] at hr1 hr1lo
  have hts : laterDepth kr S η = 2 * sExp kr S η := by unfold sExp; ring
  have hr1s : sExp kr S η ≤ r 1 := by
    dsimp only [epsOf] at hr1lo
    linarith only [hr1lo, hts, hνs, hs]
  have hrs : sExp kr S η ≤ r 1 - r 0 := by
    dsimp only [epsOf] at hr1lo
    linarith only [hr1lo, hr0.2.2, hts, hν]
  have hsd0 := (sdOf_zero_pos (χ := χ) hkr0 hS hη).le
  have hmul0 : kr * sdOf kr S η χ 0 ≤ sdOf kr S η χ 0 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hkr1 hsd0
  have htime0 : kr * sdOf kr S η χ 0 + epsOf kr S η χ ≤ 1 := by
    rw [sdOf_zero] at hmul0
    simp only [sdOf_zero, epsOf]
    linarith only [hmul0, hs1, hν]
  have htol : tolOf kr S η χ ≤ 1 / 80 := by
    dsimp only [tolOf]
    linarith only [hνs, hs1]
  have hwp := wOf_nonneg hkr0 hS hη hw.le
  have hws : wOf kr S η w * sExp kr S η = 2 * (w + 20 + 2 * kr + 3 * angU η) := by
    unfold wOf
    field_simp
  have hwr := mul_le_mul_of_nonneg_left hr1s hwp
  have hwgap := mul_le_mul_of_nonneg_left hrs hwp
  rw [hws] at hwr hwgap
  have hthin : w + 3 * angU η + 1 <
      wOf kr S η w * r 1 - 2 * (tolOf kr S η χ + 2 * tolOf kr S η χ) - tolOf kr S η χ := by
    linarith only [hwr, htol, hw, hkr0, hu]
  have hrel : 2 * tolOf kr S η χ + 4 + 2 * (kr * sdOf kr S η χ 0 + epsOf kr S η χ) +
      (1 / 16 : ℝ) + (3 * angU η + 1) ≤
      wOf kr S η w * (r 1 - r 0) - 2 * (tolOf kr S η χ + 2 * tolOf kr S η χ) := by
    linarith only [hwgap, htol, htime0, hw, hkr0, hu]
  have hbad := laterDepth_bad (S := S) (η := η) hkr0
  have htSu : laterDepth kr S η ≤ S * angU η / 8 := by
    have hn := mul_nonneg hkr0 ht.le
    nlinarith only [hbad, hn]
  have hνSu : nuOf kr S η χ ≤ S * angU η / 128 := by
    linarith only [hνs, hts, htSu]
  have hgap : 3 * (S * angU η / 100) +
      2 * (kr * sdOf kr S η χ 1 + epsOf kr S η χ) + r 1 < S * angU η := by
    simp only [sdOf_one, epsOf]
    have hSu : 0 < S * angU η := mul_pos hS hu
    nlinarith only [hbad, hνSu, hr1.2.2, hSu]
  exact ⟨hr1s, hrs, htime0, hthin, hrel, hgap⟩

end Submission.Obl.k4_raw_localized_native_systems
