import Submission.Obl.k4_finite_positive_mixed_cover_realization.Interface

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

/-- A finite fine grid has a predecessor within one mesh of any interior depth. -/
theorem FineGrid.predecessor {m : ℕ} {s : ℕ → ℝ} {gain ρ y : ℝ}
    (hs : FineGrid m s gain ρ) (hmesh : 0 ≤ ρ * gain)
    (hy₀ : s 0 ≤ y) (hy₁ : y ≤ 1) :
    ∃ j, j < m ∧ s j ≤ y ∧ y ≤ s j + ρ * gain := by
  classical
  let I := (Finset.range m).filter fun j => s j ≤ y
  have hI : I.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs.1.1, hy₀⟩⟩
  let j := I.max' hI
  have hjI : j ∈ I := Finset.max'_mem I hI
  obtain ⟨hj, hjy⟩ := Finset.mem_filter.mp hjI
  have hjm : j < m := Finset.mem_range.mp hj
  refine ⟨j, hjm, hjy, ?_⟩
  by_cases hnext : j + 1 < m
  · have hynext : y < s (j + 1) := by
      by_contra h
      have hnI : j + 1 ∈ I := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hnext, le_of_not_gt h⟩
      have hn := Finset.le_max' I (j + 1) hnI
      change j + 1 ≤ j at hn
      omega
    have hgap := hs.2.2 j hnext
    linarith
  · have hjlast : j = m - 1 := by omega
    rw [hjlast, hs.1.2.2.2]
    linarith

/-- Every fine-grid node lies in the unit interval. -/
theorem FineGrid.bounds {m : ℕ} {s : ℕ → ℝ} {gain ρ : ℝ}
    (hs : FineGrid m s gain ρ) {i : ℕ} (hi : i < m) : 0 < s i ∧ s i ≤ 1 := by
  have hmono : StrictMonoOn s (Set.Iio m) := by
    apply strictMonoOn_of_lt_add_one (Set.ordConnected_Iio)
    intro a _ ha hnext
    exact hs.1.2.2.1 a hnext
  constructor
  · exact hs.1.2.1.trans_le (hmono.monotoneOn hs.1.1 hi (Nat.zero_le _))
  · have hm : m - 1 < m := by omega
    simpa only [hs.1.2.2.2] using hmono.monotoneOn hi hm (show i ≤ m - 1 by omega)

/-- Interior room for a cover gives a deeper true grid node, within one mesh
of its candidate depth. The estimates use the original depth tolerance. -/
theorem FineGrid.deeper {m : ℕ} {s r : ℕ → ℝ} {gain ρ δ₀ L h : ℝ}
    (hs : FineGrid m s gain ρ) (hL : 0 < L) (hgain : 0 < gain)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hδ : δ₀ ≤ ρ * gain)
    {i : ℕ} (hi : i < m) (hh : gain ≤ h)
    (hdepth : |r i - s i * L| ≤ δ₀ * L) (hroom : r i + 2 * h * L ≤ L) :
    ∃ j, j < m ∧ s i + h - ρ * gain ≤ s j ∧ s j ≤ s i + h := by
  have hh₀ : 0 < h := hgain.trans_le hh
  have hδh : δ₀ ≤ h := hδ.trans ((mul_le_of_le_one_left hgain.le hρ₁).trans hh)
  have hlow : s i * L - δ₀ * L ≤ r i := by
    have := (abs_le.mp hdepth).1
    linarith
  have hy : s i + h ≤ 1 := by nlinarith
  have hsi : s 0 ≤ s i := by
    have hmono : StrictMonoOn s (Set.Iio m) := by
      apply strictMonoOn_of_lt_add_one (Set.ordConnected_Iio)
      intro a _ ha hnext
      exact hs.1.2.2.1 a hnext
    exact hmono.monotoneOn hs.1.1 hi (Nat.zero_le _)
  obtain ⟨j, hj, hjy, hyj⟩ := hs.predecessor (mul_nonneg hρ hgain.le)
    (show s 0 ≤ s i + h by linarith) hy
  exact ⟨j, hj, by linarith, hjy⟩

/-- Positive cumulative narrowness gives a fixed power gain between the old
node and the deeper true node, after both depth errors are paid. -/
theorem narrowness_gap {ℓ ρ gain h L δ₀ si sj wi wj : ℝ}
    (hℓ : 0 ≤ ℓ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1 / 4)
    (hρℓ : 16 * ρ ≤ ℓ) (hgain : 0 ≤ gain) (hh : gain ≤ h)
    (hL : 0 ≤ L) (hδ : δ₀ ≤ ρ * gain)
    (hgap : si + h - ρ * gain ≤ sj)
    (hwi : |wi - ℓ * si * L| ≤ δ₀ * L)
    (hwj : |wj - ℓ * sj * L| ≤ δ₀ * L) :
    ℓ * h * L / 2 ≤ wj - wi - 2 * δ₀ * L := by
  have hh₀ : 0 ≤ h := hgain.trans hh
  have hρh : ρ * gain ≤ ρ * h := mul_le_mul_of_nonneg_left hh hρ
  have hδh : δ₀ * L ≤ ρ * h * L :=
    mul_le_mul_of_nonneg_right (hδ.trans hρh) hL
  have hgap' : (1 - ρ) * h ≤ sj - si := by nlinarith
  have hsmall : ℓ / 2 + 4 * ρ ≤ ℓ * (1 - ρ) := by nlinarith
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hh₀ hL)
  have hgap'' := mul_le_mul_of_nonneg_left hgap' (mul_nonneg hℓ hL)
  obtain ⟨hwi₁, hwi₂⟩ := abs_le.mp hwi
  obtain ⟨hwj₁, hwj₂⟩ := abs_le.mp hwj
  nlinarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization
