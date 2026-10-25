import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

theorem measurableSet_timeCell (J : ℕ) (z : Fin J) : MeasurableSet (timeCell J z) :=
  measurableSet_Ico

theorem timeCell_subset {J : ℕ} (hJ : 0 < J) (z : Fin J) :
    timeCell J z ⊆ Ico (0 : ℝ) 1 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  intro t ht
  have hz : (z : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast z.isLt
  exact ⟨le_trans (by positivity : 0 ≤ (z : ℝ) / (J : ℝ)) ht.1,
    lt_of_lt_of_le ht.2 ((div_le_iff₀ hJr).mpr (by simpa using hz))⟩

theorem timeCell_disjoint {J : ℕ} (hJ : 0 < J) :
    Pairwise (fun z z' : Fin J => Disjoint (timeCell J z) (timeCell J z')) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  intro z z' hne
  rw [Set.disjoint_left]
  intro t ht ht'
  have hzz : z.val + 1 ≤ z'.val ∨ z'.val + 1 ≤ z.val := by
    have : z.val ≠ z'.val := fun h => hne (Fin.ext h)
    omega
  rcases hzz with h | h
  · have hcast : (z : ℝ) + 1 ≤ (z' : ℝ) := by exact_mod_cast h
    have hdiv := div_le_div_of_nonneg_right hcast hJr.le
    exact (not_lt_of_ge (le_trans hdiv ht'.1)) ht.2
  · have hcast : (z' : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast h
    have hdiv := div_le_div_of_nonneg_right hcast hJr.le
    exact (not_lt_of_ge (le_trans hdiv ht.1)) ht'.2

theorem iUnion_timeCell {J : ℕ} (hJ : 0 < J) :
    (⋃ z : Fin J, timeCell J z) = Ico (0 : ℝ) 1 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  apply Set.Subset.antisymm
  · exact iUnion_subset (timeCell_subset hJ)
  · intro t ht
    have htJ : 0 ≤ t * (J : ℝ) := mul_nonneg ht.1 hJr.le
    have hfloor : ⌊t * (J : ℝ)⌋₊ < J :=
      (Nat.floor_lt htJ).mpr (by nlinarith [ht.2])
    let z : Fin J := ⟨⌊t * (J : ℝ)⌋₊, hfloor⟩
    apply mem_iUnion.mpr
    refine ⟨z, ?_, ?_⟩
    · exact (div_le_iff₀ hJr).mpr (Nat.floor_le htJ)
    · exact (lt_div_iff₀ hJr).mpr (Nat.lt_floor_add_one (t * (J : ℝ)))

theorem volume_timeCell {J : ℕ} (hJ : 0 < J) (z : Fin J) :
    volume (timeCell J z) = ENNReal.ofReal (1 / (J : ℝ)) := by
  rw [timeCell, Real.volume_Ico]
  congr 1
  ring

/-- The equal time partition is within a factor two of the coefficient noise scale. -/
theorem exists_time_mesh {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ J : ℕ, 1 ≤ J ∧ 1 ≤ (J : ℝ) * σ ∧ (J : ℝ) * σ ≤ 2 ∧
      (J : ℝ) ≤ 2 * σ⁻¹ := by
  let J := ⌈σ⁻¹⌉₊
  have hJpos : 0 < J := Nat.ceil_pos.mpr (inv_pos.mpr hσ)
  have hlow : σ⁻¹ ≤ (J : ℝ) := Nat.le_ceil _
  have hhigh : (J : ℝ) ≤ σ⁻¹ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  refine ⟨J, hJpos, ?_, ?_, ?_⟩
  · calc
      1 = σ⁻¹ * σ := (inv_mul_cancel₀ hσ.ne').symm
      _ ≤ (J : ℝ) * σ := mul_le_mul_of_nonneg_right hlow hσ.le
  · have := mul_le_mul_of_nonneg_right hhigh hσ.le
    rw [add_mul, inv_mul_cancel₀ hσ.ne', one_mul] at this
    linarith
  · have h1 : (1 : ℝ) ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ1
    linarith

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
