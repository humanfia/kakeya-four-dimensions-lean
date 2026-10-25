/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.NormingCoordinates

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

theorem abs_splitHeadCoordinates_symm_apply_le (n : ℕ) (z : (Fin n → ℝ) × ℝ)
    (j : Fin (n + 1)) : |(splitHeadCoordinates n).symm z j| ≤ ‖z‖ := by
  change |(splitHeadCoordinates n).symm (z.1,z.2) j| ≤ ‖z‖
  rw [splitHeadCoordinates_symm_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero, ← Real.norm_eq_abs] using norm_snd_le z
  · simpa only [Fin.cons_succ, ← Real.norm_eq_abs] using
      (norm_le_pi_norm z.1 i).trans (norm_fst_le z)

theorem splitHeadCoordinates_symm_sub (n : ℕ) (x y : (Fin n → ℝ) × ℝ) :
    (splitHeadCoordinates n).symm (x-y) =
      (splitHeadCoordinates n).symm x - (splitHeadCoordinates n).symm y := by
  funext j
  change (splitHeadCoordinates n).symm (x.1-y.1,x.2-y.2) j =
    (splitHeadCoordinates n).symm (x.1,x.2) j - (splitHeadCoordinates n).symm (y.1,y.2) j
  simp only [splitHeadCoordinates_symm_apply]
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- A finite rectangular physical support, with any unused-control widths,
has a measurable enlarged target and an explicit volume bound. Perturbing
by at most each original half-width only doubles the half-widths. -/
theorem exists_rectangular_target_enlargement_of_coordinate_error {ι : Type*} (n : ℕ)
    (I : Finset ι) (c : ι → Fin (n + 1) → ℝ) (r : Fin (n + 1) → ℝ)
    (T : Set ((Fin n → ℝ) × ℝ)) (η : Fin (n+1) → ℝ) (hηr : ∀ j, η j ≤ r j)
    (hcover : ∀ y ∈ T, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates n).symm y j - c i j| ≤ r j) :
    ∃ Tplus : Set ((Fin n → ℝ) × ℝ), MeasurableSet Tplus ∧
      (∀ x y, y ∈ T → (∀ j, |(splitHeadCoordinates n).symm x j-
        (splitHeadCoordinates n).symm y j| ≤ η j) → x ∈ Tplus) ∧
      volume Tplus ≤ (I.card : ENNReal) * ∏ j, ENNReal.ofReal (4 * r j) := by
  classical
  let e := splitHeadCoordinates n
  let box (i : ι) : Set (Fin (n + 1) → ℝ) :=
    Icc (fun j => c i j - 2 * r j) (fun j => c i j + 2 * r j)
  let U : Set (Fin (n + 1) → ℝ) := ⋃ i ∈ I, box i
  have hUm : MeasurableSet U := by
    apply Finset.measurableSet_biUnion
    intro i _
    exact measurableSet_Icc
  refine ⟨e '' U, e.measurableSet_image.mpr hUm, ?_, ?_⟩
  · intro x y hy hxy
    obtain ⟨i, hi, hiy⟩ := hcover y hy
    have hpoint (j : Fin (n + 1)) : |e.symm x j - c i j| ≤ 2 * r j := by
      calc
        _ = |(e.symm x j - e.symm y j) + (e.symm y j - c i j)| := by congr 1; ring
        _ ≤ |e.symm x j - e.symm y j| + |e.symm y j - c i j| := abs_add_le _ _
        _ ≤ η j + r j := add_le_add (hxy j) (hiy j)
        _ ≤ _ := by linarith [hηr j]
    have hxu : e.symm x ∈ U := by
      apply Set.mem_iUnion₂.mpr
      refine ⟨i, hi, ?_⟩
      constructor <;> intro j
      · have h := (abs_le.mp (hpoint j)).1
        change c i j - 2 * r j ≤ e.symm x j
        linarith
      · have h := (abs_le.mp (hpoint j)).2
        change e.symm x j ≤ c i j + 2 * r j
        linarith
    exact ⟨e.symm x, hxu, e.apply_symm_apply x⟩
  · have hboxvol (i : ι) : volume (box i) = ∏ j, ENNReal.ofReal (4 * r j) := by
      change volume (Icc (fun j => c i j - 2 * r j)
        (fun j => c i j + 2 * r j)) = _
      rw [Real.volume_Icc_pi]
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      ring
    have hvolimage : volume (e '' U) = volume U := by
      calc
        _ = volume (e ⁻¹' (e '' U)) :=
          ((splitHeadCoordinates_measurePreserving n).measure_preimage
            (e.measurableSet_image.mpr hUm).nullMeasurableSet).symm
        _ = _ := by congr 1; ext u; simp
    rw [hvolimage]
    calc
      _ ≤ ∑ i ∈ I, volume (box i) := measure_biUnion_finset_le _ _
      _ = ∑ _i ∈ I, ∏ j, ENNReal.ofReal (4 * r j) :=
        Finset.sum_congr rfl (fun i _ => hboxvol i)
      _ = _ := by simp


/-- A finite rectangular physical support, with any unused-control widths,
has a measurable enlarged target and an explicit volume bound. Perturbing
by at most each original half-width only doubles the half-widths. -/
theorem exists_rectangular_target_enlargement {ι : Type*} (n : ℕ)
    (I : Finset ι) (c : ι → Fin (n + 1) → ℝ) (r : Fin (n + 1) → ℝ)
    (T : Set ((Fin n → ℝ) × ℝ)) (η : ℝ) (hη : 0 ≤ η) (hηr : ∀ j, η ≤ r j)
    (hcover : ∀ y ∈ T, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates n).symm y j - c i j| ≤ r j) :
    ∃ Tplus : Set ((Fin n → ℝ) × ℝ), MeasurableSet Tplus ∧
      (∀ x y, y ∈ T → ‖x-y‖ ≤ η → x ∈ Tplus) ∧
      volume Tplus ≤ (I.card : ENNReal) * ∏ j, ENNReal.ofReal (4 * r j) := by
  obtain ⟨Tplus,hTplus,henlarge,hvol⟩ := exists_rectangular_target_enlargement_of_coordinate_error
    n I c r T (fun _ => η) hηr hcover
  refine ⟨Tplus,hTplus,?_,hvol⟩
  intro x y hy hxy
  apply henlarge x y hy
  intro j
  change |((splitHeadCoordinates n).symm x-(splitHeadCoordinates n).symm y) j| ≤ η
  rw [← splitHeadCoordinates_symm_sub]
  exact (abs_splitHeadCoordinates_symm_apply_le n (x-y) j).trans hxy

end Submission.Lib.K4PolynomialNorming
