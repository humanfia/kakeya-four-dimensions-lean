import Submission.Obl.k4_prescribed_polynomial_visibility.VariationSeminorm

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory Function
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- Closed unit body of a seminorm. -/
def unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) := {v | V v ≤ 1}

theorem isClosed_unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    IsClosed (unitBody V) := isClosed_le (continuous_seminorm V) continuous_const

theorem measurableSet_unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    MeasurableSet (unitBody V) := (isClosed_unitBody V).measurableSet

theorem smul_unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (hr : 0 < r) : r • unitBody V = {v | V v ≤ r} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change V (r • y) ≤ r
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left hy hr.le
  · intro hx
    refine ⟨r⁻¹ • x, ?_, by simp [hr.ne']⟩
    change V (r⁻¹ • x) ≤ 1
    rw [map_smul_eq_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_eq_div,
      div_le_one hr]
    exact hx

theorem two_smul_unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    (2 : ℝ) • unitBody V = {v | V v ≤ 2} := smul_unitBody V 2 (by norm_num)

/-- Pointwise domination gives the corresponding dilation bound on unit-body volume. -/
theorem volume_unitBody_le_of_le_mul (V W : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (hr : 0 < r) (h : ∀ v, V v ≤ r * W v) :
    volume (unitBody W) ≤ ENNReal.ofReal (r ^ n) * volume (unitBody V) := by
  have hsub : unitBody W ⊆ r • unitBody V := by
    rw [smul_unitBody V r hr]
    intro x hx
    exact (h x).trans (by simpa using mul_le_mul_of_nonneg_left hx hr.le)
  calc
    volume (unitBody W) ≤ volume (r • unitBody V) := measure_mono hsub
    _ = ENNReal.ofReal (r ^ n) * volume (unitBody V) := by
      rw [Measure.addHaar_smul_of_nonneg volume hr.le, finrank_euclideanSpace_fin]

/-- A large value in one old-unit direction forces a smaller unit body after adding a seminorm.
The proof packs translates along this direction. -/
theorem volume_unitBody_add_le (V S : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (N : ℕ) (hN : 0 < N) (v : EuclideanSpace ℝ (Fin n))
    (hv : V v ≤ 1) (hSv : 3 * (N : ℝ) ≤ S v) :
    (N : ℝ≥0∞) * volume (unitBody (V + S)) ≤
      (2 : ℝ≥0∞) ^ n * volume (unitBody V) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let t : Fin N → ℝ := fun i => (i : ℝ) / (N : ℝ)
  let K := unitBody (V + S)
  let A : Fin N → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => (fun x => x + t i • v) '' K
  have hK : IsClosed K := isClosed_unitBody _
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    ((Homeomorph.addRight (t i • v)).isClosedMap K hK).measurableSet
  have hAd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hy
    have haS : S a ≤ 1 := by
      have hh : V a + S a ≤ 1 := ha
      linarith [apply_nonneg V a]
    have hbS : S b ≤ 1 := by
      have hh : V b + S b ≤ 1 := hb
      linarith [apply_nonneg V b]
    have heq : (((i : ℝ) - (j : ℝ)) / (N : ℝ)) • v = b - a := by
      have hh : a + t i • v = b + t j • v := hax.trans hbx.symm
      rw [sub_div, sub_smul]
      dsimp [t] at hh
      apply sub_eq_sub_iff_add_eq_add.mpr
      exact (add_comm _ _).trans hh
    have hd : |(i : ℝ) - (j : ℝ)| / (N : ℝ) * S v ≤ 2 := by
      have hh := map_sub_le_add S b a
      rw [← heq, map_smul_eq_mul, Real.norm_eq_abs, abs_div, abs_of_pos hNr] at hh
      linarith
    have hdiff : 1 ≤ |(i : ℝ) - (j : ℝ)| := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · rw [abs_of_nonpos (by
          have hh : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.le_of_lt h
          linarith)]
        have hh : (i : ℕ) + 1 ≤ (j : ℕ) := h
        have hh' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hh
        linarith
      · rw [abs_of_nonneg (by
          have hh : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.le_of_lt h
          linarith)]
        have hh : (j : ℕ) + 1 ≤ (i : ℕ) := h
        have hh' : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hh
        linarith
    have hh := mul_le_mul_of_nonneg_right hdiff (apply_nonneg S v)
    have hd' : |(i : ℝ) - (j : ℝ)| * S v ≤ 2 * (N : ℝ) := by
      have := (div_le_iff₀ hNr).mp (show
        |(i : ℝ) - (j : ℝ)| * S v / (N : ℝ) ≤ 2 by
          simpa only [div_mul_eq_mul_div] using hd)
      exact this
    nlinarith
  have hAsub : (⋃ i, A i) ⊆ {x | V x ≤ 2} := by
    intro x hx
    obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
    have haV : V a ≤ 1 := by
      have hh : V a + S a ≤ 1 := ha
      linarith [apply_nonneg S a]
    have hti : 0 ≤ t i := div_nonneg (Nat.cast_nonneg _) hNr.le
    have hti1 : t i ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast i.isLt.le)
    have hv' : V (t i • v) ≤ 1 := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hti]
      calc t i * V v ≤ t i * 1 := mul_le_mul_of_nonneg_left hv hti
        _ ≤ 1 := by simpa using hti1
    exact (map_add_le_add V a (t i • v)).trans (by linarith)
  have hAv : ∀ i, volume (A i) = volume K := by
    intro i
    dsimp [A]
    rw [Set.image_add_right, measure_preimage_add_right]
  calc
    (N : ℝ≥0∞) * volume (unitBody (V + S)) = ∑' i : Fin N, volume (A i) := by
      simp [hAv, K]
    _ = volume (⋃ i, A i) := (measure_iUnion hAd hAm).symm
    _ ≤ volume {x | V x ≤ 2} := measure_mono hAsub
    _ = (2 : ℝ≥0∞) ^ n * volume (unitBody V) := by
      rw [← two_smul_unitBody]
      rw [Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 2)]
      simp

/-- The same packing estimate after a convex average with the old seminorm. -/
theorem volume_unitBody_average_le (V S Q : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hQ : ∀ v, V v + S v ≤ 2 * Q v) (N : ℕ) (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin n)) (hv : V v ≤ 1) (hSv : 3 * (N : ℝ) ≤ S v) :
    (N : ℝ≥0∞) * volume (unitBody Q) ≤
      (4 : ℝ≥0∞) ^ n * volume (unitBody V) := by
  have hscale : volume (unitBody Q) ≤
      (2 : ℝ≥0∞) ^ n * volume (unitBody (V + S)) := by
    simpa using volume_unitBody_le_of_le_mul (V + S) Q 2 (by norm_num) hQ
  calc
    (N : ℝ≥0∞) * volume (unitBody Q)
      ≤ (N : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n * volume (unitBody (V + S))) := by gcongr
    _ = (2 : ℝ≥0∞) ^ n * ((N : ℝ≥0∞) * volume (unitBody (V + S))) := by ring
    _ ≤ (2 : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ n * volume (unitBody V)) := by
      gcongr 1
      exact volume_unitBody_add_le V S N hN v hv hSv
    _ = (4 : ℝ≥0∞) ^ n * volume (unitBody V) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num

theorem volume_unitBody_average_shrink (V S Q : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hQ : ∀ v, V v + S v ≤ 2 * Q v)
    (v : EuclideanSpace ℝ (Fin n)) (hv : V v ≤ 1) (hSv : 3 * (8 : ℝ) ^ n ≤ S v) :
    (2 : ℝ≥0∞) ^ n * volume (unitBody Q) ≤ volume (unitBody V) := by
  have h := volume_unitBody_average_le V S Q hQ (8 ^ n) (by positivity) v hv
    (by simpa using hSv)
  apply (ENNReal.mul_le_mul_iff_right
    (a := (4 : ℝ≥0∞) ^ n) (by positivity) (by finiteness)).mp
  calc
    (4 : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ n * volume (unitBody Q)) =
        (8 : ℝ≥0∞) ^ n * volume (unitBody Q) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (4 : ℝ≥0∞) ^ n * volume (unitBody V) := by simpa using h

end Submission.Obl.k4_prescribed_polynomial_visibility
