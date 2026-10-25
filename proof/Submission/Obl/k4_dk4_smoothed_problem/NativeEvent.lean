import Submission.Obl.k4_dk4_smoothed_problem.NativePrior

open MeasureTheory Set Metric
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem

theorem HasBoolPolynomialFormat.mono_degree {σ X : Type*} {coord : X → σ → ℝ}
    {S : Set X} {m d D : ℕ} (h : HasBoolPolynomialFormat coord S m d) (hd : d ≤ D) :
    HasBoolPolynomialFormat coord S m D := by
  obtain ⟨p, hp, b, hb⟩ := h
  exact ⟨p, fun i => (hp i).trans hd, b, hb⟩

namespace Framework

def coefficientCube (B : ℝ) : Set (Fin 6 → ℝ) :=
  Icc (fun _ => -B) (fun _ => B)

theorem mem_coefficientCube {B : ℝ} {x : Fin 6 → ℝ} :
    x ∈ coefficientCube B ↔ ∀ j, |x j| ≤ B := by
  simp only [coefficientCube, mem_Icc, Pi.le_def, abs_le]
  exact ⟨fun h j => ⟨h.1 j, h.2 j⟩,
    fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩

def physicalPoint (p : Coefficients × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (trajectoryPoint p.1 p.2)

theorem continuous_physicalPoint : Continuous physicalPoint := by
  unfold physicalPoint trajectoryPoint
  fun_prop

/-- Restricting the event to a common bounded coefficient cube supplies its
pointwise support bounds without changing the smoothed time-mass floor. -/
def boundedNativeEvent (B : ℝ) (U : Set (EuclideanSpace ℝ (Fin 4))) :
    Set (Coefficients × ℝ) :=
  {p | p.1.1 = 0 ∧ p.1.2 ∈ coefficientCube B ∧
    p.2 ∈ Icc (0 : ℝ) 1 ∧ physicalPoint p ∈ U}

theorem measurableSet_boundedNativeEvent (B : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin 4))} (hU : MeasurableSet U) :
    MeasurableSet (boundedNativeEvent B U) := by
  exact ((measurableSet_singleton (0 : ℕ)).preimage (measurable_fst.fst)).inter
    ((measurableSet_Icc.preimage (measurable_fst.snd)).inter
      ((measurableSet_Icc.preimage measurable_snd).inter
        (hU.preimage continuous_physicalPoint.measurable)))

theorem boundedNativeEvent_subset (B : ℝ) (U : Set (EuclideanSpace ℝ (Fin 4))) :
    boundedNativeEvent B U ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
  fun _ h => ⟨mem_univ _, h.2.2.1⟩

theorem boundedNativeEvent_bounds {B : ℝ} {U : Set (EuclideanSpace ℝ (Fin 4))}
    {p : Coefficients × ℝ} (hp : p ∈ boundedNativeEvent B U) :
    p.1.1 = 0 ∧ ∀ j, |p.1.2 j| ≤ B :=
  ⟨hp.1, mem_coefficientCube.mp hp.2.1⟩

theorem packLine_mem_cube {r B : ℝ} (b s : Fin 3 → ℝ)
    (hb : ∀ j, |b j| + r ≤ B) (hs : ∀ j, |s j| + r ≤ B)
    {p : PairCoefficients}
    (hp : p ∈ FiniteSmoothing.coordBox r b ×ˢ FiniteSmoothing.coordBox r s) :
    (packLine p).2 ∈ coefficientCube B := by
  have hpb := FiniteSmoothing.mem_coordBox_iff.mp hp.1
  have hps := FiniteSmoothing.mem_coordBox_iff.mp hp.2
  have hab (j : Fin 3) : |p.1 j| ≤ B := by
    calc
      |p.1 j| = |(p.1 j - b j) + b j| := by rw [sub_add_cancel]
      _ ≤ |p.1 j - b j| + |b j| := abs_add_le _ _
      _ ≤ B := by linarith [hpb j, hb j]
  have has (j : Fin 3) : |p.2 j| ≤ B := by
    calc
      |p.2 j| = |(p.2 j - s j) + s j| := by rw [sub_add_cancel]
      _ ≤ |p.2 j - s j| + |s j| := abs_add_le _ _
      _ ≤ B := by linarith [hps j, hs j]
  rw [mem_coefficientCube]
  intro j
  refine Fin.addCases (motive := fun j : Fin 6 => |(packLine p).2 j| ≤ B)
    (fun a : Fin 3 => ?_) (fun a : Fin 3 => ?_) j
  · simpa only [packLine_coordinate] using hab a
  · simpa only [packLine_slope_coordinate] using has a

theorem nativePrior_cube_support {n : ℕ} {r B : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ)
    (hb : ∀ i j, |b i j| + r ≤ B) (hs : ∀ i j, |s i j| + r ≤ B) :
    nativePrior r b s {l | l.1 = 0 ∧ l.2 ∈ coefficientCube B}ᶜ = 0 := by
  rw [nativePrior_apply, preimage_compl]
  apply FiniteSmoothing.smoothedPrior_support hr
  intro i p hp
  exact ⟨rfl, packLine_mem_cube (b i) (s i) (hb i) (hs i) hp⟩

theorem norm_two_le {z : Fin 2 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hz : ∀ j, |z j| ≤ a) : ‖WithLp.toLp 2 z‖ ≤ 2 * a := by
  have hs (j : Fin 2) : (z j) ^ 2 ≤ a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hz j)
  have hn := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
  simp [Fin.sum_univ_succ] at hn
  nlinarith [hs 0, hs 1, norm_nonneg (WithLp.toLp 2 z), sq_nonneg a]

theorem native_bounds_of_cube {B : ℝ} (hB : 0 ≤ B)
    {l : Coefficients} (hl : l.2 ∈ coefficientCube B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖planarLine l t‖ + ‖planarVelocity l‖ ≤ 6 * B ∧
      |trajectoryPoint l t 3| ≤ 2 * B := by
  have hc := mem_coefficientCube.mp hl
  have ha (i j : Fin 6) : |l.2 i + t * l.2 j| ≤ 2 * B := by
    calc
      |l.2 i + t * l.2 j| ≤ |l.2 i| + |t * l.2 j| := abs_add_le _ _
      _ ≤ B + B := by
        rw [abs_mul, abs_of_nonneg ht.1]
        exact add_le_add (hc i) ((mul_le_mul_of_nonneg_left (hc j) ht.1).trans
          (mul_le_of_le_one_left hB ht.2))
      _ = 2 * B := by ring
  have hy : ‖planarLine l t‖ ≤ 4 * B := by
    have hy0 : ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] :
        EuclideanSpace ℝ (Fin 2))‖ ≤ 2 * (2 * B) := by
      apply norm_two_le (by positivity)
      intro j
      fin_cases j
      · simpa using ha 0 3
      · simpa using ha 1 4
    have hy1 := hy0.trans_eq (show 2 * (2 * B) = 4 * B by ring)
    simpa [planarLine, trajectoryPoint] using hy1
  have hv : ‖planarVelocity l‖ ≤ 2 * B := by
    apply norm_two_le hB
    intro j
    fin_cases j
    · simpa using hc 3
    · simpa using hc 4
  exact ⟨by linarith, by simpa [trajectoryPoint] using ha 2 5⟩

theorem nativePrior_native_bounds {n : ℕ} {r B K : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hK : 6 * B ≤ K) (b s : Fin n → Fin 3 → ℝ)
    (hb : ∀ i j, |b i j| + r ≤ B) (hs : ∀ i j, |s i j| + r ≤ B) :
    ∀ᵐ l ∂nativePrior r b s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖planarLine l t‖ + ‖planarVelocity l‖ ≤ K ∧ |trajectoryPoint l t 3| ≤ K := by
  have hsupport : ∀ᵐ l ∂nativePrior r b s, l.1 = 0 ∧ l.2 ∈ coefficientCube B :=
    ae_iff.mpr (nativePrior_cube_support hr b s hb hs)
  filter_upwards [hsupport] with l hl
  intro t ht
  have h := native_bounds_of_cube hB hl.2 ht
  exact ⟨h.1.trans hK, h.2.trans (by linarith)⟩

theorem boundedNativeEvent_time_mass {n m : ℕ} (hn : 0 < n) {r δ B : ℝ}
    (hr : 0 < r) (b s : Fin n → Fin 3 → ℝ)
    (hb : ∀ i j, |b i j| + r ≤ B) (hs : ∀ i j, |s i j| + r ≤ B)
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ)
    (hρ : ∀ j, ρ j + 6 * r ≤ δ) (a : ENNReal)
    (ha : ∀ i, a ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      FiniteSmoothing.graphLine (b i) (s i) t ∈ ⋃ j, ball (z j) (ρ j)}) :
    a ≤ ((nativePrior r b s).prod volume).restrict
      (boundedNativeEvent B (⋃ j, ball (z j) δ)) univ := by
  rw [Measure.restrict_apply_univ, nativePrior_prod_apply hn hr]
  apply FiniteSmoothing.smoothedPrior_time_mass hn hr b s _ a ha
  rintro i ⟨p, t⟩ ⟨hp, ht, hcover⟩
  refine ⟨rfl, packLine_mem_cube (b i) (s i) (hb i) (hs i) hp, ht, ?_⟩
  change physicalPoint (packLine p, t) ∈ ⋃ j, ball (z j) δ
  rw [physicalPoint, packLine_trajectory]
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  exact mem_iUnion.mpr ⟨j, ball_subset_ball (hρ j)
    (FiniteSmoothing.graphLine_perturbation_mem_ball hr.le
      (FiniteSmoothing.mem_coordBox_iff.mp hp.1)
      (FiniteSmoothing.mem_coordBox_iff.mp hp.2) ht hj)⟩

theorem boundedNativeEvent_format {m : ℕ} (B : ℝ)
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    ∃ m₀ : ℕ, m₀ ≤ 14 + m ∧
      HasBoolPolynomialFormat id
        {x : Fin 7 → ℝ |
          ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈
            boundedNativeEvent B (⋃ j, ball (z j) δ)} m₀ 4 := by
  by_cases hi : i = 0
  · subst i
    refine ⟨14 + m, le_rfl, ?_⟩
    have h := (native_coefficient_box_format (fun _ => -B) (fun _ => B)).inter
      (native_incidence_format z (fun _ => δ) (fun _ => hδ))
    convert h using 1 <;> try omega
    ext x
    simp [boundedNativeEvent, coefficientCube, physicalPoint, trajectoryPoint, nativePoint]
  · refine ⟨0, by omega, ?_⟩
    convert HasBoolPolynomialFormat.empty (X := Fin 7 → ℝ) id 4 using 1
    ext x
    simp only [boundedNativeEvent, mem_setOf_eq, hi, false_and, mem_empty_iff_false]

end Framework
end Submission.Obl.k4_dk4_smoothed_problem
