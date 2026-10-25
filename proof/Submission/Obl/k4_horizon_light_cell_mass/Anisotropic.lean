import Submission.Obl.k4_native_base_flattening.UniformAveraging

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction
open Submission.Obl.k4_native_base_flattening

lemma coordinateAverage_fixed {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : constantOnCoordinateCells f.val ρ i) :
    (coordinateAverage i M hρ f).val = f.val := by
  funext x
  rw [coordinateAverage_eq]
  have hp := meshCell_law_isProbabilityMeasure hρ (x i)
  let := hp
  unfold meshAverage
  apply integral_eq_const
  unfold ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  rw [Measure.restrict_congr_set (halfOpenMeshCell_ae_eq ρ (x i)).symm]
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  apply hf
  · intro j hji
    simp only [Function.update_of_ne hji]
  · simp only [Function.update_self]
    exact (mem_halfOpenMeshCell_iff hρ).mp ht

lemma coordinateAverage_error_of_approx {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hg : constantOnCoordinateCells g.val ρ i) :
    densityL1Distance volume (coordinateAverage i M hρ f).val f.val ≤
      2 * densityL1Distance volume g.val f.val := by
  have hsym : densityL1Distance volume f.val g.val = densityL1Distance volume g.val f.val := by
    unfold densityL1Distance
    simp only [abs_sub_comm]
  calc
    _ ≤ densityL1Distance volume (coordinateAverage i M hρ f).val g.val +
        densityL1Distance volume g.val f.val :=
      densityL1Distance_triangle volume _ _ _ (coordinateAverage i M hρ f).property.1 g.property.1
    _ ≤ densityL1Distance volume f.val g.val + densityL1Distance volume g.val f.val := by
      apply add_le_add _ le_rfl
      have hc := coordinateAverage_contract i M hρ f g
      rw [coordinateAverage_fixed i M hρ g hg] at hc
      exact hc
    _ = _ := by rw [hsym, two_mul]

lemma coordinateAverage_preserves_other_mesh {n : ℕ} (i j : Fin (n + 1)) (M : ℝ)
    {ρ σ : ℝ} (hσ : 0 < σ) (hij : i ≠ j)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : constantOnCoordinateCells f.val ρ i) :
    constantOnCoordinateCells (coordinateAverage j M hσ f).val ρ i := by
  intro x y hother hfloor
  rw [coordinateAverage_eq, coordinateAverage_eq, hother j (Ne.symm hij)]
  congr 1
  funext t
  apply hf
  · intro k hki
    by_cases hkj : k = j
    · subst k; simp
    · simpa only [Function.update_of_ne hkj] using hother k hki
  · simpa only [Function.update_of_ne hij] using hfloor

/-- An isotropic approximation at each mesh controls averaging a single coordinate. -/
theorem native_coordinate_error (n : ℝ) (M D : ℕ) (hn : 2 ≤ n)
    (f : (Fin 7 → ℝ) → ℝ) (hf : NativeMixtureFormat n M D f)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ n ^ (2 * M))
    (i : Fin 7) (hi : i ∈ baseCoordinates) {ρ : ℝ} (hρ : 0 < ρ) :
    densityL1Distance volume
      (coordinateAverage i (n ^ (2 * M)) hρ ⟨f, hfm, hfb⟩).val f ≤
        2 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * ρ) := by
  obtain ⟨m, c, A, B, hm, hc, hA, hB, hsA, hsB, hf⟩ := hf
  obtain ⟨g, hgm, hgb, hcell, hs, he⟩ := finite_native_flattening (n ^ M)
    (one_le_pow₀ (by linarith : 1 ≤ n)) D hm c hc A B hA hB hsA hsB hρ
  have hgb' (x) : |g x| ≤ n ^ (2 * M) := by
    rw [abs_of_nonneg (hgb x).1]
    convert (hgb x).2 using 1 <;> rw [← pow_mul] <;> congr 1 <;> omega
  have hgc : constantOnCoordinateCells g ρ i := by
    intro x y ho hb
    apply hcell x y
    · intro j hj
      exact ho j (fun h => hj (h ▸ hi))
    · intro j hj
      by_cases hji : j = i
      · simpa [hji] using hb
      · rw [ho j hji]
  exact (coordinateAverage_error_of_approx i (n ^ (2 * M)) hρ
    ⟨f, hfm, hfb⟩ ⟨g, hgm, hgb'⟩ hgc).trans (by
      change 2 * densityL1Distance volume g f ≤ _
      rw [hf]
      exact mul_le_mul_right he 2)

/-- The accepted polynomial estimate also controls arbitrary rectangular base meshes. -/
theorem rectangular_native_flattening (n : ℝ) (M D : ℕ) (hn : 2 ≤ n)
    (f : (Fin 7 → ℝ) → ℝ) (hf : NativeMixtureFormat n M D f)
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfb : ∀ x, |f x| ≤ n ^ (2 * M))
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) :
    ∃ g : (Fin 7 → ℝ) → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
        ⌊x 0 / ρ₁⌋ = ⌊y 0 / ρ₁⌋ → ⌊x 1 / ρ₂⌋ = ⌊y 1 / ρ₂⌋ →
        ⌊x 2 / ρ₂⌋ = ⌊y 2 / ρ₂⌋ → g x = g y) ∧
      densityL1Distance volume g f ≤
        6 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂) := by
  let F : boundedMeasurableFunctions (Fin 7 → ℝ) (n ^ (2 * M)) := ⟨f, hfm, hfb⟩
  let A := coordinateAverage (2 : Fin 7) (n ^ (2 * M)) hρ₂ F
  let B := coordinateAverage (1 : Fin 7) (n ^ (2 * M)) hρ₂ A
  let C := coordinateAverage (0 : Fin 7) (n ^ (2 * M)) hρ₁ B
  have ha0 := averageInSplit_nonneg (coordinateSplit (2 : Fin 7)) _ hρ₂ F hf0
  have hb0 := averageInSplit_nonneg (coordinateSplit (1 : Fin 7)) _ hρ₂ A ha0
  have hc0 := averageInSplit_nonneg (coordinateSplit (0 : Fin 7)) _ hρ₁ B hb0
  have hc : ∀ i : Fin 7, i ∈ baseCoordinates →
      constantOnCoordinateCells C.val (if i = 0 then ρ₁ else ρ₂) i := by
    intro i hi
    simp only [baseCoordinates, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact coordinateAverage_constant 0 _ hρ₁ B
    · exact coordinateAverage_preserves_other_mesh 1 0 _ hρ₁ (by decide) B
        (coordinateAverage_constant 1 _ hρ₂ A)
    · exact coordinateAverage_preserves_other_mesh 2 0 _ hρ₁ (by decide) B
        (coordinateAverage_preserves_other_mesh 2 1 _ hρ₂ (by decide) A
          (coordinateAverage_constant 2 _ hρ₂ F))
  refine ⟨C.val, C.property.1, hc0, ?_, ?_⟩
  · intro x y ho h0 h1 h2
    let z := Function.update x 0 (y 0)
    let w := Function.update z 1 (y 1)
    calc
      C.val x = C.val z := hc 0 (by simp [baseCoordinates]) x z
        (by intro j hj; simp [z, Function.update_of_ne hj]) (by simpa [z] using h0)
      _ = C.val w := hc 1 (by simp [baseCoordinates]) z w
        (by intro j hj; simp [w, Function.update_of_ne hj]) (by simpa [w, z] using h1)
      _ = C.val y := hc 2 (by simp [baseCoordinates]) w y (by
        intro j hj
        fin_cases j <;> simp_all [w, z, baseCoordinates]) (by simpa [w, z] using h2)
  · let ρ : Fin 3 → ℝ := ![ρ₁, ρ₂, ρ₂]
    have hρ : ∀ i, 0 < ρ i := by intro i; fin_cases i <;> assumption
    let Op := fun i : Fin 3 => coordinateAverage (i.castLE (by decide) : Fin 7)
      (n ^ (2 * M)) (hρ i)
    have he := averaging_composition_error volume (n ^ (2 * M)) Op
      (fun i f g => coordinateAverage_contract _ _ (hρ i) f g) [0, 1, 2] F
    have hcoord (i : Fin 3) : densityL1Distance volume (Op i F).val F.val ≤
        2 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂) := by
      refine (native_coordinate_error n M D hn f hf hfm hfb _ ?_ (hρ i)).trans ?_
      · fin_cases i <;> simp [baseCoordinates]
      · gcongr
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
        · exact le_max_right _ _
    change densityL1Distance volume (Op 0 (Op 1 (Op 2 F))).val F.val ≤ _
    refine he.trans ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    calc
      _ ≤ 2 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂) +
          (2 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂) +
            2 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂)) :=
        add_le_add (hcoord 0) (add_le_add (hcoord 1) (hcoord 2))
      _ = _ := by ring

end Submission.Obl.k4_horizon_light_cell_mass
