import Submission.Lib.K4ModelReduction.FiniteTable
import Submission.Lib.K4OriginalLists.SignVariation
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

/-!
Quantitative averaging in the three continuous coordinates of a native
observation. All analytic averaging estimates come from the accepted
`Submission.Lib.K4ModelReduction` library.
-/

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Lib.K4ModelReduction
open scoped ENNReal

/-- Equality on a partial mesh: unaveraged coordinates retain their exact values. -/
theorem eq_of_partial_coordinate_cells {ι : Type*} [DecidableEq ι]
    (L : List ι) (f : (ι → ℝ) → ℝ) (ρ : ℝ)
    (hf : ∀ i ∈ L, constantOnCoordinateCells f ρ i)
    (x y : ι → ℝ) (hother : ∀ i ∉ L, x i = y i)
    (hfloor : ∀ i ∈ L, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) : f x = f y := by
  induction L generalizing x with
  | nil =>
    exact congrArg f (funext fun i => hother i (by simp))
  | cons i L ih =>
    let z := Function.update x i (y i)
    have hxz : f x = f z := by
      apply hf i (List.mem_cons_self ..)
      · intro j hji
        simp only [z, Function.update_of_ne hji]
      · simpa [z] using hfloor i (List.mem_cons_self ..)
    refine hxz.trans (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)) z ?_ ?_)
    · intro j hj
      by_cases hji : j = i
      · subst j
        simp [z]
      · simpa only [z, Function.update_of_ne hji] using
          hother j (by simp only [List.mem_cons, not_or]; exact ⟨hji, hj⟩)
    · intro j hj
      by_cases hji : j = i
      · subst j
        simp [z]
      · simpa only [z, Function.update_of_ne hji] using
          hfloor j (List.mem_cons_of_mem i hj)

/-- Average only a chosen list of coordinates, with a cube supplying finite transverse volume.
The input may have an arbitrary finite polynomial sign rule on each relevant line. -/
theorem partial_polynomial_averaging {n : ℕ} {ι : Type*} [Fintype ι]
    (B T : ℝ) (D : ℕ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) B)
    (hf : ∀ x, 0 ≤ f.val x) (hs : supportedInCube f.val T)
    (L : List (Fin (n + 1)))
    (p : Fin (n + 1) → (Fin n → ℝ) → ι → Polynomial ℝ)
    (hdepend : ∀ i ∈ L, ∀ y t t',
      (∀ j, (p i y j).eval t ≤ 0 ↔ (p i y j).eval t' ≤ 0) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y))
    (hdegree : ∀ i ∈ L, ∀ y, ∑ j, (p i y j).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) B,
      (∀ x, 0 ≤ g.val x) ∧
      (∫⁻ x, ENNReal.ofReal (g.val x)) = (∫⁻ x, ENNReal.ofReal (f.val x)) ∧
      (∀ x y, (∀ i ∉ L, x i = y i) →
        (∀ i ∈ L, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g.val x = g.val y) ∧
      supportedInCube g.val (T + (L.length : ℝ) * ρ) ∧
      densityL1Distance volume g.val f.val ≤
        ENNReal.ofReal ((L.length : ℝ) * (4 * B * (D : ℝ) * ρ) * (2 * T) ^ n) := by
  classical
  let S : Set (Fin n → ℝ) := Icc (fun _ => -T) (fun _ => T)
  have hS : MeasurableSet S := measurableSet_Icc
  have hvol : volume S = ENNReal.ofReal ((2 * T) ^ n) := by
    simp only [S, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) _).symm
  let g := L.foldr (fun i g => coordinateAverage i B hρ g) f
  refine ⟨g, coordinate_averaging_nonneg B hρ L f hf,
    coordinate_averaging_mass B hρ L f hf, ?_,
    coordinate_averaging_support B T hρ L f hs, ?_⟩
  · exact eq_of_partial_coordinate_cells L g.val ρ
      (coordinate_averaging_constant B hρ L f)
  · have he : ∀ i ∈ L,
        densityL1Distance volume (coordinateAverage i B hρ f).val f.val ≤
          ENNReal.ofReal (4 * B * (D : ℝ) * ρ) * volume S := by
      intro i hi
      apply coordinateAverage_polynomial_error i B D hB f S hS (p i)
      · intro y hy t
        have hy' : ¬ ∀ j, -T ≤ y j ∧ y j ≤ T := by
          simpa only [S, mem_Icc, Pi.le_def, forall_and] using hy
        obtain ⟨j, hj⟩ := not_forall.mp hy'
        apply hs _ (i.succAbove j)
        simpa only [Fin.insertNth_apply_succAbove, not_le, ← abs_le] using hj
      · intro y _
        exact hdepend i hi y
      · intro y _
        exact hdegree i hi y
    refine (coordinate_averaging_error_le B hρ L f _ he).trans_eq ?_
    rw [hvol, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

/-- The native coefficient tuple as a function of position, time and velocity. -/
def nativeCoefficients (x : Fin 7 → ℝ) : Fin 6 → ℝ :=
  ![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6]

/-- Coefficients followed by time, matching the polynomial format of an event fiber. -/
def nativeEventPoint (x : Fin 7 → ℝ) : Fin 7 → ℝ :=
  Fin.snoc (nativeCoefficients x) (x 0)

@[simp] theorem nativeEventPoint_last (x : Fin 7 → ℝ) : nativeEventPoint x 6 = x 0 := by
  change Fin.snoc _ _ (Fin.last 6) = _
  rw [Fin.snoc_last]

@[simp] theorem nativeEventPoint_last_fin (x : Fin 7 → ℝ) :
    nativeEventPoint x (Fin.last 6) = x 0 := nativeEventPoint_last x

/-- The three coordinates that remain continuous in every observation. -/
def baseCoordinates : List (Fin 7) := [0, 1, 2]

private noncomputable def sliceVariable (v : Fin 7 → ℝ) (i j : Fin 7) : Polynomial ℝ :=
  if j = i then Polynomial.X else Polynomial.C (v j)

private theorem eval_sliceVariable (v : Fin 7 → ℝ) (i j : Fin 7) (t : ℝ) :
    (sliceVariable v i j).eval t = Function.update v i t j := by
  by_cases h : j = i <;> simp [sliceVariable, h]

private theorem natDegree_sliceVariable (v : Fin 7 → ℝ) (i j : Fin 7) :
    (sliceVariable v i j).natDegree ≤ 1 := by
  unfold sliceVariable
  split_ifs <;> simp

private noncomputable def nativeCoefficientSlice (v : Fin 7 → ℝ) (i : Fin 7) :
    Fin 6 → Polynomial ℝ :=
  let q := sliceVariable v i
  ![q 1 - q 0 * q 4, q 2 - q 0 * q 5, q 3 - q 0 * q 6, q 4, q 5, q 6]

private theorem eval_nativeCoefficientSlice (v : Fin 7 → ℝ) (i : Fin 7) (t : ℝ) :
    (fun j => (nativeCoefficientSlice v i j).eval t) =
      nativeCoefficients (Function.update v i t) := by
  funext j
  fin_cases j <;>
    simp [nativeCoefficientSlice, nativeCoefficients, eval_sliceVariable]

private theorem natDegree_nativeCoefficientSlice (v : Fin 7 → ℝ) (i : Fin 7)
    (hi : i ∈ baseCoordinates) (j : Fin 6) :
    (nativeCoefficientSlice v i j).natDegree ≤ 1 := by
  have hlarge (k : Fin 7) (hk : 3 ≤ k.val) :
      sliceVariable v i k = Polynomial.C (v k) := by
    have hki : k ≠ i := by
      simp only [baseCoordinates, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> intro h <;> subst k <;> norm_num at hk
    simp [sliceVariable, hki]
  have hprod (k : Fin 7) (hk : 3 ≤ k.val) :
      (sliceVariable v i 0 * sliceVariable v i k).natDegree ≤ 1 := by
    rw [hlarge k hk]
    exact (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_sliceVariable v i 0)
  have hsub (a b : Fin 7) (hb : 3 ≤ b.val) :
      (sliceVariable v i a - sliceVariable v i 0 * sliceVariable v i b).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (natDegree_sliceVariable v i a) (hprod b hb))
  fin_cases j
  · exact hsub 1 4 (by decide)
  · exact hsub 2 5 (by decide)
  · exact hsub 3 6 (by decide)
  · exact natDegree_sliceVariable v i 4
  · exact natDegree_sliceVariable v i 5
  · exact natDegree_sliceVariable v i 6

private noncomputable def nativeEventSlice (v : Fin 7 → ℝ) (i : Fin 7) :
    Fin 7 → Polynomial ℝ :=
  Fin.snoc (nativeCoefficientSlice v i) (sliceVariable v i 0)

private theorem eval_nativeEventSlice (v : Fin 7 → ℝ) (i : Fin 7) (t : ℝ) :
    (fun j => (nativeEventSlice v i j).eval t) =
      nativeEventPoint (Function.update v i t) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change (Fin.snoc (α := fun _ : Fin 7 => Polynomial ℝ) (nativeCoefficientSlice v i)
      (sliceVariable v i 0) (Fin.last 6)).eval t =
        nativeEventPoint (Function.update v i t) (Fin.last 6)
    rw [Fin.snoc_last, nativeEventPoint_last_fin, eval_sliceVariable]
  · simpa [nativeEventSlice, nativeEventPoint] using
      congrFun (eval_nativeCoefficientSlice v i t) k

private theorem natDegree_nativeEventSlice (v : Fin 7 → ℝ) (i : Fin 7)
    (hi : i ∈ baseCoordinates) (j : Fin 7) :
    (nativeEventSlice v i j).natDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change (Fin.snoc (α := fun _ : Fin 7 => Polynomial ℝ) (nativeCoefficientSlice v i)
      (sliceVariable v i 0) (Fin.last 6)).natDegree ≤ 1
    rw [Fin.snoc_last]
    exact natDegree_sliceVariable v i 0
  · simpa only [nativeEventSlice, Fin.snoc_castSucc] using
      natDegree_nativeCoefficientSlice v i hi k

/-- The density of one weighted native component in sheared coordinates. -/
noncomputable def nativeComponentDensity (c : ℝ) (A : Set (Fin 6 → ℝ))
    (B : Set (Fin 7 → ℝ)) (x : Fin 7 → ℝ) : ℝ := by
  classical
  exact if nativeCoefficients x ∈ A ∧ nativeEventPoint x ∈ B then c else 0

theorem nativeCoefficients_measurable : Measurable nativeCoefficients := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> dsimp [nativeCoefficients] <;> fun_prop

theorem nativeEventPoint_measurable : Measurable nativeEventPoint := by
  apply Measurable.of_eval
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa only [nativeEventPoint_last_fin] using (measurable_pi_apply (0 : Fin 7))
  · simpa [nativeEventPoint] using
      (nativeCoefficients_measurable.eval (a := k))

theorem measurableSet_of_polynomial_description {n m : ℕ}
    (A : Set (Fin n → ℝ)) (p : Fin m → MvPolynomial (Fin n) ℝ)
    (b : (Fin m → Bool) → Bool)
    (hA : ∀ x, x ∈ A ↔ b (fun j => decide (0 ≤ MvPolynomial.eval x (p j))) = true) :
    MeasurableSet A := by
  have hm := Submission.Lib.K4OriginalLists.measurable_sign_rule
    (fun j x => MvPolynomial.eval x (p j))
    (fun j => (p j).continuous_eval.measurable) b
  have hs := (measurableSet_singleton true).preimage hm
  exact hs.congr (by ext x; exact (hA x).symm)

theorem nativeComponentDensity_measurable (c : ℝ) (A : Set (Fin 6 → ℝ))
    (B : Set (Fin 7 → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (nativeComponentDensity c A B) := by
  classical
  exact Measurable.ite
    ((hA.preimage nativeCoefficients_measurable).inter
      (hB.preimage nativeEventPoint_measurable)) measurable_const measurable_const

theorem nativeComponentDensity_bound (c : ℝ) (hc : 0 ≤ c)
    (A : Set (Fin 6 → ℝ)) (B : Set (Fin 7 → ℝ)) (x : Fin 7 → ℝ) :
    0 ≤ nativeComponentDensity c A B x ∧ |nativeComponentDensity c A B x| ≤ c := by
  classical
  unfold nativeComponentDensity
  split_ifs <;> simp [hc, abs_of_nonneg hc]

theorem nativeComponentDensity_support (c T : ℝ) (hT : 1 ≤ T)
    (A : Set (Fin 6 → ℝ)) (B : Set (Fin 7 → ℝ))
    (hA : ∀ a ∈ A, ∀ j, |a j| ≤ T)
    (hB : ∀ a ∈ B, a 6 ∈ Icc (0 : ℝ) 1) :
    supportedInCube (nativeComponentDensity c A B) (2 * T) := by
  classical
  intro x j hj
  have hnot : ¬ (nativeCoefficients x ∈ A ∧ nativeEventPoint x ∈ B) := by
    rintro ⟨ha, hb⟩
    have ht : x 0 ∈ Icc (0 : ℝ) 1 := by
      simpa only [nativeEventPoint_last] using hB _ hb
    have ht' : |x 0| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
    have hc := hA _ ha
    have hpos (a b : ℝ) (ha : |a - x 0 * b| ≤ T) (hb : |b| ≤ T) :
        |a| ≤ 2 * T := by
      calc
        |a| = |(a - x 0 * b) + x 0 * b| := by congr 1; ring
        _ ≤ |a - x 0 * b| + |x 0 * b| := abs_add_le _ _
        _ ≤ T + 1 * T := add_le_add ha (by
          rw [abs_mul]
          exact mul_le_mul ht' hb (abs_nonneg _) zero_le_one)
        _ = 2 * T := by ring
    have hx : ∀ j, |x j| ≤ 2 * T := by
      intro k
      fin_cases k
      · exact ht'.trans (by linarith)
      · exact hpos (x 1) (x 4) (hc 0) (hc 3)
      · exact hpos (x 2) (x 5) (hc 1) (hc 4)
      · exact hpos (x 3) (x 6) (hc 2) (hc 5)
      · exact (hc 3).trans (by linarith)
      · exact (hc 4).trans (by linarith)
      · exact (hc 5).trans (by linarith)
    exact (not_lt_of_ge (hx j)) hj
  simp [nativeComponentDensity, hnot]

/-- A single native polynomial-format component has a bounded approximation on the
three-dimensional base mesh. The estimate is independent of all polynomial coefficients. -/
theorem native_component_flattening {mA mB : ℕ}
    (c T : ℝ) (hc : 0 ≤ c) (hT : 1 ≤ T) (D : ℕ)
    (A : Set (Fin 6 → ℝ)) (B : Set (Fin 7 → ℝ))
    (pA : Fin mA → MvPolynomial (Fin 6) ℝ)
    (pB : Fin mB → MvPolynomial (Fin 7) ℝ)
    (bA : (Fin mA → Bool) → Bool) (bB : (Fin mB → Bool) → Bool)
    (hdegA : ∀ j, (pA j).totalDegree ≤ D) (hdegB : ∀ j, (pB j).totalDegree ≤ D)
    (hfmtA : ∀ a, a ∈ A ↔ bA (fun j => decide (0 ≤ MvPolynomial.eval a (pA j))) = true)
    (hfmtB : ∀ a, a ∈ B ↔ bB (fun j => decide (0 ≤ MvPolynomial.eval a (pB j))) = true)
    (hsA : ∀ a ∈ A, ∀ j, |a j| ≤ T)
    (hsB : ∀ a ∈ B, a 6 ∈ Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : (Fin 7 → ℝ) → ℝ, Measurable g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ c) ∧
      (∫⁻ x, ENNReal.ofReal (g x)) =
        (∫⁻ x, ENNReal.ofReal (nativeComponentDensity c A B x)) ∧
      (∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
        (∀ i ∈ baseCoordinates, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g x = g y) ∧
      supportedInCube g (2 * T + 3 * ρ) ∧
      densityL1Distance volume g (nativeComponentDensity c A B) ≤
        ENNReal.ofReal (12 * c * (((mA + mB) * D : ℕ) : ℝ) * ρ * (4 * T) ^ 6) := by
  classical
  let f : boundedMeasurableFunctions (Fin 7 → ℝ) c :=
    ⟨nativeComponentDensity c A B,
      nativeComponentDensity_measurable c A B
        (measurableSet_of_polynomial_description A pA bA hfmtA)
        (measurableSet_of_polynomial_description B pB bB hfmtB),
      fun x => (nativeComponentDensity_bound c hc A B x).2⟩
  let p : Fin 7 → (Fin 6 → ℝ) → (Fin mA ⊕ Fin mB) → Polynomial ℝ := fun i y =>
    Sum.elim
      (fun j => -MvPolynomial.eval₂ Polynomial.C
        (nativeCoefficientSlice (i.insertNth 0 y) i) (pA j))
      (fun j => -MvPolynomial.eval₂ Polynomial.C
        (nativeEventSlice (i.insertNth 0 y) i) (pB j))
  have hevalA (i : Fin 7) (y : Fin 6 → ℝ) (j : Fin mA) (t : ℝ) :
      (p i y (.inl j)).eval t =
        -MvPolynomial.eval (nativeCoefficients (i.insertNth t y)) (pA j) := by
    simp only [p, Sum.elim_inl, Polynomial.eval_neg,
      Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution,
      eval_nativeCoefficientSlice, Fin.update_insertNth]
  have hevalB (i : Fin 7) (y : Fin 6 → ℝ) (j : Fin mB) (t : ℝ) :
      (p i y (.inr j)).eval t =
        -MvPolynomial.eval (nativeEventPoint (i.insertNth t y)) (pB j) := by
    simp only [p, Sum.elim_inr, Polynomial.eval_neg,
      Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution,
      eval_nativeEventSlice, Fin.update_insertNth]
  have hdepend : ∀ i ∈ baseCoordinates, ∀ y t t',
      (∀ j, (p i y j).eval t ≤ 0 ↔ (p i y j).eval t' ≤ 0) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y) := by
    intro i hi y t t' hh
    have hA : nativeCoefficients (i.insertNth t y) ∈ A ↔
        nativeCoefficients (i.insertNth t' y) ∈ A := by
      rw [hfmtA, hfmtA]
      suffices heq : (fun j => decide (0 ≤ MvPolynomial.eval
          (nativeCoefficients (i.insertNth t y)) (pA j))) =
          (fun j => decide (0 ≤ MvPolynomial.eval
            (nativeCoefficients (i.insertNth t' y)) (pA j))) by rw [heq]
      funext j
      apply decide_eq_decide.mpr
      simpa only [hevalA, neg_nonpos] using hh (.inl j)
    have hB : nativeEventPoint (i.insertNth t y) ∈ B ↔
        nativeEventPoint (i.insertNth t' y) ∈ B := by
      rw [hfmtB, hfmtB]
      suffices heq : (fun j => decide (0 ≤ MvPolynomial.eval
          (nativeEventPoint (i.insertNth t y)) (pB j))) =
          (fun j => decide (0 ≤ MvPolynomial.eval
            (nativeEventPoint (i.insertNth t' y)) (pB j))) by rw [heq]
      funext j
      apply decide_eq_decide.mpr
      simpa only [hevalB, neg_nonpos] using hh (.inr j)
    simp only [f, nativeComponentDensity, hA, hB]
  have hdegree : ∀ i ∈ baseCoordinates, ∀ y,
      ∑ j, (p i y j).natDegree ≤ (mA + mB) * D := by
    intro i hi y
    calc
      _ ≤ ∑ _j : Fin mA ⊕ Fin mB, D := by
        apply Finset.sum_le_sum
        intro j _
        cases j with
        | inl j =>
          simp only [p, Sum.elim_inl, Polynomial.natDegree_neg]
          exact (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le _ _
            (natDegree_nativeCoefficientSlice _ i hi)).trans (hdegA j)
        | inr j =>
          simp only [p, Sum.elim_inr, Polynomial.natDegree_neg]
          exact (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le _ _
            (natDegree_nativeEventSlice _ i hi)).trans (hdegB j)
      _ = _ := by simp
  obtain ⟨g, hg0, hmass, hcell, hs, he⟩ := partial_polynomial_averaging
    c (2 * T) ((mA + mB) * D) hc (by linarith) f
    (fun x => (nativeComponentDensity_bound c hc A B x).1)
    (nativeComponentDensity_support c T hT A B hsA hsB)
    baseCoordinates p hdepend hdegree hρ
  refine ⟨g.val, g.property.1, fun x => ⟨hg0 x, ?_⟩, hmass, hcell, ?_, ?_⟩
  · simpa only [abs_of_nonneg (hg0 x)] using g.property.2 x
  · norm_num [baseCoordinates] at hs ⊢
    exact hs
  · convert he using 1 <;> simp only [baseCoordinates, List.length_cons,
      List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> congr 1 <;> ring

end Submission.Obl.k4_native_base_flattening
