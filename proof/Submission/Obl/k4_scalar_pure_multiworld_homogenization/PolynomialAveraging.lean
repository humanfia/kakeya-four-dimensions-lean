import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Types
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Shear
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.SignAveraging
import Submission.Obl.k4_native_shear_source_transport.PolyAxis
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Lib.K4ModelReduction
open Submission.Obl.k4_native_shear_source_transport

def chartPolynomials : Fin 5 → MvPolynomial (Fin 6) ℝ :=
  ![X 1 - X 0 * X 2, X 2, X 3 - X 0 * X 4 - X 0 ^ 2 * X 5, X 4, X 5]

def eventPoint (z : Fin 6 → ℝ) : Fin 6 → ℝ :=
  Fin.snoc (chartCoefficients z) (z 0)

@[simp] theorem eventPoint_last (z : Fin 6 → ℝ) : eventPoint z 5 = z 0 := by
  change Fin.snoc (α := fun _ : Fin 6 => ℝ) (chartCoefficients z) (z 0) (Fin.last 5) = _
  rw [Fin.snoc_last]

def eventPolynomials : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  Fin.snoc chartPolynomials (X 0)

theorem eval_chartPolynomials (z : Fin 6 → ℝ) :
    (fun j => eval z (chartPolynomials j)) = chartCoefficients z := by
  funext j
  fin_cases j <;> simp [chartPolynomials, chartCoefficients]

theorem eval_eventPolynomials (z : Fin 6 → ℝ) :
    (fun j => eval z (eventPolynomials j)) = eventPoint z := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change eval z (Fin.snoc (α := fun _ : Fin 6 => MvPolynomial (Fin 6) ℝ)
      chartPolynomials (X 0) (Fin.last 5)) =
      Fin.snoc (α := fun _ : Fin 6 => ℝ) (chartCoefficients z) (z 0) (Fin.last 5)
    rw [Fin.snoc_last, Fin.snoc_last, eval_X]
  · simpa only [eventPolynomials, eventPoint, Fin.snoc_castSucc] using
      congrFun (eval_chartPolynomials z) k

theorem chartPolynomials_degree (j : Fin 5) : (chartPolynomials j).totalDegree ≤ 3 := by
  have hmul (i k : Fin 6) :
      ((X i : MvPolynomial (Fin 6) ℝ) * X k).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X i : MvPolynomial (Fin 6) ℝ) (X k)
  have hquad : ((X 0 : MvPolynomial (Fin 6) ℝ) ^ 2 * X 5).totalDegree ≤ 3 := by
    calc
      _ ≤ ((X 0 : MvPolynomial (Fin 6) ℝ) ^ 2).totalDegree +
          (X 5 : MvPolynomial (Fin 6) ℝ).totalDegree := totalDegree_mul _ _
      _ = 3 := by simp
  have hsub (i j k : Fin 6) :
      ((X i : MvPolynomial (Fin 6) ℝ) - X j * X k).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (by simp) (hmul j k))
  fin_cases j
  · exact (hsub 1 0 2).trans (by decide)
  · simp [chartPolynomials]
  · exact (totalDegree_sub _ _).trans (max_le ((hsub 3 0 4).trans (by decide)) hquad)
  · simp [chartPolynomials]
  · simp [chartPolynomials]

theorem eventPolynomials_degree (j : Fin 6) : (eventPolynomials j).totalDegree ≤ 3 := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change (Fin.snoc (α := fun _ : Fin 6 => MvPolynomial (Fin 6) ℝ)
      chartPolynomials (X 0) (Fin.last 5)).totalDegree ≤ 3
    rw [Fin.snoc_last]
    simp
  · simpa only [eventPolynomials, Fin.snoc_castSucc] using chartPolynomials_degree k

def scalarComponentDensity (c : ℝ) (A : Set (Fin 5 → ℝ))
    (B : Set (Fin 6 → ℝ)) (z : Fin 6 → ℝ) : ℝ := by
  classical
  exact if chartCoefficients z ∈ A ∧ eventPoint z ∈ B then c else 0

theorem measurable_chartCoefficients : Measurable chartCoefficients :=
  measurable_fst.comp measurePreserving_unshear.measurable

theorem measurable_eventPoint : Measurable eventPoint := by
  apply Measurable.of_eval
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa only [eventPoint, Fin.snoc_last] using measurable_pi_apply (0 : Fin 6)
  · simpa only [eventPoint, Fin.snoc_castSucc] using
      measurable_chartCoefficients.eval (a := k)

theorem measurable_scalarComponentDensity (c : ℝ) {A : Set (Fin 5 → ℝ)}
    {B : Set (Fin 6 → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (scalarComponentDensity c A B) := by
  classical
  exact Measurable.ite ((hA.preimage measurable_chartCoefficients).inter
    (hB.preimage measurable_eventPoint)) measurable_const measurable_const

theorem scalarComponentDensity_bound {c : ℝ} (hc : 0 ≤ c)
    (A : Set (Fin 5 → ℝ)) (B : Set (Fin 6 → ℝ)) (z : Fin 6 → ℝ) :
    0 ≤ scalarComponentDensity c A B z ∧ |scalarComponentDensity c A B z| ≤ c := by
  classical
  unfold scalarComponentDensity
  split_ifs <;> simp [hc, abs_of_nonneg hc]

theorem scalarComponentDensity_support (c T : ℝ) (hT : 1 ≤ T)
    (A : Set (Fin 5 → ℝ)) (B : Set (Fin 6 → ℝ))
    (hA : ∀ a ∈ A, ∀ j, |a j| ≤ T)
    (hB : ∀ a ∈ B, a 5 ∈ Icc (0 : ℝ) 1) :
    supportedInCube (scalarComponentDensity c A B) (3 * T) := by
  classical
  intro z j hj
  have hnot : ¬ (chartCoefficients z ∈ A ∧ eventPoint z ∈ B) := by
    rintro ⟨ha, hb⟩
    have ht : z 0 ∈ Icc (0 : ℝ) 1 := by
      simpa only [eventPoint_last] using hB _ hb
    have ht' : |z 0| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
    have ht2 : |z 0 ^ 2| ≤ 1 := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) ht' 2).trans_eq (by norm_num)
    have hc := hA _ ha
    have hlinear : |z 1| ≤ 3 * T := by
      calc
        |z 1| = |chartCoefficients z 0 + z 0 * chartCoefficients z 1| := by
          congr 1
          simp [chartCoefficients]
        _ ≤ |chartCoefficients z 0| + |z 0 * chartCoefficients z 1| := abs_add_le _ _
        _ ≤ T + 1 * T := add_le_add (hc 0) (by
          rw [abs_mul]
          exact mul_le_mul ht' (hc 1) (abs_nonneg _) zero_le_one)
        _ ≤ 3 * T := by linarith
    have hquadratic : |z 3| ≤ 3 * T := by
      calc
        |z 3| = |chartCoefficients z 2 + z 0 * chartCoefficients z 3 +
            z 0 ^ 2 * chartCoefficients z 4| := by
          congr 1
          simp [chartCoefficients]
          ring
        _ ≤ |chartCoefficients z 2| + |z 0 * chartCoefficients z 3| +
            |z 0 ^ 2 * chartCoefficients z 4| := (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ T + 1 * T + 1 * T := add_le_add (add_le_add (hc 2) (by
          rw [abs_mul]
          exact mul_le_mul ht' (hc 3) (abs_nonneg _) zero_le_one)) (by
            rw [abs_mul]
            exact mul_le_mul ht2 (hc 4) (abs_nonneg _) zero_le_one)
        _ = 3 * T := by ring
    have hz : ∀ k, |z k| ≤ 3 * T := by
      intro k
      fin_cases k
      · exact ht'.trans (by linarith)
      · exact hlinear
      · exact (hc 1).trans (by linarith)
      · exact hquadratic
      · exact (hc 3).trans (by linarith)
      · exact (hc 4).trans (by linarith)
    exact (not_lt_of_ge (hz j)) hj
  simp [scalarComponentDensity, hnot]

/-- A polynomial-format scalar component can be averaged in `(t,y)` with a
uniform error independent of its polynomial coefficients. -/
theorem scalar_component_flattening (c T : ℝ) (hc : 0 ≤ c) (hT : 1 ≤ T) (D : ℕ)
    (A : Set (Fin 5 → ℝ)) (B : Set (Fin 6 → ℝ))
    (hfmtA : Format 5 T D A) (hfmtB : Format 6 T D B)
    (hsA : ∀ a ∈ A, ∀ j, |a j| ≤ T)
    (hsB : ∀ a ∈ B, a 5 ∈ Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : (Fin 6 → ℝ) → ℝ, Measurable g ∧
      (∀ z, 0 ≤ g z ∧ g z ≤ c) ∧
      (∫⁻ z, ENNReal.ofReal (g z)) =
        (∫⁻ z, ENNReal.ofReal (scalarComponentDensity c A B z)) ∧
      (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
        (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊z i / ρ⌋ = ⌊z' i / ρ⌋) → g z = g z') ∧
      supportedInCube g (3 * T + 2 * ρ) ∧
      densityL1Distance volume g (scalarComponentDensity c A B) ≤
        ENNReal.ofReal (96 * c * T * (D : ℝ) * ρ * (6 * T) ^ 5) := by
  classical
  have hmA := Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable hfmtA
  have hmB := Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable hfmtB
  obtain ⟨mA, hmA', pA, hpA, SA, hA⟩ := hfmtA
  obtain ⟨mB, hmB', pB, hpB, SB, hB⟩ := hfmtB
  let f : boundedMeasurableFunctions (Fin 6 → ℝ) c :=
    ⟨scalarComponentDensity c A B, measurable_scalarComponentDensity c hmA hmB,
      fun z => (scalarComponentDensity_bound hc A B z).2⟩
  let p : Fin 6 → (Fin 5 → ℝ) → (Fin mA ⊕ Fin mB) → Polynomial ℝ := fun i y =>
    Sum.elim
      (fun j => axisPolynomial (pA j) chartPolynomials (i.insertNth 0 y) i)
      (fun j => axisPolynomial (pB j) eventPolynomials (i.insertNth 0 y) i)
  have hevalA (i : Fin 6) (y : Fin 5 → ℝ) (j : Fin mA) (t : ℝ) :
      (p i y (.inl j)).eval t = eval (chartCoefficients (i.insertNth t y)) (pA j) := by
    simp only [p, Sum.elim_inl, axisPolynomial_eval, Fin.update_insertNth,
      eval_chartPolynomials]
  have hevalB (i : Fin 6) (y : Fin 5 → ℝ) (j : Fin mB) (t : ℝ) :
      (p i y (.inr j)).eval t = eval (eventPoint (i.insertNth t y)) (pB j) := by
    simp only [p, Sum.elim_inr, axisPolynomial_eval, Fin.update_insertNth,
      eval_eventPolynomials]
  have hdepend : ∀ i ∈ ([0, 1] : List (Fin 6)), ∀ y t t',
      (∀ j, SignType.sign ((p i y j).eval t) = SignType.sign ((p i y j).eval t')) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y) := by
    intro i hi y t t' h
    have hsignA : (fun j => SignType.sign (eval (chartCoefficients (i.insertNth t y)) (pA j))) =
        (fun j => SignType.sign (eval (chartCoefficients (i.insertNth t' y)) (pA j))) := by
      funext j
      simpa only [hevalA] using h (.inl j)
    have hsignB : (fun j => SignType.sign (eval (eventPoint (i.insertNth t y)) (pB j))) =
        (fun j => SignType.sign (eval (eventPoint (i.insertNth t' y)) (pB j))) := by
      funext j
      simpa only [hevalB] using h (.inr j)
    simp only [f, scalarComponentDensity, hA, hB, mem_ofPred_eq, hsignA, hsignB]
  have hdegree : ∀ i ∈ ([0, 1] : List (Fin 6)), ∀ y,
      ∑ j, (p i y j).natDegree ≤ 3 * ((mA + mB) * D) := by
    intro i hi y
    calc
      _ ≤ ∑ _j : Fin mA ⊕ Fin mB, 3 * D := by
        apply Finset.sum_le_sum
        intro j _
        cases j with
        | inl j =>
          exact (axisPolynomial_natDegree_le (pA j) _ 3 chartPolynomials_degree _ _).trans
            (Nat.mul_le_mul_left 3 (hpA j).1)
        | inr j =>
          exact (axisPolynomial_natDegree_le (pB j) _ 3 eventPolynomials_degree _ _).trans
            (Nat.mul_le_mul_left 3 (hpB j).1)
      _ = _ := by simp; ring
  obtain ⟨g, hg0, hmass, hcell, hs, he⟩ := partial_polynomial_sign_averaging
    c (3 * T) (3 * ((mA + mB) * D)) hc (by linarith) f
    (fun z => (scalarComponentDensity_bound hc A B z).1)
    (scalarComponentDensity_support c T hT A B hsA hsB)
    [0, 1] p hdepend hdegree hρ
  refine ⟨g.val, g.property.1, fun z => ⟨hg0 z, ?_⟩, hmass, hcell, ?_, ?_⟩
  · simpa only [abs_of_nonneg (hg0 z)] using g.property.2 z
  · simpa using hs
  · apply he.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = 48 * c * ((mA : ℝ) + mB) * D * ρ * (6 * T) ^ 5 := by norm_num; ring
      _ ≤ 48 * c * (2 * T) * D * ρ * (6 * T) ^ 5 := by
        gcongr
        linarith
      _ = _ := by ring

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
