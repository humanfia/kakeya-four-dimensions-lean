-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CommonFiberTables.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CommonFiberTables.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/CommonFiberTables.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CellFiberChoices
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.FiberCenters

/-!
Four common choices on the original reference space: one field value per
grid cell and one coefficient code per fiber in each of three directions.
The loss is the product of the four local list sizes, independently of the
number of cells or fibers.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def gridFiberKey {S : Type*} (axis : Fin 3) (g : S × S × S) : S × S :=
  ![g.2, (g.1, g.2.2), (g.1, g.2.1)] axis

/-- Choose actual common field and fiber codes, retaining the product
fraction of the original source mass. -/
theorem select_common_grid_fiber_codes {X S : Type*} [MeasurableSpace X]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {q m : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ]
    (grid : X → S × S × S) (hgrid : Measurable grid)
    (G : X → Fin q → ℝ) (hG : Measurable G)
    (C : Fin 3 → X → Fin m → ℝ) (hC : ∀ i, Measurable (C i))
    (Ω : Set X) (hΩ : MeasurableSet Ω) (p : ℝ) (K₀ Kf : ℕ)
    (hfield : ∀ g, ∃ F : Finset (Fin q → ℤ), F.card ≤ K₀ ∧
      ∀ x ∈ Ω, grid x = g → cell p (G x) ∈ F)
    (hfiber : ∀ i k, ∃ F : Finset (Fin m → ℤ), F.card ≤ Kf ∧
      ∀ x ∈ Ω, gridFiberKey i (grid x) = k → cell p (C i x) ∈ F) :
    ∃ (value : S × S × S → Fin q → ℤ)
      (fiber : Fin 3 → S × S → Fin m → ℤ) (T : Set X),
      MeasurableSet T ∧ T ⊆ Ω ∧
      (∀ x, x ∈ T ↔ x ∈ Ω ∧ cell p (G x) = value (grid x) ∧
        ∀ i, cell p (C i x) = fiber i (gridFiberKey i (grid x))) ∧
      μ.real Ω ≤ (K₀ : ℝ) * (Kf : ℝ) ^ 3 * μ.real T := by
  classical
  have hk (i : Fin 3) : Measurable (fun x => gridFiberKey i (grid x)) :=
    (measurable_of_finite (gridFiberKey i)).comp hgrid
  obtain ⟨value, T₀, hT₀, hT₀Ω, hmem₀, hmass₀⟩ :=
    select_finite_key_value_bins μ grid hgrid G hG Ω hΩ p K₀ hfield
  obtain ⟨fx, T₁, hT₁, hT₁₀, hmem₁, hmass₁⟩ :=
    select_finite_key_value_bins μ (fun x => gridFiberKey 0 (grid x)) (hk 0)
      (C 0) (hC 0) T₀ hT₀ p Kf (fun k => by
        obtain ⟨F, hF, hFm⟩ := hfiber 0 k
        exact ⟨F, hF, fun x hx => hFm x (hT₀Ω hx)⟩)
  obtain ⟨fy, T₂, hT₂, hT₂₁, hmem₂, hmass₂⟩ :=
    select_finite_key_value_bins μ (fun x => gridFiberKey 1 (grid x)) (hk 1)
      (C 1) (hC 1) T₁ hT₁ p Kf (fun k => by
        obtain ⟨F, hF, hFm⟩ := hfiber 1 k
        exact ⟨F, hF, fun x hx => hFm x (hT₀Ω (hT₁₀ hx))⟩)
  obtain ⟨fz, T₃, hT₃, hT₃₂, hmem₃, hmass₃⟩ :=
    select_finite_key_value_bins μ (fun x => gridFiberKey 2 (grid x)) (hk 2)
      (C 2) (hC 2) T₂ hT₂ p Kf (fun k => by
        obtain ⟨F, hF, hFm⟩ := hfiber 2 k
        exact ⟨F, hF, fun x hx => hFm x (hT₀Ω (hT₁₀ (hT₂₁ hx)))⟩)
  let fiber : Fin 3 → S × S → Fin m → ℤ := ![fx, fy, fz]
  refine ⟨value, fiber, T₃, hT₃, hT₃₂.trans (hT₂₁.trans (hT₁₀.trans hT₀Ω)), ?_, ?_⟩
  · intro x
    rw [hmem₃, hmem₂, hmem₁, hmem₀]
    constructor
    · rintro ⟨⟨⟨⟨hx, hg⟩, hx₀⟩, hx₁⟩, hx₂⟩
      refine ⟨hx, hg, fun i => ?_⟩
      fin_cases i
      · exact hx₀
      · exact hx₁
      · exact hx₂
    · rintro ⟨hx, hg, hf⟩
      refine ⟨⟨⟨⟨hx, hg⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hf 0
      · exact hf 1
      · exact hf 2
  · calc
      μ.real Ω ≤ (K₀ : ℝ) * μ.real T₀ := hmass₀
      _ ≤ (K₀ : ℝ) * ((Kf : ℝ) * μ.real T₁) :=
        mul_le_mul_of_nonneg_left hmass₁ (by positivity)
      _ ≤ (K₀ : ℝ) * ((Kf : ℝ) * ((Kf : ℝ) * μ.real T₂)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmass₂ (by positivity)) (by positivity)
      _ ≤ (K₀ : ℝ) * ((Kf : ℝ) * ((Kf : ℝ) * ((Kf : ℝ) * μ.real T₃))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmass₃ (by positivity)) (by positivity)) (by positivity)
      _ = _ := by ring

def gridPointOf {S : Type*} (coord : S → ℝ) (g : S × S × S) : Fin 3 → ℝ :=
  ![coord g.1, coord g.2.1, coord g.2.2]

def commonGridValue {S : Type*} {q : ℕ} (p : ℝ)
    (value : S × S × S → Fin q → ℤ) (g : S × S × S) (j : Fin q) : ℝ :=
  p * (value g j : ℝ)

/-- One chosen coefficient code gives one actual polynomial on the entire
fiber. The two other grid coordinates give its fixed time offset. -/
def commonFiberPolynomial {S : Type*} {q : ℕ} (coord : S → ℝ) (D : ℕ) (p : ℝ)
    (fiber : Fin 3 → S × S → Fin (q * (D + 1)) → ℤ)
    (axis : Fin 3) (key : S × S) (j : Fin q) : Polynomial ℝ :=
  (rowCoefficientCenter D p (fiber axis key) j).comp
    (Polynomial.C (coord key.1 + coord key.2) + Polynomial.X)

theorem degree_commonFiberPolynomial {S : Type*} {q : ℕ} (coord : S → ℝ)
    (D : ℕ) (p : ℝ) (fiber : Fin 3 → S × S → Fin (q * (D + 1)) → ℤ)
    (axis : Fin 3) (key : S × S) (j : Fin q) :
    (commonFiberPolynomial coord D p fiber axis key j).natDegree ≤ D := by
  apply Polynomial.natDegree_comp_le.trans
  have haff : (Polynomial.C (coord key.1 + coord key.2) + Polynomial.X :
      Polynomial ℝ).natDegree ≤ 1 := (Polynomial.natDegree_add_le _ _).trans (by simp)
  exact (Nat.mul_le_mul (degree_coefficientCenterPolynomial D p _) haff).trans (by simp)

theorem eval_commonFiberPolynomial {S : Type*} {q : ℕ} (coord : S → ℝ)
    (D : ℕ) (p : ℝ) (fiber : Fin 3 → S × S → Fin (q * (D + 1)) → ℤ)
    (axis : Fin 3) (g : S × S × S) (j : Fin q) :
    (commonFiberPolynomial coord D p fiber axis (gridFiberKey axis g) j).eval
        (gridPointOf coord g axis) =
      (rowCoefficientCenter D p (fiber axis (gridFiberKey axis g)) j).eval
        (∑ i, gridPointOf coord g i) := by
  simp only [commonFiberPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  fin_cases axis <;> simp [gridFiberKey, gridPointOf, Fin.sum_univ_succ] <;> ring

/-- The common tables fit every positive ORIGINAL cell. The proof chooses
an actual original occurrence in that cell and transfers its old fit to
the fixed grid center; it does not choose another polynomial there. -/
theorem selected_common_fiber_fits {X S : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (T : Set X) (grid : X → S × S × S)
    (coord : S → ℝ) (u : X → Fin 3 → ℝ) (G : X → Fin q → ℝ)
    (P : Fin 3 → X → Fin q → Polynomial ℝ) (D : ℕ) (p K ξ ε : ℝ)
    (hp : 0 < p) (hK : 1 ≤ K) (hξ : 0 ≤ ξ)
    (hcoord : ∀ s, |coord s| ≤ K) (hu : ∀ x ∈ T, ∀ i, |u x i| ≤ K)
    (hdist : ∀ x ∈ T, ∀ i, |u x i - gridPointOf coord (grid x) i| ≤ ξ)
    (hG : ∀ x ∈ T, ∀ j, |G x j| ≤ K)
    (hdegree : ∀ axis x, x ∈ T → ∀ j, (P axis x j).natDegree ≤ D)
    (hcoeff : ∀ axis x, x ∈ T → ∀ j k, |(P axis x j).coeff k| ≤ K)
    (hfit : ∀ axis x, x ∈ T → ∀ j, |G x j - (P axis x j).eval (∑ i, u x i)| ≤ ε)
    (value : S × S × S → Fin q → ℤ)
    (fiber : Fin 3 → S × S → Fin (q * (D + 1)) → ℤ)
    (hvalue : ∀ x ∈ T, cell p (G x) = value (grid x))
    (hfiber : ∀ axis x, x ∈ T → polynomialFitCoefficientCode D p (P axis x) =
      fiber axis (gridFiberKey axis (grid x))) :
    ∀ g, 0 < μ.real (T ∩ grid ⁻¹' {g}) →
      (∀ j, |commonGridValue p value g j| ≤ K + p) ∧
      ∀ axis j,
        |commonGridValue p value g j -
          (commonFiberPolynomial coord D p fiber axis (gridFiberKey axis g) j).eval
            (gridPointOf coord g axis)| ≤
          p + ε + ((D : ℝ) + 1) * p * (3 * K) ^ D +
            3 * ((D : ℝ) + 1) * D * (K + p) * (3 * K) ^ D * ξ := by
  intro g hg
  have hne : μ (T ∩ grid ⁻¹' {g}) ≠ 0 := by
    intro hzero
    simp only [measureReal_def, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hg
  obtain ⟨x, hx, hxg⟩ := nonempty_of_measure_ne_zero hne
  have hxg' : grid x = g := hxg
  have hround (j : Fin q) : |commonGridValue p value g j - G x j| ≤ p := by
    have he := coefficient_floor_error p (G x j) hp
    have hc := congrFun (hvalue x hx) j
    change ⌊G x j / p⌋ = value (grid x) j at hc
    rw [hxg'] at hc
    rw [hc, abs_sub_comm] at he
    exact he
  constructor
  · intro j
    have htri := abs_sub_le (commonGridValue p value g j) (G x j) 0
    simp only [sub_zero] at htri
    linarith [hround j, hG x hx j]
  · intro axis j
    rw [eval_commonFiberPolynomial]
    have hvg (i : Fin 3) : |gridPointOf coord (grid x) i| ≤ K := by
      fin_cases i <;> exact hcoord _
    have hf := row_center_cartesian_fit (P axis x) D (hdegree axis x hx)
      p K ξ ε p hp hK hξ (u x) (gridPointOf coord (grid x)) (hu x hx) hvg
      (hdist x hx) (fiber axis (gridFiberKey axis (grid x))) (hfiber axis x hx)
      (hcoeff axis x hx) (G x) (commonGridValue p value g) hround (hfit axis x hx) j
    simpa only [hxg'] using hf

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
