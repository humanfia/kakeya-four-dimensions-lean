/- Adapted from this LOT tree, o078, session x0260, commit 34c7136a25cd.
   Original file: Submission/Lib/K4ExactMeasureTools/CoefficientEntries.lean -/
/-
Adapted from: here:o078
-/
import Submission.Obl.k4_scalar_grid_parameter_preparation.QuadraticCurves
import Submission.Obl.k4_scalar_grid_parameter_preparation.SparseEntryPruning

namespace Submission.Obl.k4_scalar_grid_parameter_preparation
open MeasureTheory

def coefficientPhysicalEntry {α : Type*} (b : α → Fin 5 → ℝ) (B : Set α)
    (h : ℝ) (z : Fin 3 → ℤ) : Set (α × ℝ) :=
  {p | p.1 ∈ B ∧ quadraticCoordinateCode h (b p.1) p.2 = z}

theorem measurableSet_coefficientPhysicalEntry {α : Type*} [MeasurableSpace α]
    (b : α → Fin 5 → ℝ) (hb : Measurable b) {B : Set α} (hB : MeasurableSet B)
    (h : ℝ) (z : Fin 3 → ℤ) : MeasurableSet (coefficientPhysicalEntry b B h z) := by
  have hcode : Measurable (fun p : α × ℝ => quadraticCoordinateCode h (b p.1) p.2) := by
    unfold quadraticCoordinateCode quadraticCoordinates
    fun_prop
  exact (hB.preimage measurable_fst).inter (measurableSet_eq_fun hcode measurable_const)

/-- At one fixed scale, restore all coefficient-block/physical-cell entry
floors in one current law. The deletion cost is independent of the total
number of blocks and cells, and uses the ORIGINAL unnormalized prior. -/
theorem quadratic_coefficient_entry_pruning {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure (α × ℝ)) (ν : Measure α)
    (b : α → Fin 5 → ℝ) (hb : Measurable b)
    (B : κ → Set α) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise fun j j' => Disjoint (B j) (B j'))
    (b₀ : κ → Fin 5 → ℝ) {h K A : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) (hK : 1 ≤ K) (hA : 0 < A)
    (hb₀ : ∀ j e, |b₀ j e| ≤ K)
    (hblock : ∀ j, ∀ x ∈ B j, ∀ e, |b x e - b₀ j e| ≤ h)
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEtime : ∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ R : Set (α × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ENNReal.ofReal ((5000 * 111 ^ 3) * K / A) * ν Set.univ ∧
      ∀ j z, R ∩ coefficientPhysicalEntry b (B j) h z = ∅ ∨
        ENNReal.ofReal (h / A) * ν (B j) < μ (R ∩ coefficientPhysicalEntry b (B j) h z) := by
  classical
  choose Q hQcard hQcover using fun j =>
    quadratic_coordinate_block_grid_cover (b₀ j) hK (hb₀ j) hh hh₁
  obtain ⟨R, hR, hsub, hloss, hfloor⟩ := sparse_prior_entry_pruning μ ν B hB hdisj Q
    (fun j z => coefficientPhysicalEntry b (B j) h z)
    (fun j z _ => measurableSet_coefficientPhysicalEntry b hb (hB j) h z)
    (ENNReal.ofReal (h / A)) (ENNReal.ofReal ((5000 * 111 ^ 3) * K / h))
    (by
      intro j
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hQcard j)) hE
  have hconstant : ENNReal.ofReal (h / A) *
      ENNReal.ofReal ((5000 * 111 ^ 3) * K / h) =
        ENNReal.ofReal ((5000 * 111 ^ 3) * K / A) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hh.le hA.le)]
    congr 1
    field_simp [ne_of_gt hh]
  refine ⟨R, hR, hsub, by simpa only [hconstant] using hloss, ?_⟩
  intro j z
  by_cases hz : z ∈ Q j
  · exact hfloor j z hz
  · left
    ext p
    constructor
    · rintro ⟨hpR, hpB, hpCell⟩
      have hpE := hsub hpR
      have hcode : quadraticCoordinateCode h (b p.1) p.2 = z := hpCell
      have hcovered := hQcover j (b p.1) (hblock j p.1 hpB) p.2 (hEtime p hpE)
      rw [hcode] at hcovered
      exact hz hcovered
    · intro hp
      exact False.elim hp

/-- The coefficient-entry floors can be prepared on a common finite grid.
All widths use the same retained incidence law and the unchanged prior. -/
theorem multiscale_quadratic_coefficient_entry_pruning {α σ : Type*}
    [MeasurableSpace α] [Fintype σ] (n : σ → ℕ)
    (μ : Measure (α × ℝ)) (ν : Measure α)
    (b : α → Fin 5 → ℝ) (hb : Measurable b)
    (B : (s : σ) → Fin (n s) → Set α) (hB : ∀ s j, MeasurableSet (B s j))
    (hdisj : ∀ s, Pairwise fun j j' => Disjoint (B s j) (B s j'))
    (b₀ : (s : σ) → Fin (n s) → Fin 5 → ℝ) (h A : σ → ℝ) {K : ℝ}
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hK : 1 ≤ K) (hA : ∀ s, 0 < A s)
    (hb₀ : ∀ s j e, |b₀ s j e| ≤ K)
    (hblock : ∀ s j, ∀ x ∈ B s j, ∀ e, |b x e - b₀ s j e| ≤ h s)
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEtime : ∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ R : Set (α × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) * K / A s)) * ν Set.univ ∧
      ∀ s j z, R ∩ coefficientPhysicalEntry b (B s j) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * ν (B s j) <
          μ (R ∩ coefficientPhysicalEntry b (B s j) (h s) z) := by
  classical
  have hcover (s : σ) (j : Fin (n s)) :=
    quadratic_coordinate_block_grid_cover (b₀ s j) hK (hb₀ s j) (hh s) (hh₁ s)
  choose Q hQcard hQcover using hcover
  obtain ⟨R, hR, hsub, hloss, hfloor⟩ := multiscale_sparse_prior_entry_pruning
    (fun s => Fin (n s)) μ ν B hB hdisj Q
    (fun s j z => coefficientPhysicalEntry b (B s j) (h s) z)
    (fun s j z _ => measurableSet_coefficientPhysicalEntry b hb (hB s j) (h s) z)
    (fun s => ENNReal.ofReal (h s / A s))
    (fun s => ENNReal.ofReal ((5000 * 111 ^ 3) * K / h s))
    (by
      intro s j
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hQcard s j)) hE
  have hconstant (s : σ) : ENNReal.ofReal (h s / A s) *
      ENNReal.ofReal ((5000 * 111 ^ 3) * K / h s) =
        ENNReal.ofReal ((5000 * 111 ^ 3) * K / A s) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (hh s).le (hA s).le)]
    congr 1
    field_simp [ne_of_gt (hh s)]
  refine ⟨R, hR, hsub, by simpa only [hconstant] using hloss, ?_⟩
  intro s j z
  by_cases hz : z ∈ Q s j
  · exact hfloor s j z hz
  · left
    ext p
    constructor
    · rintro ⟨hpR, hpB, hpCell⟩
      have hpE := hsub hpR
      have hcode : quadraticCoordinateCode (h s) (b p.1) p.2 = z := hpCell
      have hcovered := hQcover s j (b p.1) (hblock s j p.1 hpB) p.2 (hEtime p hpE)
      rw [hcode] at hcovered
      exact hz hcovered
    · intro hp
      exact False.elim hp

/-- Graph renewal preserves every fine-cell floor and every coefficient-
entry floor on the finite grid in a single common reference family. -/
theorem multiscale_quadratic_entry_and_cell_pruning {α σ ζ : Type*}
    [MeasurableSpace α] [Fintype σ] [Fintype ζ] (n : σ → ℕ)
    (μ : Measure (α × ℝ)) (ν : Measure α)
    (b : α → Fin 5 → ℝ) (hb : Measurable b)
    (B : (s : σ) → Fin (n s) → Set α) (hB : ∀ s j, MeasurableSet (B s j))
    (hdisj : ∀ s, Pairwise fun j j' => Disjoint (B s j) (B s j'))
    (b₀ : (s : σ) → Fin (n s) → Fin 5 → ℝ) (h A : σ → ℝ) {K : ℝ}
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hK : 1 ≤ K) (hA : ∀ s, 0 < A s)
    (hb₀ : ∀ s j e, |b₀ s j e| ≤ K)
    (hblock : ∀ s j, ∀ x ∈ B s j, ∀ e, |b x e - b₀ s j e| ≤ h s)
    (F : ζ → Set (α × ℝ)) (hF : ∀ i, MeasurableSet (F i)) (θ : ζ → ENNReal)
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEtime : ∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ R : Set (α × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, θ i) +
        (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) * K / A s)) * ν Set.univ ∧
      (∀ i, R ∩ F i = ∅ ∨ θ i < μ (R ∩ F i)) ∧
      ∀ s j z, R ∩ coefficientPhysicalEntry b (B s j) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * ν (B s j) <
          μ (R ∩ coefficientPhysicalEntry b (B s j) (h s) z) := by
  classical
  have hcover (s : σ) (j : Fin (n s)) :=
    quadratic_coordinate_block_grid_cover (b₀ s j) hK (hb₀ s j) (hh s) (hh₁ s)
  choose Q hQcard hQcover using hcover
  obtain ⟨R, hR, hsub, hloss, hfine, hfloor⟩ :=
    multiscale_sparse_prior_entry_pruning_with_floors (fun s => Fin (n s)) μ ν B hB hdisj Q
      (fun s j z => coefficientPhysicalEntry b (B s j) (h s) z)
      (fun s j z _ => measurableSet_coefficientPhysicalEntry b hb (hB s j) (h s) z)
      (fun s => ENNReal.ofReal (h s / A s))
      (fun s => ENNReal.ofReal ((5000 * 111 ^ 3) * K / h s))
      (by
        intro s j
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hQcard s j)) F hF θ hE
  have hconstant (s : σ) : ENNReal.ofReal (h s / A s) *
      ENNReal.ofReal ((5000 * 111 ^ 3) * K / h s) =
        ENNReal.ofReal ((5000 * 111 ^ 3) * K / A s) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (hh s).le (hA s).le)]
    congr 1
    field_simp [ne_of_gt (hh s)]
  refine ⟨R, hR, hsub, by simpa only [hconstant] using hloss, hfine, ?_⟩
  intro s j z
  by_cases hz : z ∈ Q s j
  · exact hfloor s j z hz
  · left
    ext p
    constructor
    · rintro ⟨hpR, hpB, hpCell⟩
      have hpE := hsub hpR
      have hcode : quadraticCoordinateCode (h s) (b p.1) p.2 = z := hpCell
      have hcovered := hQcover s j (b p.1) (hblock s j p.1 hpB) p.2 (hEtime p hpE)
      rw [hcode] at hcovered
      exact hz hcovered
    · intro hp
      exact False.elim hp

end Submission.Obl.k4_scalar_grid_parameter_preparation
