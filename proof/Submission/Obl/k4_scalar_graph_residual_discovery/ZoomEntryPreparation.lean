/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ZoomEntryPreparation.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientEntries

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

/-- The old-order normalized coefficients in each trajectory's OWN coarse
bin form one global measurable bounded map, before selecting a world. -/
def normalizedCoeff (ρ : ℝ) (l : ScalarLine) (e : Fin 5) : ℝ :=
  l.2 e / ρ - (⌊l.2 e / ρ⌋ : ℝ)

theorem measurable_normalizedCoeff (ρ : ℝ) : Measurable (normalizedCoeff ρ) := by
  apply Measurable.of_eval
  intro e
  dsimp only [normalizedCoeff]
  fun_prop

theorem normalizedCoeff_mem_unit (ρ : ℝ) (l : ScalarLine) (e : Fin 5) :
    normalizedCoeff ρ l e ∈ Ico (0 : ℝ) 1 := by
  have hlo := Int.floor_le (l.2 e / ρ)
  have hhi := Int.lt_floor_add_one (l.2 e / ρ)
  dsimp only [normalizedCoeff]
  constructor <;> linarith

theorem normalizedCoeff_abs_le_one (ρ : ℝ) (l : ScalarLine) (e : Fin 5) :
    |normalizedCoeff ρ l e| ≤ 1 := by
  have h := normalizedCoeff_mem_unit ρ l e
  rw [abs_of_nonneg h.1]
  exact h.2.le

theorem normalizedCoeff_of_coarse {ρ : ℝ} (hρ : 0 < ρ) {l : ScalarLine} {q : Fin 5 → ℤ}
    (hl : cell ρ l.2 = q) (e : Fin 5) :
    normalizedCoeff ρ l e = (l.2 e - (q e : ℝ) * ρ) / ρ := by
  have he := congrFun hl e
  change ⌊l.2 e / ρ⌋ = q e at he
  dsimp only [normalizedCoeff]
  rw [he]
  field_simp

theorem normalizedCoeff_piece_diameter {ρ β r : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hscale : β ≤ ρ * r) {l l' : ScalarLine} {q : Fin 5 → ℤ}
    (hl : cell ρ l.2 = q) (hl' : cell ρ l'.2 = q)
    (hbin : cell β l.2 = cell β l'.2) (e : Fin 5) :
    |normalizedCoeff ρ l e - normalizedCoeff ρ l' e| ≤ r := by
  rw [normalizedCoeff_of_coarse hρ hl, normalizedCoeff_of_coarse hρ hl']
  have hid : (l.2 e - (q e : ℝ) * ρ) / ρ - (l'.2 e - (q e : ℝ) * ρ) / ρ =
      (l.2 e - l'.2 e) / ρ := by ring
  rw [hid, abs_div, abs_of_pos hρ]
  apply (div_le_iff₀ hρ).mpr
  have he := (norm_le_pi_norm (l.2 - l'.2) e).trans (norm_sub_lt_of_cell_eq hβ hbin).le
  change |l.2 e - l'.2 e| ≤ β at he
  nlinarith only [he, hscale]

def parameterPiece (ρ β : ℝ) (q b : Fin 5 → ℤ) : Set ScalarLine :=
  {l | cell ρ l.2 = q ∧ cell β l.2 = b}

theorem measurableSet_parameterPiece (ρ β : ℝ) (q b : Fin 5 → ℤ) :
    MeasurableSet (parameterPiece ρ β q b) :=
  (measurableSet_block ρ q).inter (measurableSet_block β b)

theorem parameterPiece_disjoint {κ : Type*} (ρ β : ℝ) (q b : κ → Fin 5 → ℤ)
    (hinj : Function.Injective (fun j => (q j, b j))) :
    Pairwise (fun j j' => Disjoint (parameterPiece ρ β (q j) (b j)) (parameterPiece ρ β (q j') (b j'))) := by
  intro j j' hne
  apply disjoint_left.mpr
  intro l hl hl'
  exact hne (hinj (Prod.ext (hl.1.symm.trans hl'.1) (hl.2.symm.trans hl'.2)))

theorem parameterPiece_representative {ρ β r : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hscale : β ≤ ρ * r) (q b : Fin 5 → ℤ) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ 1) ∧
      ∀ l ∈ parameterPiece ρ β q b, ∀ e, |normalizedCoeff ρ l e - c e| ≤ r := by
  classical
  by_cases hne : (parameterPiece ρ β q b).Nonempty
  · obtain ⟨l₀, hl₀⟩ := hne
    refine ⟨normalizedCoeff ρ l₀, normalizedCoeff_abs_le_one ρ l₀, ?_⟩
    intro l hl e
    exact normalizedCoeff_piece_diameter hρ hβ hscale hl.1 hl₀.1
      (hl.2.trans hl₀.2.symm) e
  · refine ⟨0, by intro e; simp, ?_⟩
    intro l hl
    exact False.elim (hne ⟨l, hl⟩)

/-- The accepted multiscale current-floor pruning applies to all original
coarse/fine coefficient intersections before any world is normalized. -/
theorem multiscale_zoom_coefficient_entry_pruning {σ : Type*} [Fintype σ]
    (n : σ → ℕ) (μ : Measure ScalarIncidence) (θ : Measure ScalarLine)
    {ρ : ℝ} (hρ : 0 < ρ) (β h A : σ → ℝ)
    (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hA : ∀ s, 0 < A s)
    (q b : (s : σ) → Fin (n s) → Fin 5 → ℤ)
    (hinj : ∀ s, Function.Injective (fun j => (q s j, b s j)))
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / A s)) * θ univ ∧
      ∀ s j z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
          (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * θ (parameterPiece ρ (β s) (q s j) (b s j)) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
            (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z) := by
  classical
  choose c hc hdiam using fun s j =>
    parameterPiece_representative hρ (hβ s) (hscale s) (q s j) (b s j)
  simpa only [mul_one] using multiscale_quadratic_coefficient_entry_pruning n μ θ
    (normalizedCoeff ρ) (measurable_normalizedCoeff ρ)
    (fun s j => parameterPiece ρ (β s) (q s j) (b s j))
    (fun s j => measurableSet_parameterPiece _ _ _ _)
    (fun s => parameterPiece_disjoint ρ (β s) (q s) (b s) (hinj s)) c h A
    hh hh₁ (by norm_num : (1 : ℝ) ≤ 1) hA hc hdiam hE htime

/-- Extra fine-state, strip and posterior-entry floors can be restored
with the coefficient-entry floors under this SAME final current law. -/
theorem multiscale_zoom_entry_and_floors {σ ι : Type*} [Fintype σ] [Fintype ι]
    (n : σ → ℕ) (μ : Measure ScalarIncidence) (θ : Measure ScalarLine)
    {ρ : ℝ} (hρ : 0 < ρ) (β h A : σ → ℝ)
    (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hA : ∀ s, 0 < A s)
    (q b : (s : σ) → Fin (n s) → Fin 5 → ℤ)
    (hinj : ∀ s, Function.Injective (fun j => (q s j, b s j)))
    (F : ι → Set ScalarIncidence) (hF : ∀ i, MeasurableSet (F i)) (τ : ι → ℝ≥0∞)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, τ i) +
        (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / A s)) * θ univ ∧
      (∀ i, R ∩ F i = ∅ ∨ τ i < μ (R ∩ F i)) ∧
      ∀ s j z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
          (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * θ (parameterPiece ρ (β s) (q s j) (b s j)) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
            (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z) := by
  classical
  choose c hc hdiam using fun s j =>
    parameterPiece_representative hρ (hβ s) (hscale s) (q s j) (b s j)
  simpa only [mul_one] using multiscale_quadratic_entry_and_cell_pruning n μ θ
    (normalizedCoeff ρ) (measurable_normalizedCoeff ρ)
    (fun s j => parameterPiece ρ (β s) (q s j) (b s j))
    (fun s j => measurableSet_parameterPiece _ _ _ _)
    (fun s => parameterPiece_disjoint ρ (β s) (q s) (b s) (hinj s)) c h A
    hh hh₁ (by norm_num : (1 : ℝ) ≤ 1) hA hc hdiam F hF τ hE htime

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
