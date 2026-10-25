import Submission.Obl.k4_scalar_pure_multiworld_homogenization.MarginalBounds

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction Submission.Lib.K4MarginalAveraging

def chartLabel (σ : ℝ) (z : Fin 6 → ℝ) : Fin 3 → ℤ :=
  ![⌊z 0 / σ⌋, ⌊z 1 / σ⌋, ⌊z 3 / σ⌋]

def tableBase (σ : ℝ) (l : Fin 3 → ℤ) : Fin 2 → ℝ :=
  fun j => σ * (l j.castSucc : ℝ)

def chartTable (σ a : ℝ) (h : (Fin 6 → ℝ) → ℝ) (l : Fin 3 → ℤ) : ℝ :=
  realMarginal a h (tableBase σ l, ⌊σ * (l 2 : ℝ) / a⌋)

theorem chartTable_bounds (σ a : ℝ) {h : (Fin 6 → ℝ) → ℝ}
    (hm : Measurable h) (h₀ : ∀ z, 0 ≤ h z) {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hs : supportedInCube h R) (hb : ∀ z, h z ≤ M)
    (l : Fin 3 → ℤ) : 0 ≤ chartTable σ a h l ∧ chartTable σ a h l ≤ M * (2 * R) ^ 4 := by
  refine ⟨realMarginal_nonneg a h₀ _, ?_⟩
  have hbound := marginal_bound a hR hM hs hb (tableBase σ l, ⌊σ * (l 2 : ℝ) / a⌋)
  rw [← ofReal_realMarginal a hm h₀ hs
    (fun z => by simpa only [abs_of_nonneg (h₀ z)] using hb z)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ M * (2 * R) ^ 4)).mp hbound

/-- The lookup reads the fine cell's left endpoint. Its value is the actual
averaged density whenever this fine cell stays in one coarse bin. -/
theorem chartTable_factor {σ : ℝ} (hσ : 0 < σ) (a : ℝ) (h : (Fin 6 → ℝ) → ℝ)
    (hcell : ∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
      (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊z i / σ⌋ = ⌊z' i / σ⌋) → h z = h z')
    (z : Fin 6 → ℝ) (hgood : z 3 ∉ straddles σ a) :
    realMarginal a h (chartObservation a z) = chartTable σ a h (chartLabel σ z) := by
  let b : Fin 2 → ℝ := ![z 0, z 1]
  let l : Fin 3 → ℤ := chartLabel σ z
  let rep : Fin 2 → ℝ := tableBase σ l
  have hconst (v : Fin 4 → ℝ) (b b' : Fin 2 → ℝ)
      (hb : ∀ j, ⌊b j / σ⌋ = ⌊b' j / σ⌋) :
      h (join (b, v)) = h (join (b', v)) := by
    apply hcell
    · intro i hi
      fin_cases i <;> simp_all [join]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hb 0
      · exact hb 1
  have hrep : meshTag σ rep = fun j : Fin 2 => l j.castSucc :=
    meshTag_representative hσ _
  have hfloor (j : Fin 2) : ⌊b j / σ⌋ = ⌊rep j / σ⌋ := by
    calc
      _ = l j.castSucc := by fin_cases j <;> rfl
      _ = _ := (congrFun hrep j).symm
  have hleft : meshLeft σ (z 3) = σ * (l 2 : ℝ) := by
    change (⌊z 3 / σ⌋ : ℝ) * σ = σ * (⌊z 3 / σ⌋ : ℝ)
    exact mul_comm _ _
  have hbin : ⌊z 3 / a⌋ = ⌊σ * (l 2 : ℝ) / a⌋ := by
    have hh : ⌊z 3 / a⌋ = ⌊meshLeft σ (z 3) / a⌋ := not_ne_iff.mp hgood
    rwa [hleft] at hh
  have hmarg := realCountedMarginal_same_cell volume (fun v b => h (join (b, v)))
    (fun v : Fin 4 → ℝ => ⌊v 1 / a⌋) σ hconst b rep hfloor ⌊z 3 / a⌋
  change realMarginal a h (b, ⌊z 3 / a⌋) = realMarginal a h (rep, ⌊σ * (l 2 : ℝ) / a⌋)
  exact hmarg.trans (congrArg (fun j => realMarginal a h (rep, j)) hbin)

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
