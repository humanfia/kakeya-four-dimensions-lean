/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/VelocityBins.lean -/
import Mathlib

/-! Fine velocity-bin weights inherit neighborhood bounds from coarse grid caps. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped BigOperators Classical

def scalarVelocityBin (ξ : ℝ) (j : ℤ) : Set ℝ := {v | (⌊v / ξ⌋ : ℤ) = j}

theorem measurableSet_scalarVelocityBin (ξ : ℝ) (j : ℤ) :
    MeasurableSet (scalarVelocityBin ξ j) := by
  unfold scalarVelocityBin
  exact measurableSet_eq_fun (by fun_prop) measurable_const

theorem scalarVelocityBin_disjoint (ξ : ℝ) :
    Pairwise fun i j : ℤ => Disjoint (scalarVelocityBin ξ i) (scalarVelocityBin ξ j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hi hj
  exact hij (hi.symm.trans hj)

theorem scalarVelocityBin_center_error {ξ v : ℝ} {j : ℤ} (hξ : 0 < ξ)
    (hv : v ∈ scalarVelocityBin ξ j) : |v - ξ * (j : ℝ)| ≤ ξ := by
  have h := Int.floor_eq_iff.mp hv
  have hlo := (le_div_iff₀ hξ).mp h.1
  have hhi := (div_lt_iff₀ hξ).mp h.2
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

theorem coarse_velocity_bin_near {δ u v : ℝ} (hδ : 0 < δ) (hv : |v - u| ≤ 2 * δ) :
    (⌊v / δ⌋ : ℤ) ∈ Finset.Icc ((⌊u / δ⌋ : ℤ) - 2) ((⌊u / δ⌋ : ℤ) + 2) := by
  have hlo : u / δ - 2 ≤ v / δ := by
    apply (le_div_iff₀ hδ).mpr
    rw [sub_mul, div_mul_cancel₀ _ hδ.ne']
    linarith [(abs_le.mp hv).1]
  have hhi : v / δ ≤ u / δ + 2 := by
    apply (div_le_iff₀ hδ).mpr
    rw [add_mul, div_mul_cancel₀ _ hδ.ne']
    linarith [(abs_le.mp hv).2]
  apply Finset.mem_Icc.mpr
  constructor
  · rw [← Int.floor_sub_intCast (u / δ) (2 : ℤ)]
    exact Int.floor_mono hlo
  · rw [← Int.floor_add_intCast (u / δ) (2 : ℤ)]
    exact Int.floor_mono hhi

/-- Fine bins whose centers lie in a delta-neighborhood occupy at most five
coarse delta-bins. The estimate keeps the original palette measure. -/
theorem fine_palette_neighborhood_cap {β : Type*} [Fintype β]
    (π : Measure ℝ) [IsFiniteMeasure π] (b : β → ℤ) (hb : Function.Injective b)
    {ξ δ M : ℝ} (hξ : 0 < ξ) (hδ : 0 < δ) (hξδ : ξ ≤ δ) (hM : 0 ≤ M)
    (hcap : ∀ j : ℤ, π (scalarVelocityBin δ j) ≤ ENNReal.ofReal M) (u : ℝ) :
    (∑ j, if |ξ * (b j : ℝ) - u| < δ then (π (scalarVelocityBin ξ (b j))).toReal else 0) ≤
      5 * M := by
  let F : Finset β := Finset.univ.filter (fun j => |ξ * (b j : ℝ) - u| < δ)
  let Q : Finset ℤ := Finset.Icc ((⌊u / δ⌋ : ℤ) - 2) ((⌊u / δ⌋ : ℤ) + 2)
  let E : Set ℝ := ⋃ j ∈ F, scalarVelocityBin ξ (b j)
  have hdisj : (↑F : Set β).PairwiseDisjoint (fun j => scalarVelocityBin ξ (b j)) := by
    intro i hi j hj hij
    exact scalarVelocityBin_disjoint ξ (fun he => hij (hb he))
  have hsum :
      (∑ j, if |ξ * (b j : ℝ) - u| < δ then (π (scalarVelocityBin ξ (b j))).toReal else 0) =
        (π E).toReal := by
    rw [← Finset.sum_filter]
    dsimp only [E]
    rw [measure_biUnion_finset hdisj (fun j hj => measurableSet_scalarVelocityBin ξ (b j)),
      ENNReal.toReal_sum (fun j hj => measure_ne_top π _)]
  have hcover : E ⊆ ⋃ j ∈ Q, scalarVelocityBin δ j := by
    intro v hv
    obtain ⟨j, hj, hv⟩ := Set.mem_iUnion₂.mp hv
    have hnear := (Finset.mem_filter.mp hj).2
    have herror := scalarVelocityBin_center_error hξ hv
    have hvu : |v - u| ≤ 2 * δ := by
      calc
        |v - u| = |(v - ξ * (b j : ℝ)) + (ξ * (b j : ℝ) - u)| := by congr 1; ring
        _ ≤ |v - ξ * (b j : ℝ)| + |ξ * (b j : ℝ) - u| := abs_add_le _ _
        _ ≤ ξ + δ := add_le_add herror hnear.le
        _ ≤ 2 * δ := by linarith
    exact Set.mem_iUnion₂.mpr ⟨⌊v / δ⌋, coarse_velocity_bin_near hδ hvu, rfl⟩
  have hQ : Q.card = 5 := by dsimp [Q]; rw [Int.card_Icc]; omega
  have hmass : π E ≤ ENNReal.ofReal (5 * M) := by
    calc
      π E ≤ ∑ j ∈ Q, π (scalarVelocityBin δ j) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ j ∈ Q, ENNReal.ofReal M := Finset.sum_le_sum (fun j hj => hcap j)
      _ = ENNReal.ofReal (5 * M) := by
        simp only [Finset.sum_const, hQ, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
        norm_num
  rw [hsum]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 5 * M)] using h

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
