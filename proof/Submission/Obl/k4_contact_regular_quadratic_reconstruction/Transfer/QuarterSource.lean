/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/QuarterSource.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ShearedCells
import Submission.Lib.K4QuadSheetMatching.Matching

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory

/-- A bounded residual has an original-measure source on which a bounded
constant shift makes its error less than a quarter. Only nine scalar bins
are used; the retained mass is measured by the same original law. -/
theorem exists_quarter_residual_source {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (y : Ω → ℝ) (hy : Measurable y)
    (hbound : ∀ᵐ p ∂μ, p ∈ E → |y p| ≤ 1) :
    ∃ (γ : ℝ) (E' : Set Ω), |γ| ≤ 9 / 8 ∧ MeasurableSet E' ∧ E' ⊆ E ∧
      μ E / 9 ≤ μ E' ∧ ∀ p ∈ E', |y p - γ| ≤ 1 / 8 := by
  classical
  let F : Finset ℤ := Finset.Icc (-4) 4
  let code : Ω → ℤ := fun p => ⌊y p / (1 / 4)⌋
  let cell : ℤ → Set Ω := fun j => {p | p ∈ E ∧ code p = j}
  have hcode : Measurable code := by dsimp [code]; fun_prop
  have hcell (j : ℤ) : MeasurableSet (cell j) :=
    hE.inter (measurableSet_eq_fun hcode measurable_const)
  have hcodes : ∀ p : Ω, |y p| ≤ 1 → code p ∈ F := by
    intro p hp
    have hlo : (-4 : ℝ) ≤ y p / (1 / 4) := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith [(abs_le.mp hp).1]
    have hhi : y p / (1 / 4) ≤ (4 : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith [(abs_le.mp hp).2]
    have hlf : (-4 : ℤ) ≤ code p := Int.le_floor.mpr (by simpa using hlo)
    have hhf : code p ≤ 4 := by
      have hh := (Int.floor_le (y p / (1 / 4))).trans hhi
      exact_mod_cast hh
    exact Finset.mem_Icc.mpr ⟨hlf, hhf⟩
  have hcover : E ≤ᵐ[μ] ⋃ j ∈ F, cell j := by
    filter_upwards [hbound] with p hp hpE
    exact mem_iUnion₂.mpr ⟨code p, hcodes p (hp hpE), hpE, rfl⟩
  have hmass : μ E ≤ ∑ j ∈ F, μ (cell j) :=
    (measure_mono_ae hcover).trans (measure_biUnion_finset_le F cell)
  obtain ⟨j, hj, hjmass⟩ := Submission.Lib.K4QuadSheetMatching.exists_sum_ge_div F
    (show F.Nonempty from ⟨0, by norm_num [F]⟩) (fun j => μ (cell j)) (μ E) hmass
  let γ : ℝ := ((j : ℝ) + 1 / 2) * (1 / 4)
  have hjlo : (-4 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjhi : (j : ℝ) ≤ 4 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  refine ⟨γ, cell j, ?_, hcell j, fun p hp => hp.1, ?_, ?_⟩
  · rw [abs_le]
    dsimp [γ]
    constructor <;> linarith
  · simpa [F] using hjmass
  · intro p hp
    have hh := abs_sub_center_of_floor (by norm_num : (0 : ℝ) < 1 / 4) hp.2
    simpa only [γ, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using hh

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
