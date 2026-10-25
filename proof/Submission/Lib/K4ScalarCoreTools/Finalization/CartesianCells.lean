/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/CartesianCells.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit4d8af73c,
Submission/Obl/k4_scalar_mesh_projection/CartesianCells.lean.
Generic prerequisites retain their own accepted-source credits in Pruning.lean.
-/

import Submission.Lib.K4ScalarActualSwitching.GridSampling
import Submission.Lib.K4ScalarCoreTools.Finalization.Pruning

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory
open Submission.Lib.K4ScalarActualSwitching
open scoped ENNReal

noncomputable def finiteUniformWeights (X : Type*) [Fintype X] : X → ℝ :=
  fun _ => (Fintype.card X : ℝ)⁻¹

theorem finiteUniformWeights_nonneg (X : Type*) [Fintype X] :
    ∀ x, 0 ≤ finiteUniformWeights X x := by
  intro x
  unfold finiteUniformWeights
  positivity

theorem finiteUniformWeights_sum (X : Type*) [Fintype X] [Nonempty X] :
    ∑ x, finiteUniformWeights X x = 1 := by
  simp [finiteUniformWeights]

theorem gridMean_uniform {X : Type*} [Fintype X] (f : X → ℝ) :
    gridMean (finiteUniformWeights X) f = (Fintype.card X : ℝ)⁻¹ * ∑ x, f x := by
  simp only [gridMean, finiteUniformWeights, Finset.mul_sum]

/- Convert the fixed full product grid count into the coordinate law
used by the accepted separated-anchor sampler. -/
open Classical in
theorem uniform_grid_relation_density {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) :
    gridMean (finiteUniformWeights X) (fun x =>
      gridMean (finiteUniformWeights Y) (fun y => gridFlag (R x y))) =
      ((Finset.univ.filter (fun p : X × Y => R p.1 p.2)).card : ℝ) /
        ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) := by
  classical
  simp_rw [gridMean_uniform]
  rw [← Finset.mul_sum]
  simp_rw [gridFlag_eq_ite]
  rw [← Fintype.sum_prod_type (fun p : X × Y => if R p.1 p.2 then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- A subset of retained grid cells carries its original whole-cell
floors. The source law is never replaced by uniform grid counting. -/
theorem original_grid_subset_mass_lower {Ω I : Type*} [MeasurableSpace Ω]
    [DecidableEq I] (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (cell : Ω → I) (hcell : ∀ i, MeasurableSet {x | cell x = i})
    (T : Finset I) (θ : ℝ≥0∞)
    (hfloor : ∀ i ∈ T, θ ≤ μ (E ∩ {x | cell x = i})) :
    (T.card : ℝ≥0∞) * θ ≤ μ {x | x ∈ E ∧ cell x ∈ T} := by
  classical
  have hd : (↑T : Set I).PairwiseDisjoint (fun i => E ∩ {x | cell x = i}) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.2.symm.trans hxj.2)
  have heq : {x | x ∈ E ∧ cell x ∈ T} = ⋃ i ∈ T, E ∩ {x | cell x = i} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨hx, hmem⟩
      exact ⟨cell x, hmem, hx, rfl⟩
    · rintro ⟨i, hi, hx, hxi⟩
      exact ⟨hx, by simpa only [hxi] using hi⟩
  rw [heq, measure_biUnion_finset hd (fun i _ => hE.inter (hcell i))]
  simpa using Finset.sum_le_sum (fun i hi => hfloor i hi)

/-- The light-cell deletion is charged to the original incidence law.
Every surviving cell retains a positive original mass floor. -/
theorem exists_original_heavy_grid_cells {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω)
    (E : Set Ω) (cell : Ω → I) (θ : ℝ≥0∞) :
    ∃ F : Finset I,
      (∀ i ∈ F, θ ≤ μ (E ∩ {x | cell x = i})) ∧
      μ E ≤ μ {x | x ∈ E ∧ cell x ∈ F} + θ * (Fintype.card I : ℝ≥0∞) := by
  classical
  obtain ⟨F, _, hfloor, hmass⟩ := prune_small_labels μ Finset.univ
    (fun i => E ∩ {x | cell x = i}) (fun _ => 1)
    (τ := θ) (B := (Fintype.card I : ℝ≥0∞)) (by simp)
  have hall : (⋃ i ∈ (Finset.univ : Finset I), E ∩ {x | cell x = i}) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hx
      exact hi.1
    · intro hx
      exact mem_iUnion₂.mpr ⟨cell x, Finset.mem_univ _, hx, rfl⟩
  have hF : (⋃ i ∈ F, E ∩ {x | cell x = i}) = {x | x ∈ E ∧ cell x ∈ F} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hx, hxi⟩
      exact ⟨hx, by simpa only [hxi] using hi⟩
    · rintro ⟨hx, hi⟩
      exact ⟨cell x, hi, hx, rfl⟩
  refine ⟨F, by simpa only [mul_one] using hfloor, ?_⟩
  simpa only [hall, hF] using hmass

/-- Positive original cell floors and the original cell ceiling convert
retained incidence mass to a density of actual occupied grid cells. -/
theorem exists_original_heavy_grid_density {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω)
    (E : Set Ω) (cell : Ω → I) (θ m M : ℝ)
    (hθ : 0 < θ) (_hm : 0 < m) (hM : 0 < M)
    (hlower : ENNReal.ofReal m ≤ μ E)
    (hcap : ∀ i, μ (E ∩ {x | cell x = i}) ≤ ENNReal.ofReal M)
    (hlight : θ * (Fintype.card I : ℝ) ≤ m / 2) :
    ∃ F : Finset I,
      (∀ i ∈ F, ENNReal.ofReal θ ≤ μ (E ∩ {x | cell x = i})) ∧
      (∀ i ∈ F, ∃ x ∈ E, cell x = i) ∧
      μ E ≤ μ {x | x ∈ E ∧ cell x ∈ F} +
        ENNReal.ofReal (θ * (Fintype.card I : ℝ)) ∧
      m / (2 * M) ≤ (F.card : ℝ) := by
  classical
  obtain ⟨F, hfloor, hmass⟩ := exists_original_heavy_grid_cells μ E cell (ENNReal.ofReal θ)
  have hretained : μ {x | x ∈ E ∧ cell x ∈ F} ≤
      (F.card : ℝ≥0∞) * ENNReal.ofReal M := by
    have hsub : {x | x ∈ E ∧ cell x ∈ F} ⊆ ⋃ i ∈ F, E ∩ {x | cell x = i} := by
      intro x hx
      exact mem_iUnion₂.mpr ⟨cell x, hx.2, hx.1, rfl⟩
    calc
      _ ≤ μ (⋃ i ∈ F, E ∩ {x | cell x = i}) := measure_mono hsub
      _ ≤ ∑ i ∈ F, μ (E ∩ {x | cell x = i}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ F, ENNReal.ofReal M := Finset.sum_le_sum fun i _ => hcap i
      _ = _ := by simp [nsmul_eq_mul]
  have hlight_eq : ENNReal.ofReal θ * (Fintype.card I : ℝ≥0∞) =
      ENNReal.ofReal (θ * (Fintype.card I : ℝ)) := by
    rw [ENNReal.ofReal_mul hθ.le]
    simp
  have hreal : m ≤ (F.card : ℝ) * M + θ * (Fintype.card I : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      ENNReal.ofReal m ≤ μ E := hlower
      _ ≤ _ := hmass
      _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal M +
          ENNReal.ofReal (θ * (Fintype.card I : ℝ)) := by
        rw [hlight_eq]
        exact add_le_add hretained le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
  refine ⟨F, hfloor, ?_, by simpa only [hlight_eq] using hmass, ?_⟩
  · intro i hi
    have hpos : 0 < μ (E ∩ {x | cell x = i}) :=
      (ENNReal.ofReal_pos.mpr hθ).trans_le (hfloor i hi)
    have hne : (E ∩ {x | cell x = i}).Nonempty := by
      by_contra hn
      rw [not_nonempty_iff_eq_empty.mp hn, measure_empty] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨x, hxE, hxi⟩ := hne
    exact ⟨x, hxE, hxi⟩
  · apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
    nlinarith

end Submission.Lib.K4ScalarCoreTools.Finalization
