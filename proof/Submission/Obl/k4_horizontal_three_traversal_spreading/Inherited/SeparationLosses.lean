-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/SeparationLosses.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/SeparationLosses.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteTraversals
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.PaletteDiscretization
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Loss estimates for avoiding previously used velocities and times. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- Disjoint time cells near a fixed time fit in one enlarged interval. -/
theorem time_center_near_count {Tc : Type*} [Fintype Tc] [DecidableEq Tc]
    (I : Tc → Set ℝ) (center : Tc → ℝ) (d δ r v : ℝ)
    (hd : 0 < d) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hmeas : ∀ t, MeasurableSet (I t))
    (hdisj : Pairwise (fun t u => Disjoint (I t) (I u)))
    (hvol : ∀ t, volume (I t) = ENNReal.ofReal d)
    (hnear : ∀ t s, s ∈ I t → |s - center t| ≤ δ) :
    ((univ.filter (fun t => |center t - v| ≤ r)).card : ℝ) ≤ 2 * (r + δ) / d := by
  let B : Finset Tc := univ.filter (fun t => |center t - v| ≤ r)
  let J : Set ℝ := Set.Icc (v - (r + δ)) (v + (r + δ))
  let μ : Measure ℝ := volume.restrict J
  have hJ : MeasurableSet J := measurableSet_Icc
  have hμ : μ Set.univ ≠ ∞ := by simp [μ, J, Real.volume_Icc]
  haveI : IsFiniteMeasure μ := ⟨hμ.lt_top⟩
  have hsubset (t : Tc) (ht : t ∈ B) : I t ⊆ J := by
    intro s hs
    have ht' := (mem_filter.mp ht).2
    have hdist : |s - v| ≤ r + δ :=
      (abs_sub_le s (center t) v).trans (by linarith [hnear t s hs])
    exact ⟨by linarith [(abs_le.mp hdist).1], by linarith [(abs_le.mp hdist).2]⟩
  have hfloor (t : Tc) (ht : t ∈ B) : d ≤ μ.real (I t) := by
    have heq : μ (I t) = ENNReal.ofReal d := by
      rw [Measure.restrict_apply (hmeas t), Set.inter_eq_left.mpr (hsubset t ht), hvol]
    rw [measureReal_def, heq, ENNReal.toReal_ofReal hd.le]
  have hcount := Submission.Lib.K4FinitePlankAtlases.old_cell_count μ B I
    (fun _ _ _ _ hne => hdisj hne) (fun t _ => hmeas t) hd hfloor
  have hmass : μ.real Set.univ = 2 * (r + δ) := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    change volume.real J = _
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  simpa only [hmass] using hcount

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- External palette domination also controls the probability of every bad palette set. -/
theorem finite_refresh_bad_palette_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (π : Pal → ℝ) (K : ℝ)
    (hcap : ∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
      condKey X.P X.fine e er) ≤ K * π z) (e : Ω) (B : Finset Pal) :
    (∑ er, condKey X.P X.fine e er * (if X.Z er ∈ B then 1 else 0)) ≤
      K * ∑ z ∈ B, π z := by
  have h := finite_refresh_palette_test_bound X π K hcap e
    (fun z => if z ∈ B then 1 else 0) (fun z => by split_ifs <;> norm_num)
  simpa only [mul_ite, mul_one, mul_zero, sum_ite_mem, Finset.univ_inter] using h

/-- A conditional velocity loss inherits the interval cap of the original
palette measure, enlarged only by the rounding error. -/
theorem finite_refresh_near_velocity_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C : Pal → Set ℝ) (vel : Pal → ℝ) (K δ r v A : ℝ) (hK : 0 ≤ K)
    (hmeas : ∀ z, MeasurableSet (C z))
    (hdisj : Pairwise (fun z w => Disjoint (C z) (C w)))
    (hnear : ∀ z x, x ∈ C z → |x - vel z| ≤ δ)
    (hinterval : μ.real (Set.Icc (v - (r + δ)) (v + (r + δ))) ≤ A)
    (hcap : ∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
      condKey X.P X.fine e er) ≤ K * μ.real (C z)) (e : Ω) :
    (∑ er, condKey X.P X.fine e er * (if |vel (X.Z er) - v| ≤ r then 1 else 0)) ≤
      K * A := by
  let B : Finset Pal := univ.filter (fun z => |vel z - v| ≤ r)
  have hbad := finite_refresh_bad_palette_bound X (fun z => μ.real (C z)) K hcap e B
  have hweight := (finite_palette_near_weight μ C vel hmeas hdisj δ r v hnear).trans hinterval
  have hbad' :
      (∑ er, condKey X.P X.fine e er * (if |vel (X.Z er) - v| ≤ r then 1 else 0)) ≤
        K * ∑ z ∈ B, μ.real (C z) := by
    simpa only [B, mem_filter, Finset.mem_univ, true_and] using hbad
  exact hbad'.trans (mul_le_mul_of_nonneg_left hweight hK)

/-- A heavy trajectory assigns at most its cell ceiling times the number
of bad time cells to a failed time test. -/
theorem finite_traversal_bad_cells_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
      prior κ a * ρ)
    (er : Ω) (hh : X.heavy prior lam er false) (B : Finset Tc) :
    (∑ e', condKey X.P (X.armKey false) er e' * (if X.cell e' ∈ B then 1 else 0)) ≤
      (ρ / lam) * (B.card : ℝ) := by
  have h := X.sum_condKey_cell_le hP prior hlam hρ hcell er false hh
    (fun t => if t ∈ B then 1 else 0) (fun t => by split_ifs <;> norm_num)
  simpa using h

/-- The mesh length cancels from the loss for avoiding one previous time. -/
theorem finite_traversal_near_time_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (I : Tc → Set ℝ) (center : Tc → ℝ)
    (lam H d δ r v : ℝ) (hlam : 0 < lam) (hH : 0 ≤ H)
    (hd : 0 < d) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hmeas : ∀ t, MeasurableSet (I t))
    (hdisj : Pairwise (fun t u => Disjoint (I t) (I u)))
    (hvol : ∀ t, volume (I t) = ENNReal.ofReal d)
    (hnear : ∀ t s, s ∈ I t → |s - center t| ≤ δ)
    (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
      prior κ a * (H * d))
    (er : Ω) (hh : X.heavy prior lam er false) :
    (∑ e', condKey X.P (X.armKey false) er e' *
      (if |center (X.cell e') - v| ≤ r then 1 else 0)) ≤ 2 * H * (r + δ) / lam := by
  let B : Finset Tc := univ.filter (fun t => |center t - v| ≤ r)
  have hbad := finite_traversal_bad_cells_bound X hP prior lam (H * d) hlam
    (mul_nonneg hH hd.le) hcell er hh B
  have hcount := time_center_near_count I center d δ r v hd hδ hr hmeas hdisj hvol hnear
  have hprod := mul_le_mul_of_nonneg_left hcount (div_nonneg (mul_nonneg hH hd.le) hlam.le)
  have heq : (H * d / lam) * (2 * (r + δ) / d) = 2 * H * (r + δ) / lam := by
    field_simp
  have hbad' : (∑ e', condKey X.P (X.armKey false) er e' *
      (if |center (X.cell e') - v| ≤ r then 1 else 0)) ≤ (H * d / lam) * (B.card : ℝ) := by
    simpa only [B, mem_filter, Finset.mem_univ, true_and] using hbad
  exact hbad'.trans (hprod.trans_eq heq)

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
