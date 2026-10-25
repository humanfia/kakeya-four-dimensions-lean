-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/CellCatalogue.lean.
-- Original session x1021. Accepted helper results remain imported.
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptCells
import Submission.Obl.k4_scalar_capped_heavy_potential.SupportCounting

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- A restricted source's whole-state coarse catalogue is still charged
to the ORIGINAL joint catalogue, with only the fixed rounding factors. -/
theorem restricted_assigned_intercept_census {Ω : Type*}
    (S S' : Set Ω) (hsub : S' ⊆ S) (z : Ω → Fin 3 → ℝ)
    (X intercept : Ω → ℝ) (P : (Fin 3 → ℝ) → ℝ)
    (ε p w θ Lip : ℝ) (hε : 0 < ε) (hp : 0 < p) (hw : 0 < w)
    (hεp : ε ≤ p) (hLip0 : 0 ≤ Lip) (hθ : θ ≤ w) (hmesh : Lip*p ≤ w)
    (hfit : ∀ e ∈ S', |X e-P (z e)-intercept e| ≤ θ)
    (hLip : ∀ e ∈ S', ∀ f ∈ S', |P (z e)-P (z f)| ≤ Lip*‖z e-z f‖)
    (hj : Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}) :
    Set.Finite {k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S',
      (⌊intercept e/w⌋, stateAssignedBase ε p ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k} ∧
      ({k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S',
        (⌊intercept e/w⌋, stateAssignedBase ε p ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k}).ncard ≤
        243*({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard := by
  have hjs : {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S',
      ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k} ⊆
      {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k} := by
    rintro k ⟨e, he, hk⟩
    exact ⟨e, hsub he, hk⟩
  obtain ⟨hf, h9⟩ := intercept_pair_census S' z X intercept P p w θ Lip hp hw hLip0
    hθ hmesh hfit hLip (hj.subset hjs)
  obtain ⟨ha, h27⟩ := assigned_pair_catalogue S' z X intercept hε hp hεp hf
  refine ⟨ha, ?_⟩
  calc
    _ ≤ 27*(9*({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S',
        ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard) :=
      h27.trans (Nat.mul_le_mul_left 27 h9)
    _ ≤ 27*(9*({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard) :=
      Nat.mul_le_mul_left 27 (Nat.mul_le_mul_left 9 (Set.ncard_le_ncard hjs hj))
    _ = _ := by omega

/-- Slicing a finite pair catalogue into its group fibers charges each
pair once, even when only a subcollection of groups is considered. -/
theorem catalogue_group_cell_budget {G B : Type*} [DecidableEq G] [DecidableEq B]
    (pairs : Finset (G × B)) (groups : Finset G) :
    (∑ g ∈ groups, (((pairs.filter (fun k => k.1 = g)).image Prod.snd).card : ℝ)) ≤
      (pairs.card : ℝ) := by
  classical
  have hh := Submission.Obl.k4_scalar_capped_heavy_potential.group_base_cell_budget
    groups (fun g => (pairs.filter (fun k => k.1 = g)).image Prod.snd)
    pairs ({()} : Finset Unit) (fun k => {k.1}) (fun k _ => k.2)
    (D := 1) (by intro k hk; simp) (by
      intro g hg b hb
      obtain ⟨k, hk, hkb⟩ := Finset.mem_image.mp hb
      obtain ⟨hkp, hkg⟩ := Finset.mem_filter.mp hk
      exact ⟨k, hkp, (), by simp, by simpa [hkg], hkb.symm⟩)
  simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using hh

/-- Each unit cube is bounded by its literal integer corner. -/
theorem assignedUnitCell_subset_ball (k : Fin 3 → ℤ) :
    assignedUnitCell k ⊆ Metric.closedBall 0
      (2+‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : (EuclideanSpace ℝ (Fin 3)))‖) := by
  intro x hx
  let y : (EuclideanSpace ℝ (Fin 3)) := WithLp.toLp 2 (fun i => (k i : ℝ))
  have hcoord (i : Fin 3) : |(x-y) i| ≤ 1 := by
    have hh := Int.floor_eq_iff.mp (congrFun hx i)
    change (k i : ℝ) ≤ x i/1 ∧ x i/1 < (k i : ℝ)+1 at hh
    change |x i-(k i : ℝ)| ≤ 1
    simp only [div_one] at hh
    rw [abs_le]
    constructor <;> linarith
  have hs : ‖x-y‖^2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (1 : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hcoord i)
        simpa only [sq_abs] using hh
      _ = _ := by norm_num
  have hd : ‖x-y‖ ≤ 2 := by nlinarith [norm_nonneg (x-y)]
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    _ = ‖(x-y)+y‖ := by congr 1; abel
    _ ≤ ‖x-y‖+‖y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hd le_rfl

/-- Finitely many assigned unit cells lie in one finite ball, regardless
of the original mesh or the group's mass. -/
theorem finite_assignedUnitCell_ball {m : ℕ} (code : Fin m → Fin 3 → ℤ) :
    ∃ R : ℝ, ∀ i, assignedUnitCell (code i) ⊆ Metric.closedBall 0 R := by
  let radius (i : Fin m) := 2+‖(WithLp.toLp 2 (fun j => (code i j : ℝ)) : (EuclideanSpace ℝ (Fin 3)))‖
  refine ⟨∑ i, radius i, ?_⟩
  intro i
  apply (assignedUnitCell_subset_ball (code i)).trans
  apply Metric.closedBall_subset_closedBall
  change radius i ≤ ∑ i, radius i
  exact Finset.single_le_sum (f := radius) (fun j _ => by dsimp [radius]; positivity) (Finset.mem_univ i)

end Submission.Obl.k4_physical_parent_potential_candidates
