-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/InterceptCells.lean.
-- Original session x1021. Accepted helper results remain imported.
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptState
import Submission.Lib.K4AffineMeshCaps.Saturation
import Submission.Lib.K4PlankGeometry
import Submission.Lib.K4ContinuousKakeya.Incidence
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

/-- A coarse base cell assigned by a whole original fine state. -/
def stateAssignedBase (ε p : ℝ) (k : (Fin 3 → ℤ) × ℤ) : Fin 3 → ℤ :=
  fun i => ⌊(ε*(k.1 i : ℝ))/p⌋

theorem measurable_stateAssignedBase (ε p : ℝ) : Measurable (stateAssignedBase ε p) := by
  fun_prop

/-- Fine-state assignment changes each actual coarse coordinate by at
most one integer cell; this is independent of the signal coordinate. -/
theorem stateAssignedBase_near {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) (hεp : ε ≤ p)
    (z : Fin 3 → ℝ) (X : ℝ) :
    stateAssignedBase ε p ((fun i => ⌊z i/ε⌋), ⌊X/ε⌋) ∈
      Submission.Lib.K4ListedExceptions.integerCodeBox 1 (fun i => ⌊z i/p⌋) := by
  apply Submission.Lib.K4ListedExceptions.floor_code_mem_integerCodeBox 1
    (fun i => ε*(⌊z i/ε⌋ : ℝ)) z (fun _ => p) (fun _ => hp)
  intro i
  have hh := Submission.Obl.k4_horizontal_supercritical_three_projections.abs_sub_floor_mul_le
    (x := z i) hε
  simpa only [Nat.cast_one, one_mul, mul_one, abs_sub_comm, mul_comm] using hh.trans hεp

/-- All occupied assigned intercept/base cells are paid by a fixed
27-fold enlargement of the literal intercept/base catalogue. -/
theorem assigned_pair_catalogue {Ω : Type*} (S : Set Ω)
    (z : Ω → Fin 3 → ℝ) (X intercept : Ω → ℝ) {ε p w : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hεp : ε ≤ p)
    (hfinite : Set.Finite {k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
      (⌊intercept e/w⌋, (fun i => ⌊z e i/p⌋)) = k}) :
    Set.Finite {k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
      (⌊intercept e/w⌋, stateAssignedBase ε p ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k} ∧
      ({k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
        (⌊intercept e/w⌋, stateAssignedBase ε p ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k}).ncard ≤
        27*({k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
          (⌊intercept e/w⌋, (fun i => ⌊z e i/p⌋)) = k}).ncard := by
  classical
  let J := hfinite.toFinset
  let cover : Finset (ℤ × (Fin 3 → ℤ)) := J.biUnion fun k =>
    (Submission.Lib.K4ListedExceptions.integerCodeBox 1 k.2).image (Prod.mk k.1)
  have hsub : {k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
      (⌊intercept e/w⌋, stateAssignedBase ε p ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k} ⊆
      (cover : Set (ℤ × (Fin 3 → ℤ))) := by
    rintro k ⟨e, he, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(⌊intercept e/w⌋, fun i => ⌊z e i/p⌋), ?_, ?_⟩
    · exact hfinite.mem_toFinset.mpr ⟨e, he, rfl⟩
    · exact Finset.mem_image.mpr ⟨_, stateAssignedBase_near hε hp hεp (z e) (X e), rfl⟩
  have hf := cover.finite_toSet.subset hsub
  refine ⟨hf, ?_⟩
  have hcard : cover.card ≤ J.card*27 := by
    calc
      _ ≤ ∑ k ∈ J, ((Submission.Lib.K4ListedExceptions.integerCodeBox 1 k.2).image
          (Prod.mk k.1)).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ J, (Submission.Lib.K4ListedExceptions.integerCodeBox 1 k.2).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = _ := by simp [Submission.Lib.K4ListedExceptions.card_integerCodeBox]
  rw [Set.ncard_eq_toFinset_card _ hf, Set.ncard_eq_toFinset_card _ hfinite]
  have hs : hf.toFinset ⊆ cover := fun k hk => hsub (hf.mem_toFinset.mp hk)
  exact ((Finset.card_le_card hs).trans hcard).trans_eq (Nat.mul_comm _ _)

/-- The assigned coarse time index contains the actual old time in one
slab of length at most `2*h*p`, including unaligned fine boundaries. -/
theorem state_assigned_time_slab {h ε p : ℝ} (hh : 0 < h) (hε : 0 < ε) (hp : 0 < p)
    (t0 t : ℝ) (q : ℤ)
    (hcode : (⌊(ε*(⌊((t-t0)/h)/ε⌋ : ℝ))/p⌋ : ℤ) = q) :
    t ∈ Icc (t0+h*p*(q : ℝ)) (t0+h*(p*((q : ℝ)+1)+ε)) := by
  have hcoarse := Int.floor_eq_iff.mp hcode
  rw [le_div_iff₀ hp, div_lt_iff₀ hp] at hcoarse
  have hlo := Int.floor_le (((t-t0)/h)/ε)
  have hhi := Int.lt_floor_add_one (((t-t0)/h)/ε)
  rw [le_div_iff₀ hε] at hlo
  rw [div_lt_iff₀ hε] at hhi
  have ha : p*(q : ℝ) ≤ (t-t0)/h := by nlinarith [hcoarse.1]
  have hb : (t-t0)/h ≤ p*((q : ℝ)+1)+ε := by nlinarith [hcoarse.2]
  rw [le_div_iff₀ hh] at ha
  rw [div_le_iff₀ hh] at hb
  constructor <;> nlinarith

theorem volume_state_assigned_time_section_le {h ε p : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hp : 0 < p) (hεp : ε ≤ p)
    (t0 : ℝ) (q : ℤ) (S : Set ℝ)
    (hS : ∀ t ∈ S, (⌊(ε*(⌊((t-t0)/h)/ε⌋ : ℝ))/p⌋ : ℤ) = q) :
    volume S ≤ ENNReal.ofReal (2*h*p) := by
  calc
    _ ≤ volume (Icc (t0+h*p*(q : ℝ)) (t0+h*(p*((q : ℝ)+1)+ε))) :=
      measure_mono (fun t ht => state_assigned_time_slab hh hε hp t0 t q (hS t ht))
    _ ≤ _ := by
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith

/-- Rescaled unit base cells used by the original Kakeya estimate. -/
def assignedUnitCell (k : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  WithLp.ofLp ⁻¹' Submission.Lib.K4AffineMeshCaps.meshBox 1 k

theorem measurableSet_assignedUnitCell (k : Fin 3 → ℤ) :
    MeasurableSet (assignedUnitCell k) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).measurable
    (Submission.Lib.K4AffineMeshCaps.measurableSet_meshBox 1 k)

theorem volume_assignedUnitCell (k : Fin 3 → ℤ) : volume (assignedUnitCell k) = 1 := by
  rw [assignedUnitCell, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (Submission.Lib.K4AffineMeshCaps.measurableSet_meshBox 1 k).nullMeasurableSet,
    Submission.Lib.K4AffineMeshCaps.volume_meshBox (by norm_num)]
  norm_num

theorem assignedUnitCell_disjoint : Pairwise (fun k k' =>
    Disjoint (assignedUnitCell k) (assignedUnitCell k')) := by
  intro k k' hne
  exact (Submission.Lib.K4AffineMeshCaps.meshBox_pairwiseDisjoint 1 hne).preimage _

/-- A point in the assigned unit cell is within four units of the actual
base point divided by the coarse mesh. -/
theorem assignedUnitCell_dist_le {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) (hεp : ε ≤ p)
    (z : (EuclideanSpace ℝ (Fin 3))) (X : ℝ) (k : Fin 3 → ℤ)
    (hcode : stateAssignedBase ε p ((fun i => ⌊z i/ε⌋), ⌊X/ε⌋) = k)
    (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∈ assignedUnitCell k) :
    dist x (p⁻¹ • z) ≤ 4 := by
  have hcoord (i : Fin 3) : |x i-(p⁻¹ • z) i| ≤ 2 := by
    have hc := Int.floor_eq_iff.mp (congrFun hcode i)
    have hx' := Int.floor_eq_iff.mp (congrFun hx i)
    change (k i : ℝ) ≤ x i/1 ∧ x i/1 < (k i : ℝ)+1 at hx'
    have hz := Submission.Obl.k4_horizontal_supercritical_three_projections.abs_sub_floor_mul_le (x := z i) hε
    change (k i : ℝ) ≤ (ε*(⌊z i/ε⌋ : ℝ))/p ∧
      (ε*(⌊z i/ε⌋ : ℝ))/p < (k i : ℝ)+1 at hc
    rw [le_div_iff₀ hp, div_lt_iff₀ hp] at hc
    rw [PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div, abs_le]
    obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
    simp only [div_one] at hx'
    have hzu : z i/p ≤ (k i : ℝ)+2 := (div_le_iff₀ hp).mpr (by nlinarith)
    have hzl : (k i : ℝ)-1 ≤ z i/p := (le_div_iff₀ hp).mpr (by nlinarith)
    constructor <;> linarith
  have hs : ‖x-p⁻¹ • z‖^2 ≤ 12 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (2 : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hcoord i)
        simpa only [sq_abs, PiLp.sub_apply] using h
      _ = _ := by norm_num
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x-p⁻¹ • z)]

end

end Submission.Obl.k4_physical_parent_potential_candidates
