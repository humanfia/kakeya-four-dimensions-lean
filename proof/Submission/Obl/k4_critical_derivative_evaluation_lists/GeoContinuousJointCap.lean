import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoFiniteJointCap
import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoFiniteCodeTransport
import Submission.Lib.K4ContinuousPlanks.Discretization

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/ContinuousJointCap.lean (namespace and imports renamed only). -/

/-! Integrate original joint cell caps directly in a continuous source law.
Finite exact source codes are used only to count cells, never to replace time. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

theorem finite_joint_grid_codes_on_bounded_set
    {Y Pal : Type*} (U : Set Y) (point : Y → Fin 3 → ℝ) (value : Y → ℝ)
    (velocity : Y → Pal) (z : Pal) (δ a R Q : ℝ) (hδ : 0 < δ) (ha : 0 < a)
    (hpoint : ∀ y ∈ U, ∀ i, |point y i| ≤ R) (hvalue : ∀ y ∈ U, |value y| ≤ Q)
    (hvelocity : ∀ y ∈ U, velocity y = z) :
    ((fun y => ((baseGridCode δ (point y), ⌊value y / a⌋), velocity y)) '' U).Finite := by
  have hbaseRange := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun y : U => point y) R (fun y i => hpoint y y.property i) hδ
  have hbase : ((fun y => baseGridCode δ (point y)) '' U).Finite :=
    hbaseRange.subset (by rintro _ ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩)
  have hvalueRange := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun y : U => fun _ : Fin 1 => value y) Q (fun y _ => hvalue y y.property) ha
  have hval : ((fun y => ⌊value y / a⌋) '' U).Finite :=
    (hvalueRange.image (fun q => q 0)).subset (by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨(fun _ : Fin 1 => ⌊value y / a⌋), ⟨⟨y, hy⟩, rfl⟩, rfl⟩)
  apply ((hbase.prod hval).image (fun q => (q, z))).subset
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨(baseGridCode δ (point y), ⌊value y / a⌋),
    ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, ?_⟩
  exact Prod.ext rfl (hvelocity y hy).symm

/-- A whole contact rectangle and one affine hidden band have finite joint
grid range. Absolute intercepts affect finiteness only, never the cell count. -/
theorem contact_rectangle_affine_grid_codes_finite
    {Y Pal : Type*} (U : Set Y) (point : Y → Fin 3 → ℝ) (value : Y → ℝ)
    (velocity : Y → Pal) (z : Pal) (T : Fin 4 → ℝ) (p : Fin 3 → ℝ)
    (m H A B K M δ a : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hδ : 0 < δ) (ha : 0 < a)
    (hT : ∀ i : Fin 3, |T i.succ| ≤ M)
    (hpoint : ∀ y ∈ U, point y ∈ contactOuterBox m p H A B)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval T (point y)| ≤ 2 * K * a)
    (hvelocity : ∀ y ∈ U, velocity y = z) :
    ((fun y => ((baseGridCode δ (point y), ⌊value y / a⌋), velocity y)) '' U).Finite := by
  let Rt := |m| + H
  let Rz := A + |p 0| + Rt * |p 2|
  let Ry := B + |p 1| + Rt * |p 0| + |m| * A
  let R := Rt + Rz + Ry
  have hRt : 0 ≤ Rt := by dsimp [Rt]; positivity
  have hRz : 0 ≤ Rz := by dsimp [Rz]; positivity
  have hRy : 0 ≤ Ry := by dsimp [Ry]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoords : ∀ y ∈ U, ∀ i, |point y i| ≤ R := by
    intro y hy
    let q := point y
    have hq := (mem_contactOuterBox_iff _ _ _ _ _ _).mp (hpoint y hy)
    have ht : |q 0| ≤ Rt := by
      calc
        _ = |(q 0 - m) + m| := by congr 1; ring
        _ ≤ |q 0 - m| + |m| := abs_add_le _ _
        _ ≤ _ := by dsimp [Rt]; linarith [hq.1]
    have hz : |q 1| ≤ Rz := by
      calc
        _ = |(q 1 - referenceZ p (q 0)) + (p 0 + q 0 * p 2)| := by
          unfold referenceZ; congr 1; ring
        _ ≤ |q 1 - referenceZ p (q 0)| + (|p 0| + |q 0 * p 2|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
        _ ≤ A + (|p 0| + Rt * |p 2|) := by
          apply add_le_add hq.2.1 (add_le_add le_rfl ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        _ = _ := by dsimp [Rz]; ring
    have hyy : |q 2| ≤ Ry := by
      have href : |referenceY p (q 0)| ≤ |p 1| + Rt * |p 0| := by
        unfold referenceY
        exact (abs_sub _ _).trans (add_le_add le_rfl (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)))
      have hmult : |m * (q 1 - referenceZ p (q 0))| ≤ |m| * A := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hq.2.1 (abs_nonneg _)
      calc
        _ = |contactTransverse m p q + referenceY p (q 0) +
          m * (q 1 - referenceZ p (q 0))| := by unfold contactTransverse; congr 1; ring
        _ ≤ |contactTransverse m p q| + |referenceY p (q 0)| +
          |m * (q 1 - referenceZ p (q 0))| := abs_add_three _ _ _
        _ ≤ B + (|p 1| + Rt * |p 0|) + |m| * A := add_le_add (add_le_add hq.2.2 href) hmult
        _ = _ := by dsimp [Ry]; ring
    intro i
    fin_cases i
    · change |q 0| ≤ R
      dsimp [R]
      linarith
    · change |q 1| ≤ R
      dsimp [R]
      linarith
    · change |q 2| ≤ R
      dsimp [R]
      linarith
  have hval : ∀ y ∈ U, |value y| ≤ 2 * K * a + (|T 0| + 3 * M * R) := by
    intro y hy
    have hprod (i : Fin 3) : |T i.succ * point y i| ≤ M * R := by
      rw [abs_mul]
      exact mul_le_mul (hT i) (hcoords y hy i) (abs_nonneg _) hM
    have hAffine : |affineBaseEval T (point y)| ≤ |T 0| + 3 * M * R := by
      unfold affineBaseEval
      calc
        _ ≤ ((|T 0| + |T 1 * point y 0|) + |T 2 * point y 1|) + |T 3 * point y 2| :=
          (abs_add_le _ _).trans
            (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
        _ ≤ ((|T 0| + M * R) + M * R) + M * R := by
          exact add_le_add (add_le_add (add_le_add le_rfl (hprod 0)) (hprod 1)) (hprod 2)
        _ = _ := by ring
    calc
      _ = |(value y - affineBaseEval T (point y)) + affineBaseEval T (point y)| := by congr 1; ring
      _ ≤ |value y - affineBaseEval T (point y)| + |affineBaseEval T (point y)| := abs_add_le _ _
      _ ≤ _ := add_le_add (hfit y hy) hAffine
  exact finite_joint_grid_codes_on_bounded_set U point value velocity z δ a R
    (2 * K * a + (|T 0| + 3 * M * R)) hδ ha hcoords hval hvelocity

/-- Original continuous joint caps integrate over a contact rectangle and
an affine hidden band, retaining the unchanged palette-bin factor. -/
theorem original_joint_cap_contact_rectangle
    {Y Pal : Type*} [MeasurableSpace Y] [MeasurableSpace Pal]
    [MeasurableSingletonClass Pal] [DecidableEq Pal]
    (μ : Measure Y) [IsFiniteMeasure μ] (U : Set Y) (hU : MeasurableSet U)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (velocity : Y → Pal) (z : Pal)
    (hpointm : Measurable point) (hvaluem : Measurable value) (hvelocitym : Measurable velocity)
    (T : Fin 4 → ℝ) (p : Fin 3 → ℝ) (m H A B K M δ a C Z πz : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hπ : 0 ≤ πz)
    (hδ : 0 < δ) (ha : 0 < a) (hδH : δ ≤ H / 2)
    (hδA : 2 * K * δ ≤ A) (hδB : 3 * K * δ ≤ B)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (hT : ∀ i : Fin 3, |T i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ y ∈ U, point y ∈ contactOuterBox m p H A B)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval T (point y)| ≤ 2 * K * a)
    (hvelocity : ∀ y ∈ U, velocity y = z)
    (hcap : ∀ (j : Fin 3 → ℤ) (n : ℤ),
      μ {y | baseGridCode δ (point y) = j ∧ ⌊value y / a⌋ = n ∧ velocity y = z} ≤
        ENNReal.ofReal (C * δ ^ 3 * Z * πz)) :
    μ U ≤ ENNReal.ofReal (8192 * C * K * H * A * B * Z * πz) := by
  by_cases hSne : U.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hSne, measure_empty]
    exact zero_le
  let joint := fun y => ((baseGridCode δ (point y), ⌊value y / a⌋), velocity y)
  have hfinite := contact_rectangle_affine_grid_codes_finite U point value velocity z T p
    m H A B K M δ a hH hA hB hM hδ ha hT hpoint hfit hvelocity
  have hbase : Measurable (fun y => baseGridCode δ (point y)) := by
    apply Measurable.of_eval
    intro i
    exact Int.measurable_floor.comp (((measurable_pi_apply i).comp hpointm).div_const δ)
  have hjoint : Measurable joint :=
    (hbase.prodMk (Int.measurable_floor.comp (hvaluem.div_const a))).prodMk hvelocitym
  obtain ⟨n, hn, code, decode, hcode, hdecode, hrepr⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_on
      U hU hSne joint hjoint hfinite
  let rep : Fin n → Y := fun i => Classical.choose (hrepr i)
  have hrep (i : Fin n) : rep i ∈ U ∧ joint (rep i) = decode i :=
    Classical.choose_spec (hrepr i)
  let μ' := μ.restrict U
  let P : Fin n → ℝ := fun i => μ'.real (code ⁻¹' {i})
  let point' := fun i => point (rep i)
  let value' := fun i => value (rep i)
  let velocity' := fun i => velocity (rep i)
  have hcompat : ∀ᵐ y ∂μ',
      ((baseGridCode δ (point' (code y)), ⌊value' (code y) / a⌋), velocity' (code y)) = joint y := by
    filter_upwards [ae_restrict_mem hU] with y hy
    exact (hrep (code y)).2.trans (hdecode y hy)
  have hcap' (j : Fin 3 → ℤ) (b : ℤ) :
      fiberMass P (fun i => ((baseGridCode δ (point' i), ⌊value' i / a⌋), velocity' i)) ((j, b), z) ≤
        C * δ ^ 3 * Z * πz := by
    rw [finite_code_fiber_mass_ae μ' code hcode _ joint hcompat]
    have hbound : μ' {y | joint y = ((j, b), z)} ≤ ENNReal.ofReal (C * δ ^ 3 * Z * πz) := by
      calc
        _ ≤ μ {y | joint y = ((j, b), z)} := Measure.restrict_le_self _
        _ = μ {y | baseGridCode δ (point y) = j ∧ ⌊value y / a⌋ = b ∧ velocity y = z} := by
          congr 1
          ext y
          simp only [joint, Prod.mk.injEq, Set.mem_ofPred_eq]
          tauto
        _ ≤ _ := hcap j b
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ C * δ ^ 3 * Z * πz)] using hreal
  have hmass := finite_joint_cap_contact_rectangle Finset.univ P point' value' velocity' z T p
    m H A B K M δ a C Z πz (fun _ => ENNReal.toReal_nonneg)
    hH hA hB hK hM hC hZ hπ hδ ha hδH hδA hδB hm hv hcenter hT hmesh
    (fun i _ => hpoint _ (hrep i).1) (fun i _ => hfit _ (hrep i).1)
    (fun i _ => hvelocity _ (hrep i).1) hcap'
  have hsum : (∑ i, P i) = μ.real U := by
    have hh := Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass
      μ' code hcode Finset.univ
    simpa only [Submission.Obl.k4_matching_cofinal_palette_selection.atomMass,
      Finset.coe_univ, Set.preimage_univ, μ', measureReal_restrict_apply_univ] using hh
  rw [hsum] at hmass
  have hh := ENNReal.ofReal_le_ofReal hmass
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ U)] using hh

end

end Submission.Obl.k4_critical_derivative_evaluation_lists
