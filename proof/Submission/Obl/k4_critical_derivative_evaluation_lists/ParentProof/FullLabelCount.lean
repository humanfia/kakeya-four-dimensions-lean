/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FullLabelCount.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ContactBoxes
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.JointGrid
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/TrueLabelContactCount.lean`, `Submission/Obl/k4_finite_narrowness_path_improvement/TrueLabelJointCapCount.lean`
(commit 2d33b59a). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset MeasureTheory Set
open scoped ENNReal Classical

def baseGridCode (δ : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊q i / δ⌋

/-- Integrating the original finite caps on a whole common contact box,
using the full transverse H-squared width. -/
theorem original_contact_box_joint_cap
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (p : Fin 3 → ℝ)
    (m H K δ C : ℝ) (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hδH : δ ≤ H ^ 2) (hδ1 : 3 * δ ≤ 1)
    (hm : |m| ≤ 1) (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hpoint : ∀ y ∈ U, |point y 0 - m| ≤ H / 2 ∧
      |point y 1 - referenceZ p (point y 0)| ≤ 8 * K * H ∧
      |contactTransverse m p (point y)| ≤ 32 * K ^ 2 * H ^ 2)
    (hvalue : ∀ y ∈ U, |value y| ≤ K)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | baseGridCode δ (point y) = q ∧ ⌊value y⌋ = n} ≤
        ENNReal.ofReal (C * δ ^ 3)) :
    μ U ≤ ENNReal.ofReal (56623104 * C * K ^ 6 * H ^ 4) := by
  have hK0 : 0 ≤ K := by linarith
  have hδH' : δ ≤ H := hδH.trans (by nlinarith)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hcenter : |p 0 + m * p 2| ≤ 2 * K := by
    calc
      _ ≤ |p 0| + |m * p 2| := abs_add_le _ _
      _ ≤ K + 1 * K := add_le_add hp₀ (by
        rw [abs_mul]
        exact mul_le_mul hm hp₂ (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  let c : Fin 3 → ℝ := ![p 1 - m * p 0, -(p 0 + m * p 2), m]
  have ht : ∀ y ∈ U, point y 0 ∈ Icc (m - H / 2) (m - H / 2 + 32 * K * H) := by
    intro y hy
    have hh := abs_le.mp (hpoint y hy).1
    have hKH := mul_le_mul_of_nonneg_right hK hH.le
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hZ : ∀ y ∈ U, point y 1 ∈
      Icc (referenceZ p m - 16 * K * H) (referenceZ p m - 16 * K * H + 32 * K * H) := by
    intro y hy
    have herr : |point y 1 - referenceZ p m| ≤ 9 * K * H := by
      have htime : |point y 0 - m| ≤ H := (hpoint y hy).1.trans (by linarith)
      calc
        _ = |(point y 1 - referenceZ p (point y 0)) + (point y 0 - m) * p 2| := by
          unfold referenceZ
          congr 1
          ring
        _ ≤ |point y 1 - referenceZ p (point y 0)| + |(point y 0 - m) * p 2| := abs_add_le _ _
        _ ≤ 8 * K * H + H * K := add_le_add (hpoint y hy).2.1 (by
          rw [abs_mul]
          exact mul_le_mul htime hp₂ (abs_nonneg _) hH.le)
        _ = _ := by ring
    have hh := abs_le.mp herr
    have hKH : 0 ≤ K * H := by positivity
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have htrans : ∀ y ∈ U,
      |point y 2 - c 0 - c 1 * point y 0 - c 2 * point y 1| ≤ 32 * K ^ 2 * H ^ 2 := by
    intro y hy
    convert (hpoint y hy).2.2 using 1 <;>
      dsimp [c, contactTransverse, referenceZ, referenceY] <;> congr 1 <;> ring
  have hh := original_native_joint_cap_rectangle μ U point value (fun _ => (0 : ℤ)) 0
    δ 1 (32 * K * H) (32 * K ^ 2 * H ^ 2) (2 * K)
    (m - H / 2) (referenceZ p m - 16 * K * H) C 1 1 c (0 : Fin 4 → ℝ)
    hδ (by norm_num) (by linarith) hC (by norm_num)
    (by nlinarith only [hδH', mul_le_mul_of_nonneg_right hK hH.le, hH.le])
    (by nlinarith only [hδH, mul_le_mul_of_nonneg_right hK2 (sq_nonneg H), sq_nonneg H])
    hδ1 (by change |-(p 0 + m * p 2)| ≤ 2 * K; rwa [abs_neg]) (hm.trans (by linarith))
    (by intro e; simpa using (show 0 ≤ 2 * K by positivity)) ht hZ htrans
    (by intro y hy; simpa [affineBaseValue] using (hvalue y hy).trans (by linarith : K ≤ 2 * K))
    (by intro y hy; rfl) (by
      intro q n
      have hqn := hcap q n
      change μ {y | (fun e => ⌊point y e / δ⌋) = q ∧ ⌊value y⌋ = n} ≤
        ENNReal.ofReal (C * δ ^ 3) at hqn
      simpa only [div_one, and_true, mul_one] using hqn)
  have heq : 432 * C * (2 * K) ^ 2 * (32 * K * H) ^ 2 * (32 * K ^ 2 * H ^ 2) =
      56623104 * C * K ^ 6 * H ^ 4 := by ring
  simpa only [mul_one, heq] using hh

/-- Count contacted true labels using ORIGINAL full witnesses, including
parts already deleted from the current residual law. -/
theorem full_true_label_contact_count
    {Y I : Type*} [MeasurableSpace Y] [DecidableEq I]
    (μ : Measure Y) [IsFiniteMeasure μ] (point : Y → Fin 3 → ℝ) (value : Y → ℝ)
    (S : Finset I) (witness : I → Set Y) (c : I → Fin 5 → ℝ) (p : Fin 3 → ℝ)
    (m H K D a d δ C : ℝ) (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K)
    (ha : 0 < a) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hδH : δ ≤ H ^ 2) (hδ1 : 3 * δ ≤ 1)
    (hD : D ≤ H ^ 2) (hm : |m| ≤ 1) (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hdisj : (↑S : Set I).PairwiseDisjoint witness)
    (hmeas : ∀ i ∈ S, MeasurableSet (witness i))
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (H ^ 4 * a ^ d / K) ≤ μ (witness i))
    (hvalue : ∀ i ∈ S, ∀ y ∈ witness i, |value y| ≤ K)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | baseGridCode δ (point y) = q ∧ ⌊value y⌋ = n} ≤
        ENNReal.ofReal (C * δ ^ 3))
    (hpoint : ∀ i ∈ S, ∀ y ∈ witness i, point y ∈ horizontalTrueBox (c i) m H K)
    (hc : ∀ i ∈ S, |c i 1| ≤ K)
    (hcenter : ∀ i ∈ S, |c i 3 + c i 0 + m * c i 1| ≤ K * H)
    (htilt : ∀ i ∈ S, |c i 4 - m| ≤ K * H)
    (hcontact : ∀ i ∈ S, ∃ q ∈ horizontalTrueBox (c i) m H K,
      |q 1 - referenceZ p (q 0)| ≤ K * D ∧ |q 2 - referenceY p (q 0)| ≤ K * D) :
    (S.card : ℝ) ≤ 56623104 * C * K ^ 7 / a ^ d := by
  have hKpos : 0 < K := by linarith
  have had : 0 < a ^ d := Real.rpow_pos_of_pos ha _
  let U := ⋃ i ∈ S, witness i
  have hsub (i : I) (hi : i ∈ S) : witness i ⊆ U := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
  have hmass : μ U ≤ ENNReal.ofReal (56623104 * C * K ^ 6 * H ^ 4) := by
    apply original_contact_box_joint_cap μ U point value p m H K δ C hH hH1 hK
      hδ hC hδH hδ1 hm hp₀ hp₂
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨q, hq, hqZ, hqY⟩ := hcontact i hi
      exact ⟨(hpoint i hi y hyi).1,
        horizontalTrueBox_common_contact (c i) p q m H K D hH hH1 hK hD hm
          (hc i hi) hp₂ (hcenter i hi) (htilt i hi) hq hqZ hqY
          (point y) (hpoint i hi y hyi)⟩
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
      exact hvalue i hi y hyi
    · exact hcap
  have hmassreal : μ.real U ≤ 56623104 * C * K ^ 6 * H ^ 4 := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    simpa only [measureReal_def, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ 56623104 * C * K ^ 6 * H ^ 4)] using hr
  have hθ : 0 < H ^ 4 * a ^ d / K := by positivity
  have hcount := Submission.Lib.K4FinitePlankAtlases.old_cell_count (μ.restrict U) S witness
    hdisj hmeas hθ (by
      intro i hi
      rw [measureReal_restrict_apply (hmeas i hi), Set.inter_eq_left.mpr (hsub i hi)]
      have hr := ENNReal.toReal_mono (measure_ne_top μ _) (hfloor i hi)
      simpa only [measureReal_def, ENNReal.toReal_ofReal hθ.le] using hr)
  rw [measureReal_restrict_apply_univ] at hcount
  refine hcount.trans ((div_le_div_of_nonneg_right hmassreal hθ.le).trans_eq ?_)
  field_simp [hH.ne', hKpos.ne', had.ne']

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
