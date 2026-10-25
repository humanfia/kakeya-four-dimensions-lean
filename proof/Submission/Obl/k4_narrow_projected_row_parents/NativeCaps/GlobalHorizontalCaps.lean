import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.HorizontalCaps
import Submission.Obl.k4_general_parent_projected_layers.Support.OriginalAssignmentBudget

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_narrow_projected_row_parents.PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem reference_weight_sum_le_one (p : Parameters) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {r : ℝ} (hatlas : a.AtlasAt p R k r) :
    (∑ i : Fin (a.n k r), ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) ≤ 1 := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hq : 0 ≤ a.q k r := (q_pos a k r).le
  calc (∑ i, ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i))
      = ∑ i, ENNReal.ofReal (a.q k r * (a.nu k (a.A k r i)).toReal) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ENNReal.ofReal (∑ i, a.q k r * (a.nu k (a.A k r i)).toReal) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun i hi => mul_nonneg hq ENNReal.toReal_nonneg
    _ ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (a.original_assignment_budget p hcommon hatlas)

/-- A single deletion of fixed-power small original mass makes every true
parent satisfy the horizontal joint cap at the requested fine mesh. -/
theorem eventually_global_horizontal_caps
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (ha : a.Valid p)
    {r t : ℝ} (hr : 0 < r) (hrU : r ≤ p.U) (ht : 0 < t) :
    ∀ᶠ k in atTop, ∃ Bad : Set (α × ℝ), MeasurableSet Bad ∧
      a.mu k Bad ≤ ENNReal.ofReal (p.N k ^ (-r / 2)) ∧
      ∀ (i : Fin (a.n k r)) (c : Fin 2 → ℤ) (j : ℤ),
        a.rho k {z | z ∈ a.B k r i ×ˢ a.block k r i ∧ z ∉ Bad ∧
            hcell (parentZoom p a k r i) (p.N k ^ (-t)) (a.b k z.1) z.2 = c ∧
            ⌊a.b k z.1 3 / p.N k ^ (-t)⌋ = j} ≤
          ENNReal.ofReal (horizontalParentConstant (p.K k) * (p.N k ^ (-t)) ^ 2) *
            a.pi k (Ico ((j : ℝ) * p.N k ^ (-t)) (((j : ℝ) + 1) * p.N k ^ (-t))) *
            (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) := by
  classical
  let R : ℝ := 2 + r + r⁻¹
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hri h
  have hfactor : ∀ᶠ k in atTop,
      p.K k * (parentFilling (p.K k) (width p k r))⁻¹ ≤ p.N k ^ (-r / 2) := by
    filter_upwards [hp.2.2.1.2 (r / 2) (by positivity)] with k hk
    have hN : 0 < p.N k := by linarith [hp.1 k]
    have hK : 0 ≤ p.K k := zero_le_one.trans (hp.2.2.1.1 k)
    have hInv : (parentFilling (p.K k) (width p k r))⁻¹ ≤ p.N k ^ (-r) := by
      have h := inv_anti₀ (Real.rpow_pos_of_pos hN r) (rpow_depth_le_parentFilling p hp k r)
      simpa only [Real.rpow_neg hN.le] using h
    calc p.K k * (parentFilling (p.K k) (width p k r))⁻¹ ≤ p.K k * p.N k ^ (-r) :=
          mul_le_mul_of_nonneg_left hInv hK
      _ ≤ p.N k ^ (r / 2) * p.N k ^ (-r) :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN.le _)
      _ = p.N k ^ (-r / 2) := by rw [← Real.rpow_add hN]; congr 1; ring
  filter_upwards [eventually_parent_horizontal_caps p hp a ha hr hrU ht,
    ha.2.2.1 R hR, hfactor] with k hk hAt hfac
  have hA : a.AtlasAt p R k r := hAt r hRr hrU
  choose G hGm hGsub hloss hcap using hk
  let Bad : Set (α × ℝ) := ⋃ i : Fin (a.n k r), (a.B k r i ×ˢ a.block k r i) \ G i
  have hBad : MeasurableSet Bad := MeasurableSet.iUnion fun i =>
    ((hA.2.2.1 i).2.1.prod measurableSet_Icc).diff (hGm i)
  refine ⟨Bad, hBad, ?_, ?_⟩
  · calc a.mu k Bad ≤ ∑ i : Fin (a.n k r), a.mu k ((a.B k r i ×ˢ a.block k r i) \ G i) := by
          simpa only [Bad, tsum_fintype] using measure_iUnion_le
            (μ := a.mu k) (fun i : Fin (a.n k r) => (a.B k r i ×ˢ a.block k r i) \ G i)
      _ ≤ ∑ i : Fin (a.n k r),
          ENNReal.ofReal (p.K k * (parentFilling (p.K k) (width p k r))⁻¹) *
            (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) :=
        Finset.sum_le_sum fun i hi => hloss i
      _ = ENNReal.ofReal (p.K k * (parentFilling (p.K k) (width p k r))⁻¹) *
          ∑ i : Fin (a.n k r), ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i) :=
        (Finset.mul_sum ..).symm
      _ ≤ ENNReal.ofReal (p.K k * (parentFilling (p.K k) (width p k r))⁻¹) * 1 :=
        mul_le_mul_right (reference_weight_sum_le_one p a ha.1 hA) _
      _ ≤ ENNReal.ofReal (p.N k ^ (-r / 2)) := by
        simpa only [mul_one] using ENNReal.ofReal_le_ofReal hfac
  · intro i c j
    apply le_trans _ (hcap i c j)
    apply measure_mono
    rintro z ⟨hzparent, hzbad, hzcell, hzbin⟩
    have hzG : z ∈ G i := by
      by_contra hn
      apply hzbad
      exact mem_iUnion.mpr ⟨i, hzparent, hn⟩
    exact ⟨hzG, hzcell, hzbin⟩

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
