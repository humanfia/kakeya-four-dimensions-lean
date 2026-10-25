-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MultiscaleCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/MultiscaleCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/MultiscaleCensus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockGridSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentPowerOriginalSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- A finite depth grid brackets every requested height. Only the ratio
between adjacent depths matters; no monotonicity of the grid is needed. -/
theorem exists_adjacent_height_scale (n : ℕ) (ratio : ℕ → ℝ)
    {M B height : ℝ} (hM : 0 ≤ M)
    (hstart : height < M*ratio 0) (hend : M*ratio n ≤ height)
    (hstep : ∀ j<n, ratio j ≤ B*ratio (j+1)) :
    ∃ j<n, M*ratio (j+1) ≤ height ∧ height < M*B*ratio (j+1) := by
  induction n with
  | zero => exact (not_lt_of_ge hend hstart).elim
  | succ n ih =>
    by_cases hmiddle : M*ratio n ≤ height
    · obtain ⟨j,hj,hlo,hhi⟩ := ih hmiddle (fun j hj => hstep j (by omega))
      exact ⟨j,by omega,hlo,hhi⟩
    · refine ⟨n,by omega,hend,?_⟩
      exact (lt_of_not_ge hmiddle).trans_le (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hstep n (by omega)) hM)

/-- Menus at finitely many actual depths supply the literal independent
base/height census at every admissible mesh. The census envelope can be
larger than the gradient envelope, so adjacent-depth gaps need not be paid
by the small envelope used for gradient deletion. -/
theorem parent_joint_census_from_depth_menus
    {Ω : Type*} (source : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {K Kcensus θ dimension fineMesh : ℝ} {gradientPower gapPower R : ℕ}
    (hK : 2304 ≤ K) (hθ : 0 < θ) (hθK : θ ≤ Kcensus)
    (hbudget : K^(3*R+gradientPower+gapPower+83) ≤ Kcensus)
    (hFine : 0 < fineMesh)
    (n : ℕ) (ratio : ℕ → ℝ) (hratio : ∀ j≤n, 0 < ratio j)
    (hzero : ratio 0=1)
    (hlast : K^(gradientPower+10)*ratio n ≤ fineMesh)
    (hstep : ∀ j<n, ratio j ≤ K^gapPower*ratio (j+1))
    (hmenu : ∀ j<n, ∀ base hidden : ℝ, 0 < base → 0 < hidden →
      K^(gradientPower+10)*ratio (j+1) ≤ hidden →
      K^(gradientPower+12)*base ≤ θ*hidden →
      base ≤ ratio (j+1) → hidden ≤ K^(gradientPower+10+gapPower)*ratio (j+1) →
      ∃ S : Finset (Fin 4 → ℤ),
        (S.card:ℝ) ≤ K^(3*R+gradientPower+gapPower+83)/(base^3*hidden^dimension) ∧
        ∀ x∈source, jointCode base hidden (z x) (X x)∈S) :
    ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kcensus^(100:ℕ)*base ≤ θ*hidden →
      (occupied source z X base hidden).Finite ∧
        ((occupied source z X base hidden).ncard:ℝ) ≤ Kcensus/(base^3*hidden^dimension) := by
  classical
  have hK1 : 1 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hC1 : 1 ≤ Kcensus := (one_le_pow₀ hK1).trans hbudget
  have hCp : 0 < Kcensus := zero_lt_one.trans_le hC1
  have hC100 : Kcensus ≤ Kcensus^(100:ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hC1 (by norm_num : (1:ℕ) ≤ 100)
  have hC99 : Kcensus ≤ Kcensus^(99:ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hC1 (by norm_num : (1:ℕ) ≤ 99)
  have hhiddenPower : K^(gradientPower+10+gapPower) ≤ Kcensus :=
    (pow_le_pow_right₀ hK1 (by omega)).trans hbudget
  have hphysicalPower : K^(gradientPower+12) ≤ Kcensus^(100:ℕ) :=
    ((pow_le_pow_right₀ hK1 (by omega)).trans hbudget).trans hC100
  intro base hidden hbase hbase1 hhidden hhidden1 hshape
  have hb : 0 < base := hFine.trans_le hbase
  have hw : 0 < hidden := hFine.trans_le hhidden
  have hstart : hidden < K^(gradientPower+10)*ratio 0 := by
    rw [hzero,mul_one]
    exact hhidden1.trans_lt (one_lt_pow₀ (by linarith : 1 < K) (by omega))
  obtain ⟨j,hj,hlo,hhi⟩ := exists_adjacent_height_scale n ratio
    (pow_nonneg hKp.le _) hstart (hlast.trans hhidden) hstep
  have hupper : hidden ≤ K^(gradientPower+10+gapPower)*ratio (j+1) := by
    simpa only [pow_add] using hhi.le
  have hphysical : K^(gradientPower+12)*base ≤ θ*hidden :=
    (mul_le_mul_of_nonneg_right hphysicalPower hb.le).trans hshape
  have hbaseUpper : base ≤ ratio (j+1) := by
    have hh : θ*hidden ≤ Kcensus^(100:ℕ)*ratio (j+1) := by
      calc
        θ*hidden ≤ Kcensus*hidden := mul_le_mul_of_nonneg_right hθK hw.le
        _ ≤ Kcensus*(K^(gradientPower+10+gapPower)*ratio (j+1)) :=
          mul_le_mul_of_nonneg_left hupper hCp.le
        _ ≤ Kcensus*(Kcensus^(99:ℕ)*ratio (j+1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hhiddenPower.trans hC99) (hratio (j+1) (by omega)).le) hCp.le
        _ = _ := by rw [show (100:ℕ)=99+1 from rfl,pow_succ]; ring
    exact (mul_le_mul_iff_right₀ (pow_pos hCp 100)).mp (hshape.trans hh)
  obtain ⟨S,hS,hcover⟩ := hmenu j hj base hidden hb hw hlo hphysical hbaseUpper hupper
  have hmap : ∀ q∈occupied source z X base hidden, flattenClockCode q∈(S:Set (Fin 4 → ℤ)) := by
    rintro q ⟨x,hx,rfl⟩
    exact hcover x hx
  have hfinite : (occupied source z X base hidden).Finite :=
    (S.finite_toSet.preimage flattenClockCode_injective.injOn).subset hmap
  have hcard : ((occupied source z X base hidden).ncard:ℝ) ≤ (S.card:ℝ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn flattenClockCode hmap
      flattenClockCode_injective.injOn S.finite_toSet
  refine ⟨hfinite,hcard.trans (hS.trans ?_)⟩
  exact div_le_div_of_nonneg_right hbudget (by positivity)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
