-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.FrameExpansion, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/FrameExpansion.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/FrameExpansion.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepCoreMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFrameChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates

/-!
# Old packet base versus fine local core coordinates

Two incidences at old-packet base distance `d` have fine local core points at distance
at most `K^R (1 + 4κ + 6κ³N^{2δ₀L}) 2^{T_fine - T_old} d`. The time coordinate is
rescaled by the clock ratio; the planar coordinates pass through `Q_fine⁻¹ Q_old`
(norm `κ²N^{2δ₀L} 2^{T_fine-T_old}`) and the shear `Q_fine⁻¹(u_old - u_fine)`, which a
common line of both packets bounds by `2κ(1 + κ²N^{2δ₀L}) 2^{T_fine}`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open Analytic k4_stable_native_signal_oscillation

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem packetBase_apply_zero' (a : Fin p.C) (q : Event) :
    packetBase p a q 0 =
      (q.2 - (p.j a : ℝ) / (2 : ℝ) ^ p.T (p.lev a)) / ((2 : ℝ) ^ p.T (p.lev a))⁻¹ := by
  rw [← p.native_base_coordinates_eq_packetBase a q]
  rfl

theorem packetBase_apply_one' (a : Fin p.C) (q : Event) :
    packetBase p a q 1 = packetPosition (p.Q a) (p.c a) (p.u a) q.1 q.2 0 := by
  rw [← p.native_base_coordinates_eq_packetBase a q]
  rfl

theorem packetBase_apply_two' (a : Fin p.C) (q : Event) :
    packetBase p a q 2 = packetPosition (p.Q a) (p.c a) (p.u a) q.1 q.2 1 := by
  rw [← p.native_base_coordinates_eq_packetBase a q]
  rfl

/-- **Frame expansion.** -/
theorem Native.PathData.Valid.local_core_expansion
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (old b : Fin p.C) {K : ℝ} (hK : 0 ≤ K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3))
    (z z' : Event) {l₀ : ℕ × (Fin 6 → ℝ)} (hl₀b : l₀ ∈ p.A b) (hl₀o : l₀ ∈ p.A old) :
    ‖packetLocalCorePoint Nk B p b K R c z - packetLocalCorePoint Nk B p b K R c z'‖ ≤
      K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
        ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old))) *
        ‖packetBase p old z - packetBase p old z'‖ := by
  have hκ1 : 1 ≤ p.κ := hp.1
  have hκ0 : 0 ≤ p.κ := by linarith
  set Nf : ℝ := Nk ^ (2 * δ₀ * L) with hNf
  have hNf0 : 0 ≤ Nf := by rw [hNf]; positivity
  set tb : ℝ := (2 : ℝ) ^ p.T (p.lev b) with htb
  set tO : ℝ := (2 : ℝ) ^ p.T (p.lev old) with hto
  have htb0 : 0 < tb := by rw [htb]; positivity
  have hto0 : 0 < tO := by rw [hto]; positivity
  set Do := packetBase p old z - packetBase p old z' with hDo
  set τ := z.2 - z'.2 with hτ
  -- the old differences
  have hDo0 : Do 0 = tO * τ := by
    rw [hDo, PiLp.sub_apply, packetBase_apply_zero', packetBase_apply_zero']
    field_simp
    ring
  set Po : EuclideanSpace ℝ (Fin 2) :=
    packetPosition (p.Q old) (p.c old) (p.u old) z.1 z.2 -
      packetPosition (p.Q old) (p.c old) (p.u old) z'.1 z'.2 with hPo
  have hPo0 : Po 0 = Do 1 := by
    rw [hPo, hDo, PiLp.sub_apply, PiLp.sub_apply, packetBase_apply_one', packetBase_apply_one']
  have hPo1 : Po 1 = Do 2 := by
    rw [hPo, hDo, PiLp.sub_apply, PiLp.sub_apply, packetBase_apply_two', packetBase_apply_two']
  have hPoDo : ‖Po‖ ≤ ‖Do‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_two, Fin.sum_univ_three, hPo0, hPo1]
    nlinarith [sq_nonneg ‖Do 0‖]
  have hτDo : tO * |τ| ≤ ‖Do‖ := by
    have hh : |Do 0| ≤ ‖Do‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le Do 0
    rw [hDo0, abs_mul, abs_of_pos hto0] at hh
    exact hh
  -- operator bounds
  have hdetb : (p.Q b).det ≠ 0 := (hp.2.2.2.2.2.2.2 b).2.2.1
  have hdeto : (p.Q old).det ≠ 0 := (hp.2.2.2.2.2.2.2 old).2.2.1
  have hQbinv (w : EuclideanSpace ℝ (Fin 2)) :
      ‖Matrix.toEuclideanLin (p.Q b)⁻¹ w‖ ≤ tb * (p.κ * Nf * ‖w‖) := by
    have hh := hp.normalized_frame_operator_bound hN b w
    change ‖tb⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ w‖ ≤ p.κ * Nf * ‖w‖ at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htb0)] at hh
    calc
      _ = tb * (tb⁻¹ * ‖Matrix.toEuclideanLin (p.Q b)⁻¹ w‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh htb0.le
  have hQo (w : EuclideanSpace ℝ (Fin 2)) :
      ‖Matrix.toEuclideanLin (p.Q old) w‖ ≤ tO⁻¹ * (p.κ * ‖w‖) := by
    have hh := hp.denormalized_frame_operator_bound old w
    change ‖tO • Matrix.toEuclideanLin (p.Q old) w‖ ≤ p.κ * ‖w‖ at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hto0] at hh
    calc
      _ = tO⁻¹ * (tO * ‖Matrix.toEuclideanLin (p.Q old) w‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hto0).le
  have hvb : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (v l₀ - p.u b)‖ ≤ tb * (2 * p.κ) := by
    have hh := hp.normalized_velocity_bound b l₀ hl₀b
    change ‖tb⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ (v l₀ - p.u b)‖ ≤ 2 * p.κ at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htb0)] at hh
    calc
      _ = tb * (tb⁻¹ * ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (v l₀ - p.u b)‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh htb0.le
  have hvo : ‖Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)‖ ≤ tO * (2 * p.κ) := by
    have hh := hp.normalized_velocity_bound old l₀ hl₀o
    change ‖tO⁻¹ • Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)‖ ≤ 2 * p.κ at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hto0)] at hh
    calc
      _ = tO * (tO⁻¹ * ‖Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hto0.le
  -- the shear
  have hshear : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (p.u old - p.u b)‖ ≤
      tb * (2 * p.κ + 2 * p.κ ^ 3 * Nf) := by
    have hsplit : p.u old - p.u b = (v l₀ - p.u b) -
        Matrix.toEuclideanLin (p.Q old) (Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)) := by
      rw [Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (p.Q old) hdeto]
      abel
    rw [hsplit, map_sub]
    have h2 : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (Matrix.toEuclideanLin (p.Q old)
        (Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)))‖ ≤ tb * (2 * p.κ ^ 3 * Nf) := by
      calc
        _ ≤ tb * (p.κ * Nf * ‖Matrix.toEuclideanLin (p.Q old)
            (Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old))‖) := hQbinv _
        _ ≤ tb * (p.κ * Nf * (tO⁻¹ * (p.κ * (tO * (2 * p.κ))))) := by
          gcongr
          exact (hQo _).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hvo hκ0) (inv_pos.mpr hto0).le)
        _ = tb * (2 * p.κ ^ 3 * Nf) := by field_simp
    calc
      _ ≤ ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (v l₀ - p.u b)‖ +
          ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (Matrix.toEuclideanLin (p.Q old)
            (Matrix.toEuclideanLin (p.Q old)⁻¹ (v l₀ - p.u old)))‖ := norm_sub_le _ _
      _ ≤ tb * (2 * p.κ) + tb * (2 * p.κ ^ 3 * Nf) := add_le_add hvb h2
      _ = _ := by ring
  -- the fine planar difference
  set Pb : EuclideanSpace ℝ (Fin 2) :=
    packetPosition (p.Q b) (p.c b) (p.u b) z.1 z.2 -
      packetPosition (p.Q b) (p.c b) (p.u b) z'.1 z'.2 with hPb
  have hPbeq : Pb = Matrix.toEuclideanLin (p.Q b)⁻¹ (Matrix.toEuclideanLin (p.Q old) Po) +
      τ • Matrix.toEuclideanLin (p.Q b)⁻¹ (p.u old - p.u b) := by
    have hpos (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) :
        packetPosition Q c u z.1 z.2 - packetPosition Q c u z'.1 z'.2 =
          Matrix.toEuclideanLin Q⁻¹ ((Submission.Lib.K4XInterface.gy z.1 z.2 -
            Submission.Lib.K4XInterface.gy z'.1 z'.2) - τ • u) := by
      simp only [packetPosition]
      rw [← map_sub]
      congr 1
      rw [hτ, sub_smul]
      abel
    have hcancel : Matrix.toEuclideanLin (p.Q old) Po =
        (Submission.Lib.K4XInterface.gy z.1 z.2 - Submission.Lib.K4XInterface.gy z'.1 z'.2) -
          τ • p.u old := by
      rw [hPo, hpos, Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (p.Q old) hdeto]
    have harg : (Submission.Lib.K4XInterface.gy z.1 z.2 -
        Submission.Lib.K4XInterface.gy z'.1 z'.2) - τ • p.u b =
        Matrix.toEuclideanLin (p.Q old) Po + τ • (p.u old - p.u b) := by
      rw [hcancel, smul_sub]
      abel
    rw [hPb, hpos, harg, map_add, map_smul]
  have hPbnorm : ‖Pb‖ ≤ tb * tO⁻¹ * (p.κ ^ 2 * Nf) * ‖Po‖ +
      tb * |τ| * (2 * p.κ + 2 * p.κ ^ 3 * Nf) := by
    rw [hPbeq]
    calc
      _ ≤ ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (Matrix.toEuclideanLin (p.Q old) Po)‖ +
          ‖τ • Matrix.toEuclideanLin (p.Q b)⁻¹ (p.u old - p.u b)‖ := norm_add_le _ _
      _ ≤ tb * (p.κ * Nf * (tO⁻¹ * (p.κ * ‖Po‖))) +
          |τ| * (tb * (2 * p.κ + 2 * p.κ ^ 3 * Nf)) := by
        gcongr
        · exact (hQbinv _).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hQo Po) (by positivity)) htb0.le)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hshear (abs_nonneg _)
      _ = _ := by ring
  -- the local core difference
  have hlocal : ‖packetLocalCorePoint Nk B p b K R c z - packetLocalCorePoint Nk B p b K R c z'‖ ≤
      K ^ R * (tb * |τ| + 2 * ‖Pb‖) := by
    have hcoord (q : Event) : packetLocalCorePoint Nk B p b K R c q =
        (K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c) := rfl
    rw [hcoord, hcoord, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hK R), packetNativeCube_base_coreUnitBase,
      packetNativeCube_base_coreUnitBase]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK R)
    have h6 : 1 ≤ 2 * (3 * p.κ) := by linarith
    have hd0 : |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
        (packetBase p b z) - Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b z')) 0| = tb * |τ| := by
      simp only [Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase,
        PiLp.sub_apply]
      change |packetBase p b z 0 - packetBase p b z' 0| = _
      rw [packetBase_apply_zero', packetBase_apply_zero']
      rw [show (z.2 - (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)) / ((2 : ℝ) ^ p.T (p.lev b))⁻¹ -
          (z'.2 - (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)) / ((2 : ℝ) ^ p.T (p.lev b))⁻¹ =
          tb * τ by rw [htb, hτ]; field_simp; ring]
      rw [abs_mul, abs_of_pos htb0]
    have hdj (j : Fin 2) : |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
        (3 * p.κ) (packetBase p b z) -
          Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
            (packetBase p b z')) j.succ| ≤ ‖Pb‖ := by
      have hPbj : |Pb j| ≤ ‖Pb‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le Pb j
      refine le_trans ?_ hPbj
      have hsucc : ∀ q : Event, (Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b q)) j.succ =
            (packetPosition (p.Q b) (p.c b) (p.u b) q.1 q.2 j + 3 * p.κ) / (2 * (3 * p.κ)) := by
        intro q
        fin_cases j
        · simp only [Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase]
          change (packetBase p b q 1 + 3 * p.κ) / (2 * (3 * p.κ)) = _
          rw [packetBase_apply_one']
          rfl
        · simp only [Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase]
          change (packetBase p b q 2 + 3 * p.κ) / (2 * (3 * p.κ)) = _
          rw [packetBase_apply_two']
          rfl
      rw [PiLp.sub_apply, hsucc, hsucc, ← sub_div, abs_div,
        abs_of_pos (show (0 : ℝ) < 2 * (3 * p.κ) by linarith), div_le_iff₀ (by linarith),
        hPb, PiLp.sub_apply]
      have hsub : packetPosition (p.Q b) (p.c b) (p.u b) z.1 z.2 j + 3 * p.κ -
          (packetPosition (p.Q b) (p.c b) (p.u b) z'.1 z'.2 j + 3 * p.κ) =
          packetPosition (p.Q b) (p.c b) (p.u b) z.1 z.2 j -
            packetPosition (p.Q b) (p.c b) (p.u b) z'.1 z'.2 j := by ring
      rw [hsub]
      nlinarith [abs_nonneg (packetPosition (p.Q b) (p.c b) (p.u b) z.1 z.2 j -
        packetPosition (p.Q b) (p.c b) (p.u b) z'.1 z'.2 j)]
    calc
      _ ≤ ∑ i : Fin 3, |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b z) -
            Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
              (packetBase p b z')) i| := euclidean_norm_le_sum_abs _
      _ = |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b z) -
            Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
              (packetBase p b z')) 0| +
          |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b z) -
            Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
              (packetBase p b z')) (0 : Fin 2).succ| +
          |(Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase
          (3 * p.κ) (packetBase p b z) -
            Submission.Lib.K4OriginalGeometricReference.Analytic.coreUnitBase (3 * p.κ)
              (packetBase p b z')) (1 : Fin 2).succ| := by
        rw [Fin.sum_univ_three]
        rfl
      _ ≤ tb * |τ| + ‖Pb‖ + ‖Pb‖ := by
        rw [hd0]
        exact add_le_add (add_le_add le_rfl (hdj 0)) (hdj 1)
      _ = _ := by ring
  -- combine
  have hτ' : |τ| ≤ tO⁻¹ * ‖Do‖ := by
    rw [le_inv_mul_iff₀ hto0]
    exact hτDo
  have hDo0' : 0 ≤ ‖Do‖ := norm_nonneg _
  have hratio : tb * tO⁻¹ = tb / tO := by rw [div_eq_mul_inv]
  calc
    _ ≤ K ^ R * (tb * |τ| + 2 * ‖Pb‖) := hlocal
    _ ≤ K ^ R * (tb * (tO⁻¹ * ‖Do‖) + 2 * (tb * tO⁻¹ * (p.κ ^ 2 * Nf) * ‖Do‖ +
        tb * (tO⁻¹ * ‖Do‖) * (2 * p.κ + 2 * p.κ ^ 3 * Nf))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK R)
      have h1 : tb * |τ| ≤ tb * (tO⁻¹ * ‖Do‖) := mul_le_mul_of_nonneg_left hτ' htb0.le
      have h2 : ‖Pb‖ ≤ tb * tO⁻¹ * (p.κ ^ 2 * Nf) * ‖Do‖ +
          tb * (tO⁻¹ * ‖Do‖) * (2 * p.κ + 2 * p.κ ^ 3 * Nf) := by
        refine hPbnorm.trans (add_le_add ?_ ?_)
        · exact mul_le_mul_of_nonneg_left hPoDo (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ' htb0.le)
            (by positivity)
      linarith
    _ = K ^ R * ((1 + 4 * p.κ + (2 * p.κ ^ 2 * Nf + 4 * p.κ ^ 3 * Nf)) * (tb / tO)) * ‖Do‖ := by
      rw [← hratio]; ring
    _ ≤ K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nf) * (tb / tO)) * ‖Do‖ := by
      apply mul_le_mul_of_nonneg_right _ hDo0'
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK R)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hκ23 : p.κ ^ 2 ≤ p.κ ^ 3 := pow_le_pow_right₀ hκ1 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hκ23 hNf0]

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
