/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/TerminalMeshConditions.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMeshPowers
import Submission.Obl.k4_general_parent_projected_layers.Support.SupportMeshResolution
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentGeometry
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! One fixed projected mesh exponent works at every later output tolerance. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Filter

noncomputable section

def projectionMeshExponent (J C : ℕ) (kappa ell : ℝ) : ℝ :=
  8 * ((J : ℝ) + C + kappa + ell + 4)

theorem projectionMeshExponent_gt_two (J C : ℕ) {kappa ell : ℝ}
    (hk : 0 < kappa) (hl : 0 < ell) : 2 < projectionMeshExponent J C kappa ell := by
  unfold projectionMeshExponent
  nlinarith [Nat.cast_nonneg (α := ℝ) J, Nat.cast_nonneg (α := ℝ) C]

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

structure TerminalMeshConditions (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s r M m : ℝ) (J C : ℕ) : Prop where
  sigma_le_time : p.N k ^ (-M) ≤ a.q k s
  major_le_time : p.N k ^ (-m) ≤ a.q k s
  major_le_packet : p.N k ^ (-m) ≤ a.q k s * narrow p k s
  root_small : p.N k ^ (-M) ≤ (parentFilling (p.K k) (width p k s) ^ J)⁻¹
  resolution : ∀ i e,
    (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * p.N k ^ (-r)) ≤ p.N k ^ (-M)
  oscillation : parentFilling (p.K k) (width p k s) ^ C *
    (24 * p.K k ^ 2 * (p.N k ^ (-M) + p.N k ^ (-m)) / (a.q k s * narrow p k s)) ≤ width p k s

theorem eventually_terminal_mesh_conditions (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (J C : ℕ) {a₀ m : ℝ} (ha₀ : 0 < a₀)
    (hm : projectionMeshExponent J C p.kappa p.ell * a₀ < m) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∀ R s : ℝ, a₀ ≤ s → s ≤ 2 * a₀ →
      a.AtlasAt p R k s → a.TerminalMeshConditions p k s r
        (projectionMeshExponent J C p.kappa p.ell * a₀ / 2) m J C := by
  have hk : 0 < p.kappa := hp.2.2.2.2.2.1
  have hl : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  let L := projectionMeshExponent J C p.kappa p.ell
  let M := L * a₀ / 2
  let E := (2 * (p.kappa + p.ell) + 1) * a₀
  let r := M + E + a₀
  have hL : 2 < L := projectionMeshExponent_gt_two J C hk hl
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hLJ : 3 * (J : ℝ) ≤ L / 2 := by
    dsimp [L, projectionMeshExponent]
    nlinarith [Nat.cast_nonneg (α := ℝ) J, Nat.cast_nonneg (α := ℝ) C]
  have hLC : 3 * (C : ℝ) + 2 * p.kappa + 2 * p.ell + 6 ≤ L / 2 := by
    dsimp [L, projectionMeshExponent]
    nlinarith [Nat.cast_nonneg (α := ℝ) J, Nat.cast_nonneg (α := ℝ) C]
  have hLE : 2 * (p.kappa + p.ell) + 1 ≤ L / 2 := by
    dsimp [L, projectionMeshExponent]
    nlinarith [Nat.cast_nonneg (α := ℝ) J, Nat.cast_nonneg (α := ℝ) C]
  have hMJ : (3 * a₀) * J ≤ M := by
    have h := mul_le_mul_of_nonneg_right hLJ ha₀.le
    dsimp [M]
    nlinarith only [h]
  have hMC : (3 * a₀) * C + 3 * a₀ + E + 2 * a₀ ≤ M := by
    have h := mul_le_mul_of_nonneg_right hLC ha₀.le
    dsimp [M, E]
    nlinarith only [h]
  have hME : E ≤ M := by
    have h := mul_le_mul_of_nonneg_right hLE ha₀.le
    dsimp [M, E]
    nlinarith only [h]
  have hMm : M ≤ m := by
    have heq : 2 * M = L * a₀ := by dsimp [M]; ring
    nlinarith only [hm, hM, heq]
  have h48 : ∀ᶠ k in atTop, 48 ≤ p.N k ^ a₀ := by
    filter_upwards [Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      hp.2.1 (a := 0) (b := a₀) ha₀ 48] with k hk'
    simpa only [Real.rpow_zero, mul_one] using hk'.le
  refine ⟨r, by dsimp [r]; positivity, ?_⟩
  filter_upwards [eventually_parentFilling_le p hp ha₀, hp.2.2.1.2 a₀ ha₀,
    a.eventually_q_narrow_lower p hp (2 * a₀) ha₀, h48] with k hfill hKbound hqg hconst
  intro R s hslo hshi hatlas
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hq : 0 < a.q k s := by unfold q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hg1 : narrow p k s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1
    (by nlinarith [mul_nonneg hl.le (ha₀.le.trans hslo)])
  have hqg' : p.N k ^ (-E) ≤ a.q k s * narrow p k s := by
    convert hqg R s hatlas hshi using 1
    congr 1
    dsimp [E]
    ring
  have hσqg : p.N k ^ (-M) ≤ a.q k s * narrow p k s :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -M ≤ -E)).trans hqg'
  have hσq : p.N k ^ (-M) ≤ a.q k s := hσqg.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg1 hq.le)
  have hχσ : p.N k ^ (-m) ≤ p.N k ^ (-M) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hHpos : 0 < parentFilling (p.K k) (width p k s) := by
    unfold parentFilling width
    positivity
  have hHbound : parentFilling (p.K k) (width p k s) ≤ p.N k ^ (3 * a₀) :=
    (hfill s).trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  refine ⟨hσq, hχσ.trans hσq, hχσ.trans hσqg,
    mesh_le_inverse_filling_power hN1 hHpos hHbound hMJ, ?_, ?_⟩
  · intro i e
    have hlabel := hatlas.2.2.2.2.1 i
    have hrow := supportZoom_mesh_resolution hK hq hg hg1
      (Real.rpow_nonneg hN.le (-r)) (a.blockMid k s i)
      (a.c k s i 0 + a.blockMid k s i * a.c k s i 1) (a.c k s i)
      (hlabel.2.2.2.1 3) (hlabel.2.2.2.1 4) e
    exact hrow.trans (physical_mesh_over_packet hN1 hqg' (by dsimp [r, M, L]; linarith))
  · exact (native_oscillation_mesh_bound hN1 hHpos.le (by linarith) hHbound hKbound
      hconst hχσ hqg' hMC).trans
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -(2 * a₀) ≤ -s))

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
