/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/PreparedParentNative.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ConditionalNativeLaw
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap
import Submission.Obl.k4_scalar_angular_pair_agreement.ChartGeometry
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! The exact prepared parent supplies the native simple-root hypotheses. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

def nativePoint (a : PreparedModel α) (k : ℕ) (z : α × ℝ) : NativePoint :=
  WithLp.toLp 2 (a.x k z.1 z.2)

theorem measurable_nativePoint (a : PreparedModel α) (k : ℕ)
    (hb : Measurable (a.b k)) : Measurable (a.nativePoint k) := by
  unfold nativePoint x Submission.Lib.K4ContactNormalization.point
  fun_prop

theorem nativePoint_base (a : PreparedModel α) (k : ℕ) (z : α × ℝ) :
    rootBaseCoordinates (a.nativePoint k z) = basePoint (a.b k z.1) z.2 := by
  ext i
  fin_cases i <;>
    simp [rootBaseCoordinates, erBase, nativePoint, x,
      Submission.Lib.K4ContactNormalization.point, basePoint,
      Submission.Lib.K4MovingMeshBoxes.basePoint]

theorem nativePoint_value (a : PreparedModel α) (k : ℕ) (z : α × ℝ)
    (P : MvPolynomial (Fin 4) ℝ) :
    value P (a.nativePoint k z) = eval (a.x k z.1 z.2) P := rfl

theorem interval_subset_unit (T : ℕ) (j : Fin (2 ^ T)) : interval T j ⊆ Icc 0 1 :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_subset_unit T j

def blockMid (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : ℝ :=
  Submission.Obl.k4_scalar_angular_pair_agreement.mid (a.T k s) (a.j k s i)

theorem block_distance_mid (a : PreparedModel α) (k : ℕ) (s : ℝ)
    (i : Fin (a.n k s)) {t : ℝ} (ht : t ∈ a.block k s i) :
    |t - a.blockMid k s i| ≤ a.q k s / 2 := by
  simpa only [blockMid, q, zpow_neg, zpow_natCast] using
    (Submission.Obl.k4_scalar_angular_pair_agreement.mem_I_iff_mid
      (a.T k s) (a.j k s i) t).mp ht

theorem nativePoint_base_norm (a : PreparedModel α) (k : ℕ) {z : α × ℝ}
    {K : ℝ} (hK : 1 ≤ K)
    (hb : |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ K)
    (ht : z.2 ∈ Icc 0 1) : ‖nativeBase (a.nativePoint k z)‖ ≤ 2 * K := by
  have ht' : |z.2| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hz : |a.b k z.1 0 + z.2 * a.b k z.1 3| ≤
      |a.b k z.1 0| + |a.b k z.1 3| := by
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht' (abs_nonneg (a.b k z.1 3))
  have hy : |a.b k z.1 1 + z.2 * a.b k z.1 4| ≤
      |a.b k z.1 1| + |a.b k z.1 4| := by
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht' (abs_nonneg (a.b k z.1 4))
  have hn := Submission.Obl.k4_scalar_coefficient_clustering.coeff_norm_le_abs_add
    (nativeBase (a.nativePoint k z))
  change ‖nativeBase (a.nativePoint k z)‖ ≤
    |z.2| + |a.b k z.1 0 + z.2 * a.b k z.1 3| +
      |a.b k z.1 1 + z.2 * a.b k z.1 4| at hn
  linarith

theorem ae_nativePoint_goodSet (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ}
    (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    ∀ᵐ z ∂a.mu k, z ∈ a.B k s i ×ˢ a.block k s i →
      a.nativePoint k z ∈ goodSet (2 * p.K k) (width p k s) (a.F k s i) (a.P k) := by
  rcases hcommon k with ⟨hbmeas, hnu, _hpi, hdom, _hrho, _hsupp, _hmass, hPdeg, hb, hP⟩
  have : IsProbabilityMeasure (a.nu k) := hnu
  have hbprod : ∀ᵐ (z : α × ℝ) ∂(a.nu k).prod volume,
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k :=
    (Measure.quasiMeasurePreserving_fst (μ := a.nu k) (ν := (volume : Measure ℝ))).ae hb
  have hbmu := (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hbprod
  rcases hatlas.2.2.2.2.1 i with ⟨_hfloor, _hceil, _hinc, _hc, hFdeg, _hpacket, hfit, hlower⟩
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 < p.K k := lt_of_lt_of_le zero_lt_one hK
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN0 _
  filter_upwards [hbmu, hP, hlower] with z hzb hzP hzF
  intro hz
  have ht : z.2 ∈ Icc (0 : ℝ) 1 := interval_subset_unit _ _ hz.2
  have hn := a.nativePoint_base_norm k hK hzb ht
  have hfits := hfit z.1 hz.1 z.2 hz.2
  have hlow := hzF hz.1 hz.2
  have hsig := hzP.1 z.2 ht
  have hlow' : (2 * p.K k)⁻¹ ≤ (p.K k)⁻¹ := inv_anti₀ hK0 (by linarith)
  have hcurvF : |curvature (a.F k s i) 3| ≤ p.K k / width p k s := by
    simpa only [second_pderiv_eq_curvature _ hFdeg, eval_C] using hfits.2.2
  have hcurvP : |curvature (a.P k) 3| ≤ p.K k := by
    simpa only [second_pderiv_eq_curvature _ hPdeg, eval_C] using hsig.2.2
  simp only [goodSet, mem_ofPred_eq]
  refine ⟨hn, ?_, hlow'.trans hlow, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfits.1.trans (by nlinarith)
  · exact hfits.2.1.trans (by linarith)
  · exact hcurvF.trans (div_le_div_of_nonneg_right (by linarith) ha.le)
  · exact hsig.1.trans (by linarith)
  · exact hsig.2.1.trans (by linarith)
  · exact hcurvP.trans (by linarith)

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
