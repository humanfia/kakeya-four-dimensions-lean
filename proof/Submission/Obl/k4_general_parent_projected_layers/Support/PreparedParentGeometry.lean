/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/PreparedParentGeometry.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentNative
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! The original full parent incidence law in its normalized packet chart. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

def parentSet (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : Set (α × ℝ) :=
  a.B k s i ×ˢ a.block k s i

theorem measurableSet_parentSet (p : Parameters) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    MeasurableSet (a.parentSet k s i) :=
  ((hatlas.2.2.1 i).2.1).prod measurableSet_Icc

def parentNativeLaw (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    Measure NativePoint := conditionalNativeLaw (a.mu k) (a.parentSet k s i) (a.nativePoint k)

def parentSupportZoom (p : Parameters) (a : PreparedModel α) (k : ℕ) (s : ℝ)
    (i : Fin (a.n k s)) : Zoom :=
  supportZoom (p.K k) (a.q k s) (narrow p k s) (a.blockMid k s i)
    (a.c k s i 0 + a.blockMid k s i * a.c k s i 1) (a.c k s i)

theorem parentSupportZoom_ok (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : (a.parentSupportZoom p k s i).Ok := by
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hN : 0 < p.N k := by linarith [hp.1 k]
  exact supportZoom_ok hK (by unfold q; positivity) (Real.rpow_pos_of_pos hN _) _ _ _

theorem parentSupportZoom_hidden (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : (a.parentSupportZoom p k s i).a = 1 := rfl

theorem parentSupportZoom_jacobian (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    |(a.parentSupportZoom p k s i).baseMatrix.det|⁻¹ =
      16384 * p.K k ^ 3 * a.q k s ^ 3 * narrow p k s := by
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hN : 0 < p.N k := by linarith [hp.1 k]
  exact supportZoom_jacobian hK (by unfold q; positivity) (Real.rpow_pos_of_pos hN _) _ _ _

theorem parentSupportZoom_small (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s))
    {z : α × ℝ} (hz : z ∈ a.parentSet k s i) :
    rootBaseCoordinates ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) ∈
      Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) := by
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 < p.K k := lt_of_lt_of_le zero_lt_one hK
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k s := by unfold q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have ht := a.block_distance_mid k s i hz.2
  have htq : |z.2 - a.blockMid k s i| ≤ a.q k s := ht.trans (by linarith)
  have hlabel := hatlas.2.2.2.2.1 i
  have hpacket := hlabel.2.2.2.2.2.1 z.1 ((hatlas.2.2.1 i).2.2 hz.1) z.2 hz.2
  have hc1 : |a.c k s i 1| ≤ p.K k := hlabel.2.2.2.1 1
  apply supportZoom_small hK0 hq hg (a.c k s i) (a.nativePoint k z)
  · exact htq.trans (by nlinarith)
  · change |(a.x k z.1 z.2) 1 - (a.c k s i 0 + a.blockMid k s i * a.c k s i 1)| ≤ _
    calc
      _ = |((a.x k z.1 z.2) 1 - a.c k s i 0 - z.2 * a.c k s i 1) +
          (z.2 - a.blockMid k s i) * a.c k s i 1| := by congr 1; ring
      _ ≤ |(a.x k z.1 z.2) 1 - a.c k s i 0 - z.2 * a.c k s i 1| +
          |z.2 - a.blockMid k s i| * |a.c k s i 1| := by
        simpa only [abs_mul] using abs_add_le
          ((a.x k z.1 z.2) 1 - a.c k s i 0 - z.2 * a.c k s i 1)
          ((z.2 - a.blockMid k s i) * a.c k s i 1)
      _ ≤ p.K k * a.q k s + a.q k s * p.K k := add_le_add hpacket.1
        (mul_le_mul htq hc1 (abs_nonneg _) hq.le)
      _ = _ := by ring
  · change |(a.x k z.1 z.2) 2 - a.c k s i 2 - a.c k s i 3 * z.2 -
      a.c k s i 4 * (a.x k z.1 z.2) 1| ≤ _
    simpa only [mul_comm] using hpacket.2.1

theorem parentNativeLaw_probability (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) : IsProbabilityMeasure (a.parentNativeLaw k s i) := by
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  exact conditionalNativeLaw_probability _ _ _
    (a.original_parent_mass_pos p hp hatlas i).ne' (measure_ne_top _ _)

theorem parentNativeLaw_good (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) :
    ∀ᵐ z ∂a.parentNativeLaw k s i,
      z ∈ goodSet (2 * p.K k) (width p k s) (a.F k s i) (a.P k) :=
  conditionalNativeLaw_ae _ (a.measurableSet_parentSet p hatlas i) _
    (a.measurable_nativePoint k (hcommon k).1)
    (measurableSet_goodSet _ _ _ _) (a.ae_nativePoint_goodSet p hp hcommon hatlas i)

theorem parentNativeLaw_small (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) :
    ∀ᵐ z ∂a.parentNativeLaw k s i,
      rootBaseCoordinates ((a.parentSupportZoom p k s i).nativePoint z) ∈
        Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) := by
  apply conditionalNativeLaw_ae _ (a.measurableSet_parentSet p hatlas i) _
    (a.measurable_nativePoint k (hcommon k).1)
    (measurableSet_Icc.preimage
      (measurable_rootBaseCoordinates.comp (Zoom.measurable_nativePoint _)))
  exact Filter.Eventually.of_forall (fun z hz => a.parentSupportZoom_small p hp hatlas i hz)

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
