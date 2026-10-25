/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ScalarGoodCrop.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_general_parent_projected_layers.Support.NativeScalar
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldRepresentatives
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! A measurable original-label crop sufficient for all scalar coefficient bounds. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial

noncomputable section

local instance scalarGoodCropPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

def scalarGoodLabels (a : PreparedModel α) (p : Parameters) (k : ℕ) : Set α :=
  {l | |a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k ∧
    |eval (a.x k l 0) (a.P k)| ≤ p.K k ∧
    |eval (a.x k l (1 / 2)) (a.P k)| ≤ p.K k ∧
    |eval (a.x k l 1) (a.P k)| ≤ p.K k}

theorem measurableSet_scalarGoodLabels (a : PreparedModel α) (p : Parameters) (k : ℕ)
    (hb : Measurable (a.b k)) : MeasurableSet (a.scalarGoodLabels p k) := by
  have hx (t : ℝ) : Measurable (fun l => a.x k l t) := by
    unfold x Submission.Lib.K4ContactNormalization.point
    fun_prop
  have heval (t : ℝ) : Measurable (fun l => |eval (a.x k l t) (a.P k)|) :=
    ((a.P k).continuous_eval.measurable.comp (hx t)).abs
  have he (i : Fin 6) : Measurable (fun l => a.b k l i) :=
    (measurable_pi_apply i).comp hb
  have hbase : MeasurableSet {l | |a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k} :=
    measurableSet_le ((((he 0).abs.add (he 1).abs).add (he 3).abs).add (he 4).abs) measurable_const
  exact hbase.inter ((measurableSet_le (heval 0) measurable_const).inter
    ((measurableSet_le (heval (1 / 2)) measurable_const).inter
      (measurableSet_le (heval 1) measurable_const)))

theorem ae_scalarGoodLabels (a : PreparedModel α) (p : Parameters)
    (hcommon : a.Common p) (k : ℕ) : ∀ᵐ z ∂a.mu k, z.1 ∈ a.scalarGoodLabels p k := by
  rcases hcommon k with ⟨_hbmeas, hnu, _hpi, hdom, _hrho, _hsupp, _hmass, _hPdeg, hb, hP⟩
  letI := hnu
  have hbprod : ∀ᵐ (z : α × ℝ) ∂(a.nu k).prod volume,
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k :=
    (Measure.quasiMeasurePreserving_fst (μ := a.nu k) (ν := (volume : Measure ℝ))).ae hb
  have hbmu := (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hbprod
  filter_upwards [hbmu, hP] with z hz hzs
  exact ⟨hz, (hzs.1 0 (by norm_num)).1, (hzs.1 (1 / 2) (by norm_num)).1,
    (hzs.1 1 (by norm_num)).1⟩

theorem scalarGoodLabels_samples (a : PreparedModel α) (p : Parameters) (k : ℕ)
    {l : α} (hl : l ∈ a.scalarGoodLabels p k) :
    ∀ t ∈ ({0, 1 / 2, 1} : Finset ℝ), |eval (a.x k l t) (a.P k)| ≤ p.K k := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact hl.2.1
  · exact hl.2.2.1
  · exact hl.2.2.2

theorem scalar_world_coefficient_bound (a : PreparedModel α) (p : Parameters)
    (hp : p.Valid) (k : ℕ) {chi g : ℝ} (hc : 0 < chi) (hg : 0 < g)
    (q : Fin 4 → ℤ) (l : α) (i : Fin 5) :
    |nativeScalarCoefficients (a.P k) (a.b k) g
      (projectedWorldRepresentatives (p.K k) chi g q 2)
      (projectedWorldRepresentatives (p.K k) chi g q 3)
      (projectedWorldCrop (a.scalarGoodLabels p k) (a.b k) chi g q) l i| ≤ 8 * p.K k := by
  apply nativeScalarCoefficients_bound _ _ hg (by linarith [hp.2.2.1.1 k])
  · intro l hl
    have h := projectedWorldRepresentatives_gap hc hg (a.b k l) hl.1.1 hl.2
    exact ⟨h.2.1.trans (by simpa using mul_le_mul_of_nonneg_right (hp.2.2.1.1 k) hg.le),
      h.2.2.trans (by simpa using mul_le_mul_of_nonneg_right (hp.2.2.1.1 k) hg.le)⟩
  · intro l hl
    exact a.scalarGoodLabels_samples p k hl.1

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
