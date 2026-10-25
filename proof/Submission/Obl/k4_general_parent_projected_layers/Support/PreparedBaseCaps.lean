/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/PreparedBaseCaps.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap
import Submission.Obl.k4_general_parent_projected_layers.Support.AffineMeshCap
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Pure base ceilings from the original unit native-signal bins. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem cell_eq_baseMesh (a : PreparedModel α) (N r : ℝ) (k : ℕ) (z : α × ℝ) :
    a.cell N r k z = baseMesh (N ^ (-r)) (basePoint (a.b k z.1) z.2) := rfl

theorem ae_native_signal_bound (p : Parameters) (a : PreparedModel α)
    (hcommon : a.Common p) (k : ℕ) :
    ∀ᵐ z ∂a.mu k, |eval (a.x k z.1 z.2) (a.P k)| ≤ p.K k := by
  rcases hcommon k with ⟨_hb, _hnu, _hpi, _hdom, _hrho, hsupp, _hmass, _hdeg, _hbnd, hsig⟩
  have hunit : ∀ᵐ z ∂a.mu k, z ∈ (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    ae_iff.mpr hsupp
  filter_upwards [hunit, hsig] with z hz hzs
  exact (hzs.1 z.2 hz.2).1

theorem pure_base_cap_of_unit_signal (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p) (k : ℕ) {r : ℝ}
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      a.mu k {z | a.cell (p.N k) r k z = q ∧
        ⌊eval (a.x k z.1 z.2) (a.P k)⌋ = j} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ 3)) (q : Fin 3 → ℤ) :
    a.mu k {z | baseMesh (p.N k ^ (-r)) (basePoint (a.b k z.1) z.2) = q} ≤
      ENNReal.ofReal ((4 * p.K k + 2) * p.K k * (p.N k ^ (-r)) ^ 3) := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans (hp.2.2.1.1 k)
  have hd : 0 < p.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have hbound : ∀ᵐ z ∂a.mu k, True → |eval (a.x k z.1 z.2) (a.P k)| ≤ p.K k :=
    (a.ae_native_signal_bound p hcommon k).mono (fun _ hz _ => hz)
  have hc (q : Fin 3 → ℤ) (j : ℤ) :
      a.mu k {z | baseMesh (p.N k ^ (-r)) (basePoint (a.b k z.1) z.2) = q ∧
        ⌊eval (a.x k z.1 z.2) (a.P k) / 1⌋ = j ∧ True} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ 3) := by
    simpa only [div_one, and_true, cell_eq_baseMesh] using hcap q j
  simpa only [and_true, div_one] using base_cell_cap_of_bounded_signal
    (a.mu k) (fun z => basePoint (a.b k z.1) z.2)
    (fun z => eval (a.x k z.1 z.2) (a.P k)) (fun _ => True)
    hd (by norm_num : (0 : ℝ) < 1) hK hK hbound hc q

theorem eventually_pure_base_caps (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p) (hcaps : a.Caps p)
    {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ q : Fin 3 → ℤ,
      a.mu k {z | baseMesh (p.N k ^ (-r)) (basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * (p.N k ^ (-r)) ^ 3) := by
  have hv : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hR.le
  filter_upwards [hcaps R hR] with k hk
  intro r hrl hrh q
  apply a.pure_base_cap_of_unit_signal p hp hcommon k (q := q)
  intro q' j
  have h := (hk r 0 1 hrl hrh (by norm_num) (by linarith) hv hR.le).2.1 true q' j
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hpower : p.N k ^ (-3 * r) = (p.N k ^ (-r)) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  change a.mu k {z | a.cell (p.N k) r k z = q' ∧
    ⌊eval (a.x k z.1 z.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * 0)) at h
  simpa only [neg_zero, Real.rpow_zero, mul_zero, sub_zero, div_one, hpower] using h

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
