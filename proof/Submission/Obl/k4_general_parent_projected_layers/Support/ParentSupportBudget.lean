/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentSupportBudget.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass
import Submission.Obl.k4_general_parent_projected_layers.Support.OriginalAssignmentBudget
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Aggregate parent support losses against full original assignment weights. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem volume_block (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    volume (a.block k s i) = ENNReal.ofReal (a.q k s) := by
  rw [block, interval, Real.volume_Icc]
  unfold q
  rw [zpow_neg, zpow_natCast]
  congr 1
  ring

theorem original_parent_mass_upper (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ}
    (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    a.mu k (a.B k s i ×ˢ a.block k s i) ≤
      ENNReal.ofReal (p.K k * a.q k s) * a.nu k (a.A k s i) := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hK : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans (hp.2.2.1.1 k)
  have hq : 0 ≤ a.q k s := by unfold q; positivity
  calc
    _ ≤ (ENNReal.ofReal (p.K k) • (a.nu k).prod volume) (a.B k s i ×ˢ a.block k s i) :=
      (hcommon k).2.2.2.1 _
    _ = ENNReal.ofReal (p.K k) * (a.nu k (a.B k s i) * ENNReal.ofReal (a.q k s)) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, volume_block]
    _ ≤ ENNReal.ofReal (p.K k) * (a.nu k (a.A k s i) * ENNReal.ofReal (a.q k s)) :=
      mul_le_mul' le_rfl (mul_le_mul' (measure_mono (hatlas.2.2.1 i).2.2) le_rfl)
    _ = _ := by rw [ENNReal.ofReal_mul hK]; ring

theorem sum_original_parent_mass_le (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) :
    ∑ i : Fin (a.n k s), a.mu k (a.B k s i ×ˢ a.block k s i) ≤ ENNReal.ofReal (p.K k) := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hK : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans (hp.2.2.1.1 k)
  have hq : 0 ≤ a.q k s := by unfold q; positivity
  have hconvert (i : Fin (a.n k s)) :
      ENNReal.ofReal (p.K k * a.q k s) * a.nu k (a.A k s i) =
        ENNReal.ofReal (p.K k * (a.q k s * (a.nu k (a.A k s i)).toReal)) := by
    rw [show p.K k * (a.q k s * (a.nu k (a.A k s i)).toReal) =
      (p.K k * a.q k s) * (a.nu k (a.A k s i)).toReal by ring,
      ENNReal.ofReal_mul (mul_nonneg hK hq),
      ENNReal.ofReal_toReal (measure_ne_top (a.nu k) (a.A k s i))]

  calc
    _ ≤ ∑ i : Fin (a.n k s), ENNReal.ofReal (p.K k * a.q k s) * a.nu k (a.A k s i) :=
      Finset.sum_le_sum (fun i hi => a.original_parent_mass_upper p hp hcommon hatlas i)
    _ = ENNReal.ofReal (p.K k * ∑ i : Fin (a.n k s),
        a.q k s * (a.nu k (a.A k s i)).toReal) := by
      simp_rw [hconvert]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => by positivity), Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (a.original_assignment_budget p hcommon hatlas) hK)

end PreparedModel

/-- Local losses are summed in the original law; no conditional reference is stored. -/
theorem finite_parent_loss_union {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (P E : ι → Set Ω) (eta K : ℝ≥0∞)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ P i)
    (hbudget : ∑ i, μ (P i) ≤ K)
    (hloss : ∀ i, μ (P i \ E i) ≤ μ (P i) * eta) :
    μ (⋃ i, E i)ᶜ ≤ K * eta := by
  have hsub : (⋃ i, E i)ᶜ ≤ᵐ[μ] ⋃ i, P i \ E i := by
    filter_upwards [hcover] with p hp
    intro hnot
    obtain ⟨i, hi⟩ := hp
    exact mem_iUnion.mpr ⟨i, hi, fun he => hnot (mem_iUnion.mpr ⟨i, he⟩)⟩
  calc
    _ ≤ μ (⋃ i, P i \ E i) := measure_mono_ae hsub
    _ ≤ ∑ i, μ (P i \ E i) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, μ (P i) * eta := Finset.sum_le_sum (fun i hi => hloss i)
    _ = (∑ i, μ (P i)) * eta := (Finset.sum_mul ..).symm
    _ ≤ K * eta := mul_le_mul' hbudget le_rfl

end

end Submission.Obl.k4_general_parent_projected_layers
