/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/WeightedTerminalBudget.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.OriginalAssignmentBudget
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Original palette weights cancel the major intercept mesh in support sums. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

noncomputable section

theorem weighted_projected_support_budget {ι κ γ : Type*}
    (V : Finset ι) (I : ι → Finset κ) (G : ι → κ → Finset γ)
    (w : ι → ℝ) (T : ι → κ → γ → ℝ)
    {chi g q Cmajor Ccrop Carea : ℝ}
    (hc : 0 ≤ chi) (hg : 0 ≤ g) (hq : 0 ≤ q)
    (hCmajor : 0 ≤ Cmajor) (hCcrop : 0 ≤ Ccrop) (hCarea : 0 ≤ Carea)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hwsum : ∑ v ∈ V, w v ≤ 1)
    (hmajor : ∀ v ∈ V, ((I v).card : ℝ) * chi ≤ Cmajor * q)
    (hcrop : ∀ v ∈ V, ∀ z ∈ I v, ((G v z).card : ℝ) ≤ Ccrop)
    (harea : ∀ v ∈ V, ∀ z ∈ I v, ∀ e ∈ G v z, T v z e ≤ Carea * q ^ 2) :
    (∑ v ∈ V, ∑ z ∈ I v, ∑ e ∈ G v z, (chi * g * w v) * T v z e) ≤
      Cmajor * Ccrop * Carea * q ^ 3 * g := by
  have hinner (v : ι) (hv : v ∈ V) (z : κ) (hz : z ∈ I v) :
      (∑ e ∈ G v z, (chi * g * w v) * T v z e) ≤
        Ccrop * (chi * g * w v) * (Carea * q ^ 2) := by
    have hwv : 0 ≤ chi * g * w v := mul_nonneg (mul_nonneg hc hg) (hw v hv)
    calc
      _ ≤ ∑ _e ∈ G v z, (chi * g * w v) * (Carea * q ^ 2) :=
        Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (harea v hv z hz e he) hwv)
      _ = ((G v z).card : ℝ) * (chi * g * w v) * (Carea * q ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcrop v hv z hz) hwv) (by positivity)
  have houter (v : ι) (hv : v ∈ V) :
      (∑ z ∈ I v, ∑ e ∈ G v z, (chi * g * w v) * T v z e) ≤
        (Cmajor * Ccrop * Carea * q ^ 3 * g) * w v := by
    have hwv : 0 ≤ w v := hw v hv
    calc
      _ ≤ ∑ _z ∈ I v, Ccrop * (chi * g * w v) * (Carea * q ^ 2) :=
        Finset.sum_le_sum (fun z hz => hinner v hv z hz)
      _ = (((I v).card : ℝ) * chi) * (Ccrop * Carea * q ^ 2 * g * w v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (Cmajor * q) * (Ccrop * Carea * q ^ 2 * g * w v) :=
        mul_le_mul_of_nonneg_right (hmajor v hv) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ v ∈ V, (Cmajor * Ccrop * Carea * q ^ 3 * g) * w v :=
      Finset.sum_le_sum (fun v hv => houter v hv)
    _ = (Cmajor * Ccrop * Carea * q ^ 3 * g) * ∑ v ∈ V, w v := by rw [Finset.mul_sum]
    _ ≤ (Cmajor * Ccrop * Carea * q ^ 3 * g) * 1 :=
      mul_le_mul_of_nonneg_left hwsum (by positivity)
    _ = _ := mul_one _

open MeasureTheory

theorem PreparedModel.weighted_terminal_support_budget {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s)
    {C : ℝ} (hC : 0 ≤ C) (cost : Fin (a.n k s) → ℝ)
    (hcost : ∀ i, cost i ≤ C * (a.q k s ^ 3 * PreparedModel.narrow p k s)) :
    (∑ i, cost i) ≤ C * p.K k / (PreparedModel.width p k s) ^ p.d := by
  calc
    _ ≤ ∑ _i : Fin (a.n k s), C * (a.q k s ^ 3 * PreparedModel.narrow p k s) :=
      Finset.sum_le_sum (fun i hi => hcost i)
    _ = C * ((a.n k s : ℝ) * (a.q k s ^ 3 * PreparedModel.narrow p k s)) := by simp; ring
    _ ≤ C * (p.K k / (PreparedModel.width p k s) ^ p.d) :=
      mul_le_mul_of_nonneg_left (a.original_label_volume_budget p hp hcommon hatlas) hC
    _ = _ := by ring

end

end Submission.Obl.k4_general_parent_projected_layers
