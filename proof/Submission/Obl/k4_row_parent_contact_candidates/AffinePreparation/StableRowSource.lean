/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/StableRowSource.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ParentRowGeometry
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ParentStablePartition
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ParentContactBudget

/-! Dense row events retained inside the original two-group native partition. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_stable_native_signal_oscillation (nativeBase)

noncomputable section

structure StableRowSource {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (k : ℕ) (r e₀ M B : ℝ) where
  rowParent : CoarseRowParent p a k r (M * p.N k ^ (-e₀)) M
  lam_ne : rowParent.lam ≠ 0
  inv_le : |rowParent.lam⁻¹| ≤ M
  groups : Fin 2 → Set (α × ℝ)
  measurable_groups : ∀ e, MeasurableSet (groups e)
  oscillation : ∀ e z, z ∈ groups e → ∀ w, w ∈ groups e →
    |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
      2 * (2 * p.K k) ^ 14 * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r + p.N k ^ B *
        ‖nativeBase ((a.parentSupportZoom p k r rowParent.Q).nativePoint (a.nativePoint k z)) -
          nativeBase ((a.parentSupportZoom p k r rowParent.Q).nativePoint (a.nativePoint k w))‖
  mass : ENNReal.ofReal (a.q k r / (2 * M)) * a.nu k (a.A k r rowParent.Q) ≤
    a.rho k (rowParent.G ∩ ⋃ e, groups e)

namespace StableRowSource

variable {α : Type} [MeasurableSpace α]
variable {p : Submission.Obl.k4_general_parent_projected_layers.Parameters} {a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α} {k : ℕ} {r e₀ M B : ℝ}

def keep (S : StableRowSource p a k r e₀ M B) : Set (α × ℝ) :=
  S.rowParent.G ∩ ⋃ e, S.groups e

def source (S : StableRowSource p a k r e₀ M B) : Measure (α × ℝ) := (a.rho k).restrict S.keep

def weight (S : StableRowSource p a k r e₀ M B) : ℝ :=
  a.q k r * (a.nu k (a.A k r S.rowParent.Q)).toReal

def law (S : StableRowSource p a k r e₀ M B) : Measure (α × ℝ) :=
  (ENNReal.ofReal S.weight)⁻¹ • S.source

def sample (S : StableRowSource p a k r e₀ M B) :
    Submission.Lib.K4ContactAffine.NativeSample (α × ℝ) := S.rowParent.sample S.law

theorem measurable_keep (S : StableRowSource p a k r e₀ M B) : MeasurableSet S.keep :=
  S.rowParent.measurable_G.inter (MeasurableSet.iUnion S.measurable_groups)

theorem source_le_mu (S : StableRowSource p a k r e₀ M B) (hcommon : a.Common p) :
    S.source ≤ a.mu k := Measure.restrict_le_self.trans (hcommon k).2.2.2.2.1

theorem ae_source_groups (S : StableRowSource p a k r e₀ M B) :
    ∀ᵐ z ∂S.source, ∃ e, z ∈ S.groups e := by
  filter_upwards [ae_restrict_mem S.measurable_keep] with z hz
  exact mem_iUnion.mp hz.2

theorem weight_pos (S : StableRowSource p a k r e₀ M B) (hp : p.Valid)
    (hcommon : a.Common p) {R : ℝ} (hatr : a.AtlasAt p R k r) : 0 < S.weight := by
  letI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.2.2.1.1 k)
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have ha : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r := Real.rpow_pos_of_pos hN _
  have hg : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  have hprior : a.nu k (a.A k r S.rowParent.Q) ≠ 0 := by
    apply (lt_of_lt_of_le _ (hatr.2.2.2.2.1 S.rowParent.Q).1).ne'
    exact ENNReal.ofReal_pos.mpr (by positivity)
  exact mul_pos hq (ENNReal.toReal_pos hprior (measure_ne_top _ _))

theorem law_mass (S : StableRowSource p a k r e₀ M B) (hp : p.Valid)
    (hcommon : a.Common p) {R : ℝ} (hatr : a.AtlasAt p R k r) (hM : 0 < M) :
    ENNReal.ofReal ((2 * M)⁻¹) ≤ S.law univ := by
  letI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hw := S.weight_pos hp hcommon hatr
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hmass : ENNReal.ofReal (S.weight / (2 * M)) ≤ S.source univ := by
    rw [source, Measure.restrict_apply_univ, keep]
    convert S.mass using 1
    calc
      ENNReal.ofReal (S.weight / (2 * M)) =
          ENNReal.ofReal ((a.q k r / (2 * M)) * (a.nu k (a.A k r S.rowParent.Q)).toReal) := by
        congr 1
        dsimp [weight]
        ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [law, Measure.smul_apply, smul_eq_mul]
  calc
    ENNReal.ofReal ((2 * M)⁻¹) =
        (ENNReal.ofReal S.weight)⁻¹ * ENNReal.ofReal (S.weight / (2 * M)) := by
      rw [← ENNReal.ofReal_inv_of_pos hw, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul' le_rfl hmass

end StableRowSource

/-- The stable sources exist for every eligible late row parent, before
any later affine mesh or approximation tolerance is requested. -/
theorem eventually_stable_row_sources {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatlases : a.Atlases p) {r e₀ : ℝ}
    (hr : 0 < r) (hrU : r ≤ p.U) (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop,
      ∀ RP : CoarseRowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
        RP.lam ≠ 0 → |RP.lam⁻¹| ≤ M k →
        ∃ S : StableRowSource p a k r e₀ (M k) B, S.rowParent = RP := by
  obtain ⟨B, hB, hgroups⟩ := eventually_parent_signal_groups p hp a hcommon hcaps hatlases hr hrU
  let R : ℝ := 2 + r + r⁻¹
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hri h
  refine ⟨B, hB, ?_⟩
  filter_upwards [hgroups, hatlases R hR,
    eventually_parent_partition_preserves_row_mass p hp a hcommon hr M hM hMsub]
    with k hk hka hkretain
  intro RP hlam hinv
  have hatr : a.AtlasAt p R k r := hka r hRr hrU
  obtain ⟨E, hEm, _hEsub, _hEd, hloss, hosc⟩ := hk RP.Q
  have hmass := hkretain R hatr RP.Q RP.G RP.G_sub RP.mass E hloss
  exact ⟨⟨RP, hlam, hinv, E, hEm, hosc, hmass⟩, rfl⟩

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
