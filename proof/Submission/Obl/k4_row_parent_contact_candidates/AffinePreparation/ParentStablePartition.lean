/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ParentStablePartition.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ParentStableBase
import Submission.Obl.k4_general_parent_projected_layers.Support.TerminalMeshConditions
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentScalePowers
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

/-! One fixed parent partition precedes all later row-chart mesh requests. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_stable_native_signal_oscillation (nativeBase)

noncomputable section

/-- At a fixed positive depth, every original parent has the accepted two
stable groups, with relative loss `H_parent⁻¹` and one fixed polynomial
Lipschitz exponent. The groups do not depend on a later mesh or velocity bin. -/
theorem eventually_parent_signal_groups {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α)
    (hcommon : a.Common p) (hcaps : a.Caps p) (hatlases : a.Atlases p)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ p.U) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop, ∀ i : Fin (a.n k r),
      ∃ E : Fin 2 → Set (α × ℝ), (∀ e, MeasurableSet (E e)) ∧
        (∀ e, E e ⊆ a.parentSet k r i) ∧
        (∀ e e', e ≠ e' → Disjoint (E e) (E e')) ∧
        a.mu k (a.parentSet k r i \ ⋃ e, E e) ≤ a.mu k (a.parentSet k r i) *
          ENNReal.ofReal ((parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r))⁻¹) ∧
        ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
          |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
            2 * (2 * p.K k) ^ 14 * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r + p.N k ^ B *
              ‖nativeBase ((a.parentSupportZoom p k r i).nativePoint (a.nativePoint k z)) -
                nativeBase ((a.parentSupportZoom p k r i).nativePoint (a.nativePoint k w))‖ := by
  obtain ⟨J, C, hC, hpart⟩ :=
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.finite_mesh_prepared_parent_support (α := α) 1
  let L := projectionMeshExponent J C p.kappa p.ell
  obtain ⟨t, ht, hmesh⟩ := Submission.Obl.k4_general_parent_projected_layers.PreparedModel.eventually_terminal_mesh_conditions
    p hp a J C (a₀ := r) (m := L * r + 1) hr (by dsimp [L]; linarith)
  let R : ℝ := 2 + t + t⁻¹ + r + r⁻¹
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have htR : t ≤ R := by dsimp [R]; linarith
  have htiR : t⁻¹ ≤ R := by dsimp [R]; linarith
  have hriR : r⁻¹ ≤ R := by dsimp [R]; linarith
  have hRt : R⁻¹ ≤ t := by
    simpa only [inv_inv] using inv_anti₀ hti htiR
  have hRr : R⁻¹ ≤ r := by
    simpa only [inv_inv] using inv_anti₀ hri hriR
  let B : ℝ := (r + 1) * C
  have hCp : (0 : ℝ) < C := by
    have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  filter_upwards [hmesh, a.eventually_pure_base_caps p hp hcommon hcaps hR,
    hatlases R hR, eventually_parentFilling_le p hp (eps := 1) one_pos]
    with k hkm hkc hka hkH
  intro i
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hatlas : a.AtlasAt p R k r := hka r hRr hrU
  have hmsh := hkm R r le_rfl (by linarith) hatlas
  have hH0 : 0 ≤ parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r) := by
    unfold parentFilling Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width
    positivity
  have hLip : parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r) ^ C ≤ p.N k ^ B := by
    calc
      _ ≤ (p.N k ^ (r + 1)) ^ C := pow_le_pow_left₀ hH0 (hkH r) C
      _ = _ := by
        rw [← Real.rpow_mul_natCast hN.le]
  obtain ⟨E, hEm, hEsub, hEd, hEloss, hEosc⟩ := hpart p hp a hcommon R k r hr.le hatlas i
    (p.N k ^ (-t)) (p.N k ^ (-(L * r / 2)))
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) hmsh.root_small
    (hmsh.resolution i) (hkc t hRt htR)
  refine ⟨E, hEm, hEsub, hEd, ?_, ?_⟩
  · simpa only [pow_one] using hEloss
  · intro e z hz w hw
    exact (hEosc e z hz w hw).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hLip (norm_nonneg _)))

/-- The first partition's relative loss is negligible for every subpower
dense row law at this positive parent depth. It is chosen before later affine
approximation tolerances. -/
theorem eventually_parent_partition_preserves_row_mass {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    {r : ℝ} (hr : 0 < r) (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    ∀ᶠ k in atTop, ∀ (R : ℝ) (hatlas : a.AtlasAt p R k r) (i : Fin (a.n k r))
      (G : Set (α × ℝ)), G ⊆ a.parentSet k r i →
      ENNReal.ofReal (a.q k r / M k) * a.nu k (a.A k r i) ≤ a.rho k G →
      ∀ E : Fin 2 → Set (α × ℝ),
        a.mu k (a.parentSet k r i \ ⋃ e, E e) ≤ a.mu k (a.parentSet k r i) *
          ENNReal.ofReal ((parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r))⁻¹) →
        ENNReal.ofReal (a.q k r / (2 * M k)) * a.nu k (a.A k r i) ≤
          a.rho k (G ∩ ⋃ e, E e) := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hNp : ∀ k, 0 < p.N k := fun k => by linarith [hp.1 k]
  have hK0 : ∀ k, 0 ≤ p.K k := fun k => zero_le_one.trans (hp.2.2.1.1 k)
  have hM0 : ∀ k, 0 ≤ M k := fun k => zero_le_one.trans (hM k)
  have hprod1 : ∀ k, 1 ≤ p.K k * M k := fun k =>
    one_le_mul_of_one_le_of_one_le (hp.2.2.1.1 k) (hM k)
  have hprodsub := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul
    hNp hK0 hM0 hp.2.2.1.2 hMsub
  filter_upwards [Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.2.1 hprod1 hprodsub 1 (show -r < (0 : ℝ) by linarith)
      (show (0 : ℝ) ≤ 2 by norm_num)] with k hk
  simp only [pow_one, Real.rpow_zero] at hk
  intro R hatlas i G hG hmass E hloss
  have hMpos : 0 < M k := zero_lt_one.trans_le (hM k)
  have hNk : 0 < p.N k := hNp k
  have hHinv : (parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r))⁻¹ ≤ p.N k ^ (-r) := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos (hNp k) r) (rpow_depth_le_parentFilling p hp k r)
    simpa only [Real.rpow_neg (hNp k).le] using h
  have hsmall : p.K k * (parentFilling (p.K k) (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r))⁻¹ ≤
      1 / (2 * M k) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * M k)).mpr
    calc
      _ ≤ (p.K k * p.N k ^ (-r)) * (2 * M k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHinv (hK0 k)) (by positivity)
      _ = 2 * (p.K k * M k) * p.N k ^ (-r) := by ring
      _ ≤ 1 := hk.le
  apply parent_stable_current_mass p hp a hcommon hatlas i G hG E hMpos
    (by unfold parentFilling Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width; positivity) hmass hloss hsmall

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
