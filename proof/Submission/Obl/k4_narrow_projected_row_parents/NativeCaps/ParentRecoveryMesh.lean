/- Adapted from this LOT tree o222, session x0774, commit 9dbb47a74d2ab640ef4d8807465d86d7e9066adc,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentRecoveryMesh.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.ParentStableBase
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMeshPowers
import Submission.Obl.k4_general_parent_projected_layers.Support.SupportMeshResolution

/-! Resolve stable native oscillation and a row chart with a fixed source mesh. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Matrix Filter
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- A fixed polynomial bound for the row matrix gives a fixed finer source
mesh resolving both that row chart and the native oscillation groups. -/
theorem eventually_parent_recovery_mesh_uniform {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {r B C t : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C) (ht : 0 < t)
    :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop, ∀ (R : ℝ) (hatlas : a.AtlasAt p R k r)
      (i : Fin (a.n k r)),
      (∀ e, (∑ j, |(a.parentSupportZoom p k r i).baseMatrix e j| * p.N k ^ (-D)) ≤
        p.N k ^ (-(B + r + 1))) ∧
      p.N k ^ B * (3 * p.N k ^ (-(B + r + 1))) ≤ PreparedModel.width p k r ∧
      ∀ (A : Matrix (Fin 3) (Fin 3) ℝ), (∀ e, (∑ j, |A e j|) ≤ p.N k ^ C) →
        ∀ e, (∑ j, |A e j| * p.N k ^ (-D)) ≤ p.N k ^ (-t) := by
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  let E : ℝ := (p.kappa + p.ell) * r + 1
  let M : ℝ := B + r + 1
  let D : ℝ := M + E + t + C + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [a.eventually_q_narrow_lower p hp r (eps := 1) one_pos,
    hp.2.1.eventually (eventually_ge_atTop 3)] with k hkqg hN3
  intro R hatlas i
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hq : 0 < a.q k r := by unfold PreparedModel.q; positivity
  have hg : 0 < PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  have hg1 : PreparedModel.narrow p k r ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith [mul_pos hℓ hr])
  have hqg : p.N k ^ (-E) ≤ a.q k r * PreparedModel.narrow p k r := by
    convert hkqg R r hatlas le_rfl using 1
    congr 1
    dsimp [E]
    ring
  have hdelta : 0 ≤ p.N k ^ (-D) := Real.rpow_nonneg hN.le _
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have hlabel := hatlas.2.2.2.2.1 i
    have hrow := supportZoom_mesh_resolution hK hq hg hg1 hdelta
      (a.blockMid k r i) (a.c k r i 0 + a.blockMid k r i * a.c k r i 1)
      (a.c k r i) (hlabel.2.2.2.1 3) (hlabel.2.2.2.1 4) e
    exact hrow.trans (physical_mesh_over_packet hN1 hqg (by dsimp [D]; linarith))
  · change p.N k ^ B * (3 * p.N k ^ (-M)) ≤ p.N k ^ (-r)
    calc
      _ = 3 * p.N k ^ (B - M) := by rw [sub_eq_add_neg, Real.rpow_add hN]; ring
      _ ≤ p.N k * p.N k ^ (B - M) :=
        mul_le_mul_of_nonneg_right hN3 (Real.rpow_nonneg hN.le _)
      _ = _ := by
        calc p.N k * p.N k ^ (B - M) = p.N k ^ (1 + (B - M)) := by
              rw [Real.rpow_add hN, Real.rpow_one]
          _ = p.N k ^ (-r) := by congr 1; dsimp [M]; ring
  · intro A hkA e
    calc
      _ = (∑ j, |A e j|) * p.N k ^ (-D) := (Finset.sum_mul ..).symm
      _ ≤ p.N k ^ C * p.N k ^ (-D) := mul_le_mul_of_nonneg_right (hkA e) hdelta
      _ = p.N k ^ (C - D) := by rw [sub_eq_add_neg, Real.rpow_add hN]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [D]; linarith)


/-- A sequence of row matrices inherits the same uniform source mesh. -/
theorem eventually_parent_recovery_mesh {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {r B C t : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C) (ht : 0 < t)
    (A : (k : ℕ) → Fin (a.n k r) → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ᶠ k in atTop, ∀ i e, (∑ j, |A k i e j|) ≤ p.N k ^ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop, ∀ (R : ℝ) (hatlas : a.AtlasAt p R k r)
      (i : Fin (a.n k r)),
      (∀ e, (∑ j, |(a.parentSupportZoom p k r i).baseMatrix e j| * p.N k ^ (-D)) ≤
        p.N k ^ (-(B + r + 1))) ∧
      p.N k ^ B * (3 * p.N k ^ (-(B + r + 1))) ≤ PreparedModel.width p k r ∧
      ∀ e, (∑ j, |A k i e j| * p.N k ^ (-D)) ≤ p.N k ^ (-t) := by
  obtain ⟨D, hD, hmesh⟩ := eventually_parent_recovery_mesh_uniform p hp a hr hB hC ht
  refine ⟨D, hD, ?_⟩
  filter_upwards [hmesh, hA] with k hk hka
  intro R hatlas i
  have hm := hk R hatlas i
  exact ⟨hm.1, hm.2.1, hm.2.2 (A k i) (hka i)⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
