/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentGroupSupport.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedParentBand
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedZoomGap
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Terminal native-signal support of one parent in one original projected group. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem parent_group_terminal_support (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) (E : Fin 2 → Set (α × ℝ))
    (hparent : ∀ e, E e ⊆ a.parentSet k s i)
    {L sigma chi y₀ y₁ z₀ z₁ : ℝ} (hL : 0 ≤ L) (hσ : 0 < sigma)
    (hσq : sigma ≤ a.q k s) (hchi : 0 ≤ chi) (hchiqg : chi ≤ a.q k s * narrow p k s)
    (hy₁ : |y₁| ≤ p.K k) (hz₁ : |z₁| ≤ p.K k)
    (hsmall : L * (24 * p.K k ^ 2 * (sigma + chi) / (a.q k s * narrow p k s)) ≤ width p k s)
    (hosc : ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
      |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
        2 * (2 * p.K k) ^ 14 * width p k s +
          L * ‖nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) -
            nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k w))‖) :
    ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * sigma ^ 2 ≤ 14400 * p.K k ^ 2 * a.q k s ^ 2 *
        (2 * (2 * (2 * p.K k) ^ 14 + 1) + 2) ∧
      ∀ e z, z ∈ E e → a.b k z.1 ∈ majorGroup chi z₀ z₁ →
        |a.b k z.1 4 - y₁| ≤ narrow p k s →
        (projectedCell sigma (narrow p k s) y₀ y₁ (a.b k z.1) z.2,
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋) ∈ F := by
  classical
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k s := by unfold q; positivity
  have hq1 : a.q k s ≤ 1 := by
    rw [q, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hg1 : narrow p k s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [hp.1 k]) (by nlinarith [mul_nonneg hℓ.le hs])
  have hchig : chi ≤ narrow p k s := hchiqg.trans
    (by nlinarith [mul_le_mul_of_nonneg_right hq1 hg.le])
  have hlabel := hatlas.2.2.2.2.1 i
  have hc₃ : |a.c k s i 3| ≤ p.K k := hlabel.2.2.2.1 3
  have hc₄ : |a.c k s i 4| ≤ p.K k := hlabel.2.2.2.1 4
  let S : Set (α × ℝ) := {z | a.b k z.1 ∈ majorGroup chi z₀ z₁ ∧
    |a.b k z.1 4 - y₁| ≤ narrow p k s}
  let cell : α × ℝ → Fin 2 → ℤ := fun z =>
    projectedCell sigma (narrow p k s) y₀ y₁ (a.b k z.1) z.2
  let signal : α × ℝ → ℝ := fun z => eval (a.x k z.1 z.2) (a.P k)
  let M : ℝ := 2 * (2 * p.K k) ^ 14 + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  by_cases hnonempty : (⋃ e, E e ∩ S).Nonempty
  · obtain ⟨z, hz⟩ := hnonempty
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    have hzparent := hparent e he.1
    have hzpacket := hlabel.2.2.2.2.2.1 z.1
      ((hatlas.2.2.1 i).2.2 hzparent.1) z.2 hzparent.2
    have hv := projected_parent_band_velocity (a.c k s i) (a.b k z.1) hK hg hchig hc₄
      he.2.1 hzpacket.2.2 he.2.2
    obtain ⟨B, hB, hBcover⟩ := projected_parent_cell_cover
      (sigma := sigma) (y₀ := y₀) (z₀ := z₀) (tmid := a.blockMid k s i)
      (a.c k s i) hK hg hchi hchiqg hc₄ hσ hσq hv
    have hcover (e : Fin 2) : ∀ z ∈ E e ∩ S, cell z ∈ B := by
      intro z hz
      have hzp := hparent e hz.1
      have hpkt := hlabel.2.2.2.2.2.1 z.1 ((hatlas.2.2.1 i).2.2 hzp.1) z.2 hzp.2
      exact hBcover (a.b k z.1) z.2 (interval_subset_unit _ _ hzp.2)
        ((a.block_distance_mid k s i hzp.2).trans (by linarith)) hz.2.1 hpkt.2.1
    have hosc' (e : Fin 2) : ∀ z ∈ E e ∩ S, ∀ w ∈ E e ∩ S,
        cell z = cell w → |signal z - signal w| ≤ M * width p k s := by
      intro z hz w hw hcell
      have hzp := hparent e hz.1
      have hwp := hparent e hw.1
      have hraw := projectedCell_base_gap hσ hg hchi hK0 hy₁ hz₁
        (a.b k z.1) (a.b k w.1) (cell z)
        (interval_subset_unit _ _ hzp.2) (interval_subset_unit _ _ hwp.2)
        hz.2.1 hw.2.1 rfl hcell.symm
      have hgap := supportZoom_base_gap (tmid := a.blockMid k s i)
        (z₀ := a.c k s i 0 + a.blockMid k s i * a.c k s i 1) (a.c k s i)
        hK hq hg hg1 hσ.le hchi hc₃ hc₄ (a.nativePoint k z) (a.nativePoint k w)
        hraw.1 hraw.2.1 hraw.2.2
      have hbnd : |signal z - signal w| ≤ 2 * (2 * p.K k) ^ 14 * width p k s +
          L * (24 * p.K k ^ 2 * (sigma + chi) / (a.q k s * narrow p k s)) :=
        (hosc e z hz.1 w hw.1).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap hL))
      dsimp [M]
      nlinarith
    choose G hGcard hGcover using fun e =>
      terminal_support_of_fiber_oscillation (E e ∩ S) cell signal B ha hM (hcover e) (hosc' e)
    let F := Finset.univ.biUnion G
    have hcard : (F.card : ℝ) ≤ 2 * ((B.card : ℝ) * (2 * M + 2)) := by
      calc
        _ ≤ ∑ e : Fin 2, ((G e).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _e : Fin 2, (B.card : ℝ) * (2 * M + 2) :=
          Finset.sum_le_sum (fun e he => hGcard e)
        _ = _ := by simp
    refine ⟨F, ?_, ?_⟩
    · calc
        _ ≤ (2 * ((B.card : ℝ) * (2 * M + 2))) * sigma ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
        _ = (2 * (2 * M + 2)) * ((B.card : ℝ) * sigma ^ 2) := by ring
        _ ≤ (2 * (2 * M + 2)) * (7200 * p.K k ^ 2 * a.q k s ^ 2) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _ := by dsimp [M]; ring
    · intro e z hz hzmajor hzcrop
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e,
        hGcover e z ⟨hz, hzmajor, hzcrop⟩⟩
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
    · intro e z hz hzmajor hzcrop
      exact (hnonempty ⟨z, mem_iUnion.mpr ⟨e, hz, hzmajor, hzcrop⟩⟩).elim

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
