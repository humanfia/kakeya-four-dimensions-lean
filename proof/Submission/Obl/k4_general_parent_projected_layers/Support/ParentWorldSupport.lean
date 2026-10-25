/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentWorldSupport.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentGroupSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.CompatibleWorlds
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldSupportBudget
import Submission.Obl.k4_row_cell_regularization.Palette
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Original-palette weighted terminal support of a complete true parent. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

def terminalAreaConstant (K : ℝ) : ℝ :=
  14400 * K ^ 2 * (2 * (2 * (2 * K) ^ 14 + 1) + 2)

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem blockMid_mem (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    a.blockMid k s i ∈ a.block k s i := by
  apply (Submission.Obl.k4_scalar_angular_pair_agreement.mem_I_iff_mid _ _ _).mpr
  simp only [blockMid, sub_self, abs_zero]
  positivity

theorem parent_world_terminal_support (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (hpi : IsProbabilityMeasure (a.pi k))
    (i : Fin (a.n k s)) (E : Fin 2 → Set (α × ℝ))
    (hparent : ∀ e, E e ⊆ a.parentSet k s i)
    (hcoeff : ∀ e z, z ∈ E e →
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k)
    {L sigma chi : ℝ} (hL : 0 ≤ L) (hσ : 0 < sigma) (hσq : sigma ≤ a.q k s)
    (hchi : 0 < chi) (hchiq : chi ≤ a.q k s)
    (hchiqg : chi ≤ a.q k s * narrow p k s)
    (hsmall : L * (24 * p.K k ^ 2 * (sigma + chi) / (a.q k s * narrow p k s)) ≤ width p k s)
    (hosc : ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
      |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
        2 * (2 * p.K k) ^ 14 * width p k s +
          L * ‖nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) -
            nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k w))‖)
    (Q : Finset (Fin 4 → ℤ)) :
    ∃ F : (Fin 4 → ℤ) → Finset ((Fin 2 → ℤ) × ℤ),
      (∑ u ∈ Q, (chi * narrow p k s *
        (a.pi k {v | ⌊v / chi⌋ = u 0}).toReal) * ((F u).card * sigma ^ 2)) ≤
          (10 * p.K k) * (180 * p.K k ^ 2) * terminalAreaConstant (p.K k) *
            a.q k s ^ 3 * narrow p k s ∧
      ∀ u ∈ Q, ∀ e z, z ∈ E e → projectedWorldTag chi (narrow p k s) (a.b k z.1) = u →
        (projectedCell sigma (narrow p k s)
          (projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 2)
          (projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 3) (a.b k z.1) z.2,
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋) ∈ F u := by
  classical
  letI := hpi
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k s := by unfold q; positivity
  have hq1 : a.q k s ≤ 1 := by
    rw [q, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hmid := a.blockMid_mem k s i
  have hmidunit := interval_subset_unit _ _ hmid
  have hlabel := hatlas.2.2.2.2.1 i
  have hc₄ : |a.c k s i 4| ≤ p.K k := hlabel.2.2.2.1 4
  obtain ⟨V, I, G, hI, hG, hcompatible⟩ := compatible_parent_world_lists (a.c k s i)
    hK hq.le hq1 hg hchi hchiq hchiqg hmidunit hc₄
  let active := Q.filter (fun u => ∃ e z, z ∈ E e ∧
    projectedWorldTag chi (narrow p k s) (a.b k z.1) = u)
  have hactive : ∀ u ∈ active,
      u 0 ∈ V ∧ u 1 ∈ I (u 0) ∧ (u 2, u 3) ∈ G (u 0) (u 1) := by
    intro u hu
    obtain ⟨e, z, hz, htag⟩ := (Finset.mem_filter.mp hu).2
    have hzp := hparent e hz
    have hpkt := hlabel.2.2.2.2.2.1 z.1 ((hatlas.2.2.1 i).2.2 hzp.1) _ hmid
    have hmajor : |a.b k z.1 0 + a.blockMid k s i * a.b k z.1 3 -
        (a.c k s i 0 + a.blockMid k s i * a.c k s i 1)| ≤ p.K k * a.q k s := by
      have hh : |a.b k z.1 0 + a.blockMid k s i * a.b k z.1 3 -
          a.c k s i 0 - a.blockMid k s i * a.c k s i 1| ≤ p.K k * a.q k s := hpkt.1
      simpa only [sub_add_eq_sub_sub] using hh
    simpa only [htag] using hcompatible (a.b k z.1) (hcoeff e z hz) hmajor hpkt.2.1 hpkt.2.2
  have hpart (u : Fin 4 → ℤ) := a.parent_group_terminal_support p hp hs hatlas i E hparent
    (y₀ := projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 2)
    (y₁ := projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 3)
    (z₀ := projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 1)
    (z₁ := projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 0)
    hL hσ hσq hchi.le hchiqg
    (projectedWorldRepresentatives_bound hK0 u 3)
    (projectedWorldRepresentatives_bound hK0 u 0) hsmall hosc
  choose F₀ hF₀ hFcover using hpart
  let F (u : Fin 4 → ℤ) := if u ∈ active then F₀ u else ∅
  have harea (u : Fin 4 → ℤ) : ((F u).card : ℝ) * sigma ^ 2 ≤
      terminalAreaConstant (p.K k) * a.q k s ^ 2 := by
    by_cases hu : u ∈ active
    · simpa only [F, if_pos hu, terminalAreaConstant, mul_assoc, mul_left_comm, mul_comm] using hF₀ u
    · simp only [F, if_neg hu, Finset.card_empty, Nat.cast_zero, zero_mul]
      unfold terminalAreaConstant
      positivity
  let w (v : ℤ) := (a.pi k {x | ⌊x / chi⌋ = v}).toReal
  have hwsum : ∑ v ∈ V, w v ≤ 1 := by
    have h := Submission.Obl.k4_row_cell_regularization.sum_binWeight_le_one hchi (a.pi k) V
    change (∑ v ∈ V, (a.pi k (Submission.Obl.k4_row_cell_regularization.velocityCell chi v)).toReal) ≤ 1 at h
    simpa only [w, Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hchi] using h
  have hsum := weighted_world_support_budget active V I G w
    (fun u => ((F u).card : ℝ) * sigma ^ 2) hchi.le hg.le hq.le
    (by positivity : 0 ≤ 10 * p.K k) (by positivity : 0 ≤ 180 * p.K k ^ 2)
    (by unfold terminalAreaConstant; positivity) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => by positivity) hwsum hactive (fun v _ => hI v) (fun v _ z _ => hG v z)
    (fun v _ z _ e _ => harea _)
  have heq : (∑ u ∈ Q, (chi * narrow p k s * w (u 0)) * ((F u).card * sigma ^ 2)) =
      ∑ u ∈ active, (chi * narrow p k s * w (u 0)) * ((F u).card * sigma ^ 2) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnot
    by_cases hm : u ∈ active
    · exact (hnot hm).elim
    · simp only [F, if_neg hm, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero]
  refine ⟨F, ?_, ?_⟩
  · change (∑ u ∈ Q, (chi * narrow p k s * w (u 0)) * ((F u).card * sigma ^ 2)) ≤ _
    rw [heq]
    exact hsum
  · intro u hu e z hz htag
    have ha : u ∈ active := Finset.mem_filter.mpr ⟨hu, e, z, hz, htag⟩
    have hrep := projectedWorldRepresentatives_gap hchi hg (a.b k z.1) (hcoeff e z hz) htag
    dsimp only [F]
    rw [if_pos ha]
    exact hFcover u e z hz hrep.1 hrep.2.2

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
