-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.TerminalAncestry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/TerminalAncestry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/TerminalAncestry.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/TerminalAncestry.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/TerminalAncestry.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.HistoryPackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FinePredictionCore
import Submission.Obl.k4_finite_forest_width_selection.ForestCombinatorics

/-! The terminal packet predicts its whole ancestor chain on the original
full-measure uniqueness core. No comparison of earlier depths with L is
needed for this list. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped BigOperators

theorem measurableSet_packetUnique {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X)
    (hF : ∀ b, MeasurableSet (F b)) (w : Fin W) :
    MeasurableSet {z | packetUnique lev γ F w z} := by
  have heq : {z | packetUnique lev γ F w z} =
      ⋂ b, ⋂ b', {z | lev b = lev b' → γ b = w → γ b' = w →
        z ∈ F b → z ∈ F b' → b = b'} := by
    ext z
    simp only [packetUnique, mem_ofPred_eq, mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro b'
  exact (MeasurableSet.const (lev b = lev b')).imp
    ((MeasurableSet.const (γ b = w)).imp ((MeasurableSet.const (γ b' = w)).imp
      ((hF b).imp ((hF b').imp (MeasurableSet.const (b = b'))))))

noncomputable def terminalAncestorList {W : ℕ} (p : PathData W) (m : ℕ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin p.C) :=
  (p.lst (m - 1) w o).biUnion (fun b =>
    Finset.univ.image (fun i : Fin m => forestAncestor p.lev p.par b i))

theorem terminalAncestorList_card {W : ℕ} (p : PathData W) (m : ℕ)
    (hlist : ∀ i w o, ((p.lst i w o).card : ℝ) ≤ p.κ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((terminalAncestorList p m w o).card : ℝ) ≤ m * p.κ := by
  classical
  have hn : (terminalAncestorList p m w o).card ≤ (p.lst (m - 1) w o).card * m := by
    calc
      _ ≤ ∑ b ∈ p.lst (m - 1) w o,
          (Finset.univ.image (fun i : Fin m => forestAncestor p.lev p.par b i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ p.lst (m - 1) w o, m := by
        apply Finset.sum_le_sum
        intro b _
        exact Finset.card_image_le.trans (by simp)
      _ = _ := by simp
  calc
    _ ≤ ((p.lst (m - 1) w o).card : ℝ) * m := by exact_mod_cast hn
    _ = (m : ℝ) * (p.lst (m - 1) w o).card := mul_comm _ _
    _ ≤ m * p.κ := mul_le_mul_of_nonneg_left (hlist _ _ _) (Nat.cast_nonneg _)

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.parent_iterate_world_incidence
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (n : ℕ) (hn : n ≤ p.lev b) :
    p.γ (p.par^[n] b) = p.γ b ∧ p.F b ⊆ p.F (p.par^[n] b) := by
  induction n generalizing b with
  | zero => exact ⟨rfl, Subset.rfl⟩
  | succ n ih =>
    have hb : 0 < p.lev b := by omega
    obtain ⟨hlev, hγ, _, hF⟩ := hp.parent b hb
    have hn' : n ≤ p.lev (p.par b) := by omega
    obtain ⟨hγ', hF'⟩ := ih (p.par b) hn'
    rw [Function.iterate_succ_apply]
    exact ⟨hγ'.trans hγ, hF.trans hF'⟩

theorem PathData.Valid.ae_packet_unique
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (w : Fin W) :
    ∀ᵐ z ∂(ν w).prod volume, packetUnique p.lev p.γ p.F w z := by
  apply ae_packetUnique
  intro b b' hne hlev hγ hγ'
  simpa only [hγ] using hp.packet_aedisjoint b b' hne hlev (hγ.trans hγ'.symm)

/-- All current packet labels are predicted at L from the ORIGINAL terminal
list, once shared closed-endpoint overlaps are removed at zero mass cost. -/
theorem PathData.Valid.terminalAncestorList_mem
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (w : Fin W) (z : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hunique : packetUnique p.lev p.γ p.F w z)
    (hterminal : ∃ t, p.lev t = m - 1 ∧ p.γ t = w ∧ z ∈ p.F t)
    (b : Fin p.C) (hbw : p.γ b = w) (hzb : z ∈ p.F b) :
    b ∈ terminalAncestorList p m w (obs (B w) (δ Nk L) z) := by
  classical
  obtain ⟨t, htlev, htw, hzt⟩ := hterminal
  have hbi : p.lev b < m := (hp.2.2.2.2.2.2.2 b).1
  have hbit : p.lev b ≤ p.lev t := by omega
  let a := forestAncestor p.lev p.par t (p.lev b)
  have halev : p.lev a = p.lev b := forestAncestor_level (fun b hb => (hp.parent b hb).1) t _ hbit
  have ha := hp.parent_iterate_world_incidence t (p.lev t - p.lev b) (Nat.sub_le _ _)
  have haw : p.γ a = w := ha.1.trans htw
  have hza : z ∈ p.F a := ha.2 hzt
  have hba : b = a := hunique b a halev.symm hbw haw hzb hza
  have htlist := (hp.2.2.2.2.2.2.2 t).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z hzt
  have hlast : p.r (m - 1) = L := hp.2.2.2.1
  rw [htlev, htw, hlast] at htlist
  apply Finset.mem_biUnion.mpr
  refine ⟨t, htlist, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨⟨p.lev b, hbi⟩, Finset.mem_univ _, hba.symm⟩

/-- The finite success union has short terminal lists even when an earlier
actual depth exceeds L. Only terminal coverage and original endpoint
uniqueness are used, and both have finite old polynomial format. -/
theorem PathData.Valid.prediction_union_known_of_terminal
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (w : Fin W) (eligible : Fin p.C → Prop)
    (helig : ∀ b, eligible b → p.γ b = w)
    {z : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hunique : packetUnique p.lev p.γ p.F w z)
    (hterminal : ∃ t, p.lev t = m - 1 ∧ p.γ t = w ∧ z ∈ p.F t)
    (hz : z ∈ packetPredictionUnion p.F eligible) :
    ∃ b ∈ terminalAncestorList p m w (obs (B w) (δ Nk L) z), eligible b ∧ z ∈ p.F b := by
  obtain ⟨b, hb, hzb⟩ := hz
  exact ⟨b, hp.terminalAncestorList_mem w z hunique hterminal b (helig b hb) hzb, hb, hzb⟩

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
