-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ReferencePruning.lean.
import Submission.Obl.k4_finite_affine_parent_sources.MarginalFloors
import Submission.Obl.k4_finite_affine_parent_sources.HistoryPalette

/-! Reference-weight pruning before conditioning on an appended finite state. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Hist Sf : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Hist]
  [DecidableEq Hist] [Fintype Sf] [DecidableEq Sf]

/-- Fixed reference weights pay once for each possible appended state.
The retained history--state entries all have their current reference floor. -/
theorem exists_reference_state_floors
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (history : Ω → Hist) (key : Ω → Sf)
    (reference : Hist → ℝ) (hreference : ∀ h, 0 ≤ reference h)
    (options : Hist → Finset Sf) (J B L : ℝ) (hJ : 0 ≤ J) (hL : 0 < L)
    (hoptions : ∀ h, ((options h).card : ℝ) ≤ J) (hbudget : (∑ h, reference h) ≤ B)
    (hallowed : ∀ e, 0 < P e → key e ∈ options (history e)) :
    ∃ S : Finset Ω, (∀ e ∈ S, 0 < P e) ∧
      (∑ e, P e) - J * B / L ≤ ∑ e ∈ S, P e ∧
      ∀ h s, fiberMass (fun e => if e ∈ S then P e else 0)
          (fun e => (history e, key e)) (h, s) ≠ 0 →
        reference h ≤ L * fiberMass (fun e => if e ∈ S then P e else 0)
          (fun e => (history e, key e)) (h, s) := by
  let U : Finset Ω := univ.filter (fun e => 0 < P e)
  let cells : Hist × Sf → Finset Ω := fun a =>
    univ.filter (fun e => (history e, key e) = a)
  let threshold : Hist × Sf → ℝ := fun a => if a.2 ∈ options a.1 then reference a.1 / L else 0
  have hthreshold : ∀ a, 0 ≤ threshold a := by
    intro a
    dsimp [threshold]
    split_ifs
    · exact div_nonneg (hreference a.1) hL.le
    · rfl
  obtain ⟨S, hSU, hmass, hfloor⟩ := exists_simultaneous_marginal_floors U P cells threshold hthreshold
  have htotal : (∑ a, threshold a) ≤ J * B / L := by
    calc
      _ = ∑ h, ((options h).card : ℝ) * (reference h / L) := by
        simp [threshold, Fintype.sum_prod_type]
      _ ≤ ∑ h, J * (reference h / L) := sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_right (hoptions h) (div_nonneg (hreference h) hL.le)
      _ = J * (∑ h, reference h) / L := by
        rw [← mul_sum, ← sum_div]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hJ) hL.le
  have hmassU : (∑ e ∈ U, P e) = ∑ e, P e := by
    apply sum_subset (subset_univ U)
    intro e _ hnot
    have hn : ¬ 0 < P e := by
      intro h
      exact hnot (mem_filter.mpr ⟨mem_univ e, h⟩)
    exact le_antisymm (le_of_not_gt hn) (hP e)
  refine ⟨S, (fun e he => (mem_filter.mp (hSU he)).2), ?_, ?_⟩
  · rw [hmassU] at hmass
    linarith only [hmass, htotal]
  · intro h s hne
    have hfibre : fiberMass (fun e => if e ∈ S then P e else 0)
        (fun e => (history e, key e)) (h, s) = ∑ e ∈ S ∩ cells (h, s), P e := by
      change (∑ e ∈ cells (h, s), if e ∈ S then P e else 0) = _
      have hset : (cells (h, s)).filter (fun e => e ∈ S) = S ∩ cells (h, s) := by
        ext e
        simp [and_comm]
      rw [← sum_filter, hset]
    have hactive : (S ∩ cells (h, s)).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro hz
      exact hne (by rw [hfibre, hz, sum_empty])
    have hs : s ∈ options h := by
      obtain ⟨e, he⟩ := hactive
      have heS := (mem_inter.mp he).1
      have heU := hSU heS
      have hekeys := (mem_filter.mp (mem_inter.mp he).2).2
      have heallowed := hallowed e (mem_filter.mp heU).2
      rcases Prod.mk.inj hekeys with ⟨hh, hk⟩
      simpa only [hh, hk] using heallowed
    have hlower : reference h / L ≤ fiberMass (fun e => if e ∈ S then P e else 0)
        (fun e => (history e, key e)) (h, s) := by
      simpa only [threshold, hs, ite_true, hfibre] using hfloor (h, s) hactive
    simpa only [mul_comm] using (div_le_iff₀ hL).mp hlower

/-- The retained law has an aggregate conditional palette cap against the
unchanged external palette, after all reference histories are forgotten. -/
theorem exists_reference_palette_restriction
    {Pal : Type*} [DecidableEq Pal]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (history : Ω → Hist) (key : Ω → Sf) (Z : Ω → Pal)
    (reference : Hist → ℝ) (hreference : ∀ h, 0 ≤ reference h)
    (π : Pal → ℝ) (hπ : ∀ z, 0 ≤ π z) (K J B L : ℝ)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hL : 0 < L)
    (options : Hist → Finset Sf) (hoptions : ∀ h, ((options h).card : ℝ) ≤ J)
    (hbudget : (∑ h, reference h) ≤ B)
    (hallowed : ∀ e, 0 < P e → key e ∈ options (history e))
    (hnum : ∀ h z, fiberMass P (fun e => (history e, Z e)) (h, z) ≤ K * reference h * π z) :
    ∃ S : Finset Ω, (∀ e ∈ S, 0 < P e) ∧
      (∑ e, P e) - J * B / L ≤ ∑ e ∈ S, P e ∧
      ∀ e z, (∑ er ∈ univ.filter (fun er => Z er = z),
        condKey (fun e => if e ∈ S then P e else 0) key e er) ≤ (K * L) * π z := by
  obtain ⟨S, hS, hmass, hfloor⟩ := exists_reference_state_floors P hP history key
    reference hreference options J B L hJ hL hoptions hbudget hallowed
  refine ⟨S, hS, hmass, ?_⟩
  have hnonneg : ∀ e, 0 ≤ (if e ∈ S then P e else 0) := by
    intro e
    split_ifs
    · exact hP e
    · rfl
  have hdom : ∀ e, (if e ∈ S then P e else 0) ≤ P e := by
    intro e
    split_ifs
    · rfl
    · exact hP e
  apply conditional_palette_cap_of_history_floors (fun e => if e ∈ S then P e else 0) hnonneg
    history key Z reference π K L hK hL.le hπ hfloor
  intro h z
  refine le_trans ?_ (hnum h z)
  unfold fiberMass
  exact sum_le_sum fun e _ => hdom e

end

end Submission.Obl.k4_finite_affine_parent_sources
