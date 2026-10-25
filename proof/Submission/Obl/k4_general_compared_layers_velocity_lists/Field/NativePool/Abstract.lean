-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.NativePool.Abstract; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- `pooled_domination` below is adapted from this checkout's accepted o248,
   `Submission/Obl/k4_wide_velocity_lists_scalar_preparation/PoolAbstract.lean`, theorem
   `pooled_terminal` (its pruning half: the conditional palette domination produced by accepted
   o236 `prune_and_forget`, before the velocity-wise lists are integrated). `nativeBox` is the
   four-coordinate analogue of o248's `stateBox` (`PoolBasics.lean`). -/
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning

/-!
# Abstract pruning with conditional palette domination

A finite disjoint family of pieces covers a law; each piece meets only listed states and
carries a reference weight dominating its velocity bins by a palette. Deleting the light
(piece, state) pairs (accepted o236 `prune_and_forget`) leaves a submeasure whose states have
conditional palette domination with constant `δ⁻¹`, at a loss of `δ` times the total weight
of the listed pairs.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

namespace NativePool

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩

/-- The native states within one step of a given one in each of the four coordinates. -/
def nativeBox (σ : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun e => Finset.Icc (σ e - 1) (σ e + 1)

theorem card_nativeBox (σ : Fin 4 → ℤ) : (nativeBox σ).card = 81 := by
  simp only [nativeBox, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_four]
  have h : ∀ z : ℤ, (z + 1 + 1 - (z - 1)).toNat = 3 := by intro z; omega
  rw [h, h, h, h]
  norm_num

theorem mem_nativeBox {σ σ' : Fin 4 → ℤ} (h : ∀ e, σ e - 1 ≤ σ' e ∧ σ' e ≤ σ e + 1) :
    σ' ∈ nativeBox σ := by
  simp only [nativeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  exact h

/-- The listed states of a piece: the box around the state of a chosen point of the piece
outside the bad set, and none when there is no such point. -/
def pieceBox {Ω : Type*} (P bad : Set Ω) (st : Ω → Fin 4 → ℤ) : Finset (Fin 4 → ℤ) := by
  classical
  exact if hx : ∃ ω, ω ∈ P ∧ ω ∉ bad then nativeBox (st (Classical.choose hx)) else ∅

theorem pieceBox_card_le {Ω : Type*} (P bad : Set Ω) (st : Ω → Fin 4 → ℤ) :
    (pieceBox P bad st).card ≤ 81 ∧
      ((pieceBox P bad st).Nonempty → ∃ ω, ω ∈ P ∧ ω ∉ bad) := by
  classical
  by_cases hx : ∃ ω, ω ∈ P ∧ ω ∉ bad
  · have heq : pieceBox P bad st = nativeBox (st (Classical.choose hx)) := by
      simp only [pieceBox, hx, ↓reduceDIte]
    rw [heq, card_nativeBox]
    exact ⟨le_rfl, fun _ => hx⟩
  · have heq : pieceBox P bad st = ∅ := by
      simp only [pieceBox, hx, ↓reduceDIte]
    rw [heq]
    exact ⟨by simp, fun h => absurd h Finset.not_nonempty_empty⟩

/-- A point of a piece outside the bad set has a listed state, as soon as any two such
points have states within one step of each other. -/
theorem mem_pieceBox {Ω : Type*} {P bad : Set Ω} {st : Ω → Fin 4 → ℤ}
    (hbox : ∀ ω ω₀, ω ∈ P → ω ∉ bad → ω₀ ∈ P → ω₀ ∉ bad → st ω ∈ nativeBox (st ω₀))
    {ω : Ω} (hω : ω ∈ P) (hωb : ω ∉ bad) : st ω ∈ pieceBox P bad st := by
  classical
  have hx : ∃ ω, ω ∈ P ∧ ω ∉ bad := ⟨ω, hω, hωb⟩
  simp only [pieceBox, hx, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hx
  exact hbox ω _ hω hωb h1 h2

open Submission.Obl.k4_critical_conditional_row_preparation in
/-- Abstract pruning: a submeasure losing at most `δ` times the total reference weight of the
listed (piece, state) pairs, on which every state has conditional palette domination with
constant `δ⁻¹`. -/
theorem pooled_domination {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [MeasurableSingletonClass O] [Countable O]
    (law : Measure Ω)
    (out : Ω → O) (hout : Measurable out) (vel : Ω → ℤ) (hvel : Measurable vel)
    (π : Measure ℤ)
    {n : ℕ} (R : Fin n → Set Ω) (hR : ∀ i, MeasurableSet (R i))
    (hdisj : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hcover : ∀ᵐ p ∂law, ∃ i, p ∈ R i)
    (options : Fin n → Finset O) (hopt : ∀ i, ∀ᵐ p ∂law, p ∈ R i → out p ∈ options i)
    (W : Fin n → ℝ≥0∞) (hW : ∀ i a, law (R i ∩ vel ⁻¹' {a}) ≤ W i * π {a})
    (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδt : δ ≠ ⊤) :
    ∃ τ : Measure Ω, τ ≤ law ∧
      law univ ≤ τ univ + δ * ∑ i, ((options i).card : ℝ≥0∞) * W i ∧
      ∀ o a, τ {p | out p = o ∧ vel p = a} ≤ δ⁻¹ * π {a} * τ {p | out p = o} := by
  classical
  let state : Ω → Option (Fin n) × O := fun p => (coverLabel R p, out p)
  have hstate : Measurable state := (measurable_coverLabel R hR hdisj).prodMk hout
  have hcap : ∀ q v, law {p | state p = q ∧ vel p = v} ≤
      1 * historyReference options W q * π {v} := by
    rintro ⟨i, o⟩ v
    cases i with
    | none =>
      have hsub : {p | state p = (none, o) ∧ vel p = v} ⊆ {p | ¬ ∃ i, p ∈ R i} := by
        rintro p ⟨hp, -⟩
        exact (coverLabel_eq_none R p).mp (congrArg Prod.fst hp)
      calc _ ≤ law {p | ¬ ∃ i, p ∈ R i} := measure_mono hsub
        _ = 0 := ae_iff.mp hcover
        _ ≤ _ := zero_le
    | some i =>
      by_cases ho : o ∈ options i
      · have hsub : {p | state p = (some i, o) ∧ vel p = v} ⊆ R i ∩ vel ⁻¹' {v} := by
          rintro p ⟨hp, hv⟩
          exact ⟨(coverLabel_eq_some R hdisj p i).mp (congrArg Prod.fst hp), hv⟩
        simp only [historyReference, Option.elim_some, ho, ite_true, one_mul]
        exact (measure_mono hsub).trans (hW i v)
      · have hsub : {p | state p = (some i, o) ∧ vel p = v} ⊆
            {p | ¬ (p ∈ R i → out p ∈ options i)} := by
          rintro p ⟨hp, -⟩ himp
          have hRi := (coverLabel_eq_some R hdisj p i).mp (congrArg Prod.fst hp)
          have hmemo := himp hRi
          rw [show out p = o from congrArg Prod.snd hp] at hmemo
          exact ho hmemo
        calc _ ≤ _ := measure_mono hsub
          _ = 0 := ae_iff.mp (hopt i)
          _ ≤ _ := zero_le
  obtain ⟨τ, hτ, hmass, hdom⟩ := prune_and_forget law state hstate vel hvel π
    (historyReference options W) 1 δ hδ0 hδt Prod.snd measurable_snd hcap
  rw [tsum_historyReference] at hmass
  refine ⟨τ, hτ, hmass, ?_⟩
  intro o a
  have h := hdom o a
  rw [one_div] at h
  exact h

end

end NativePool

end Submission.Obl.k4_general_compared_layers_velocity_lists
