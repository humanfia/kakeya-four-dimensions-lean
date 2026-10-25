-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FiberMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Finset

/-- Balance of fiber cardinalities bounds each fiber by the average cardinality. -/
theorem balanced_fiber_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (S : Finset ι) (f : ι → κ) {L : ℝ}
    (hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      L * (S.filter (fun i => f i = k')).card) (k : κ) :
    ((S.filter (fun i => f i = k)).card : ℝ) * Fintype.card κ ≤ L * S.card := by
  have hsum : (∑ k' : κ, ((S.filter (fun i => f i = k')).card : ℝ)) = S.card := by
    exact_mod_cast (S.card_eq_sum_card_fiberwise (t := univ) (f := f)
      (fun _ _ => mem_univ _)).symm
  have hh := sum_le_sum (s := (univ : Finset κ)) (fun k' _ => hbal k k')
  simpa only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hsum, mul_comm] using hh

/-- An upper bound on each fine weight and balanced fiber sizes bound any selected coarse mass. -/
theorem selected_fiber_mass_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (S : Finset ι) (Q : Finset κ) (f : ι → κ) (a : ι → ℝ) {U L : ℝ}
    (hU : 0 ≤ U) (ha : ∀ i ∈ S, a i ≤ U)
    (hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      L * (S.filter (fun i => f i = k')).card) :
    (∑ i ∈ S with f i ∈ Q, a i) * Fintype.card κ ≤ U * L * S.card * Q.card := by
  have hw (k : κ) : (∑ i ∈ S with f i = k, a i) ≤
      U * (S.filter (fun i => f i = k)).card := by
    calc
      _ ≤ ∑ _i ∈ S with f _i = k, U :=
        sum_le_sum fun i hi => ha i (mem_filter.mp hi).1
      _ = _ := by simp [mul_comm]
  have hmass (k : κ) : (∑ i ∈ S with f i = k, a i) * Fintype.card κ ≤ U * L * S.card := by
    calc
      _ ≤ (U * (S.filter (fun i => f i = k)).card) * Fintype.card κ :=
        mul_le_mul_of_nonneg_right (hw k) (Nat.cast_nonneg _)
      _ = U * ((S.filter (fun i => f i = k)).card * (Fintype.card κ : ℝ)) := by ring
      _ ≤ U * (L * S.card) := mul_le_mul_of_nonneg_left (balanced_fiber_card_le S f hbal k) hU
      _ = _ := by ring
  calc
    (∑ i ∈ S with f i ∈ Q, a i) * Fintype.card κ =
        (∑ k ∈ Q, ∑ i ∈ S with f i = k, a i) * Fintype.card κ := by
      rw [sum_fiberwise_eq_sum_filter]
    _ = ∑ k ∈ Q, (∑ i ∈ S with f i = k, a i) * Fintype.card κ := sum_mul ..
    _ ≤ ∑ _k ∈ Q, U * L * S.card := sum_le_sum fun k _ => hmass k
    _ = U * L * S.card * Q.card := by simp [mul_comm]

/-- Retention of mass forces retention of coarse cardinality when all fibers are balanced.
The reference mass can be larger than the mass of the selected fine family. -/
theorem selected_fiber_card_of_mass {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (S : Finset ι) (Q : Finset κ) (f : ι → κ) (a : ι → ℝ)
    {b c U L M : ℝ} (hb : 0 ≤ b) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hn : 0 < Fintype.card ι) (ha : ∀ i ∈ S, a i ≤ U)
    (hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      L * (S.filter (fun i => f i = k')).card)
    (hdense : c * Fintype.card ι ≤ M)
    (hkeep : b * M ≤ ∑ i ∈ S with f i ∈ Q, a i) :
    b * c * Fintype.card κ ≤ U * L * Q.card := by
  have hn' : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hn
  apply (mul_le_mul_iff_left₀ hn').mp
  calc
    (b * c * Fintype.card κ) * Fintype.card ι =
        (b * (c * Fintype.card ι)) * Fintype.card κ := by ring
    _ ≤ (b * M) * Fintype.card κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdense hb) (Nat.cast_nonneg _)
    _ ≤ (∑ i ∈ S with f i ∈ Q, a i) * Fintype.card κ :=
      mul_le_mul_of_nonneg_right hkeep (Nat.cast_nonneg _)
    _ ≤ U * L * S.card * Q.card := selected_fiber_mass_le S Q f a hU ha hbal
    _ ≤ U * L * Fintype.card ι * Q.card := by
      gcongr
      exact_mod_cast S.card_le_univ
    _ = (U * L * Q.card) * Fintype.card ι := by ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
