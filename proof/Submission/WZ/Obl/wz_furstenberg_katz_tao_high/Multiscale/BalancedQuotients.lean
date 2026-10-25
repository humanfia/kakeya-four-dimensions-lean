-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.BalancedQuotients.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0572, Multiscale/BalancedQuotients.lean; namespace renamed.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.UniformFibers
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.BranchBalance

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- Balancing both levels of a quotient balances the resulting coarse fibers. -/
theorem balanced_image {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (q : α → β) (p : β → γ) {K : ℝ} (hK : 0 ≤ K)
    (hq : Balanced S q K) (hp : Balanced S (p ∘ q) K) :
    Balanced (S.image q) p (K ^ 2) := by
  classical
  have heq (x : α) : branchFiber S (p ∘ q) q x = leafFiber (S.image q) p (q x) := by
    ext b
    simp only [branchFiber, leafFiber, Finset.mem_image, Finset.mem_filter, Function.comp_apply]
    constructor
    · rintro ⟨a, ⟨ha, hap⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hap⟩
    · rintro ⟨⟨a, ha, rfl⟩, hap⟩
      exact ⟨a, ⟨ha, hap⟩, rfl⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  rw [← heq x, ← heq y]
  exact branch_balance_of_leaf_balance S (p ∘ q) q hK
    (fun _ _ h => congrArg p h) hp hq x hx y hy

/-- A balanced quotient preserves the relative size of every union of fibers,
up to the balancing factor. Both inequalities avoid division. -/
theorem balanced_image_filter_counts {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (q : α → β) {K : ℝ} (hbal : Balanced S q K)
    (P : β → Prop) [DecidablePred P] :
    (S.card : ℝ) * ((S.image q).filter P).card ≤
      K * (S.image q).card * (S.filter (fun a => P (q a))).card ∧
    ((S.image q).card : ℝ) * (S.filter (fun a => P (q a))).card ≤
      K * S.card * ((S.image q).filter P).card := by
  classical
  let U := (S.image q).filter P
  let V := S.filter (fun a => P (q a))
  have hvimage : V.image q = U := by
    ext b
    simp only [V, U, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hp⟩
    · rintro ⟨⟨a, ha, rfl⟩, hp⟩
      exact ⟨a, ⟨ha, hp⟩, rfl⟩
  have hsum : (V.card : ℝ) = ∑ b ∈ U, ((S.filter (fun a => q a = b)).card : ℝ) := by
    have hh : (V.card : ℝ) = ∑ b ∈ V.image q, ((V.filter (fun a => q a = b)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image q V
    rw [hvimage] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro b hb
    have hPb := (Finset.mem_filter.mp hb).2
    congr 2
    ext a
    simp only [V, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, heq⟩
      exact ⟨ha, heq⟩
    · rintro ⟨ha, heq⟩
      exact ⟨⟨ha, by rwa [heq]⟩, heq⟩
  have hbounds (b : β) (hb : b ∈ U) :
      ((S.image q).card : ℝ) * (S.filter (fun a => q a = b)).card ≤ K * S.card ∧
      (S.card : ℝ) ≤ K * (S.image q).card * (S.filter (fun a => q a = b)).card := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hb).1
    have heq : S.filter (fun x => q x = q a) = leafFiber S q a := by
      ext x
      simp [leafFiber]
    rw [heq]
    exact balanced_fiber_card_bounds S q hbal ha
  constructor
  · calc
      (S.card : ℝ) * U.card = ∑ _b ∈ U, (S.card : ℝ) := by simp [mul_comm]
      _ ≤ ∑ b ∈ U, K * (S.image q).card * ((S.filter (fun a => q a = b)).card : ℝ) :=
        Finset.sum_le_sum fun b hb => (hbounds b hb).2
      _ = K * (S.image q).card * V.card := by rw [hsum, Finset.mul_sum]
  · calc
      ((S.image q).card : ℝ) * V.card =
          ∑ b ∈ U, ((S.image q).card : ℝ) * (S.filter (fun a => q a = b)).card := by
        rw [hsum, Finset.mul_sum]
      _ ≤ ∑ _b ∈ U, K * (S.card : ℝ) := Finset.sum_le_sum fun b hb => (hbounds b hb).1
      _ = K * S.card * U.card := by simp [mul_comm, mul_left_comm]

/-- Normalized counting bounds pass from a balanced family to its quotient. -/
theorem balanced_image_filter_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (hS : S.Nonempty) (q : α → β) {K A : ℝ} (hK : 0 ≤ K)
    (hbal : Balanced S q K) (P : β → Prop) [DecidablePred P]
    (hcount : ((S.filter (fun a => P (q a))).card : ℝ) ≤ A * S.card) :
    (((S.image q).filter P).card : ℝ) ≤ K * A * (S.image q).card := by
  have hSp : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hh := (balanced_image_filter_counts S q hbal P).1
  apply (mul_le_mul_iff_right₀ hSp).mp
  calc
    _ ≤ K * (S.image q).card * (S.filter (fun a => P (q a))).card := hh
    _ ≤ K * (S.image q).card * (A * S.card) :=
      mul_le_mul_of_nonneg_left hcount (mul_nonneg hK (Nat.cast_nonneg _))
    _ = _ := by ring

/-- Spatial nonconcentration survives balanced quantization, with its radius
increased by the quantization error. -/
theorem balanced_quantized_count {α β E : Type*} [DecidableEq α] [DecidableEq β]
    [PseudoMetricSpace E] (S : Finset α) (hS : S.Nonempty) (q : α → β)
    (x : α → E) (y : β → E) {K C r e σ : ℝ} (hK : 0 ≤ K)
    (hbal : Balanced S q K) (he : 0 ≤ e)
    (hclose : ∀ a ∈ S, dist (x a) (y (q a)) ≤ e)
    (hcount : ∀ z ρ, r ≤ ρ →
      ((S.filter (fun a => dist (x a) z ≤ ρ)).card : ℝ) ≤ C * ρ ^ σ * S.card) :
    ∀ z ρ, r ≤ ρ →
      (((S.image q).filter (fun b => dist (y b) z ≤ ρ)).card : ℝ) ≤
        K * (C * (ρ + e) ^ σ) * (S.image q).card := by
  classical
  intro z ρ hρ
  apply balanced_image_filter_bound S hS q hK hbal
  calc
    _ ≤ ((S.filter (fun a => dist (x a) z ≤ ρ + e)).card : ℝ) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      obtain ⟨ha, hya⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      have ht := dist_triangle (x a) (y (q a)) z
      linarith [hclose a ha]
    _ ≤ _ := hcount z (ρ + e) (by linarith)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
