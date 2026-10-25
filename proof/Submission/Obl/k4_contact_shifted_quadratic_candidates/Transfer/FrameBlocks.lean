/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameBlocks.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameGood

/-!
# Residual blocks and the residual incidence law

A retained node lies in the parent block. Its residual block is the image of
its original block in parent time `τ = (t - t₀) / q₀ = 2^T₀ * t - j₀`, with
length `q / q₀`. The residual incidence law of a product of a trajectory set
and a residual block is the original core mass of the original block,
divided by the parent reference.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (f : Frame D k s₀ U')

theorem block_eq_dyadic (h : ℕ) (i : Fin (f.nl h)) :
    f.block h i = dyadicBlock (f.Tl h) (D.j k (f.depth h) i) := rfl

theorem time_eq (t : ℝ) :
    (t - f.t₀) / f.q₀ = (2 : ℝ) ^ f.T₀ * t - (D.j k (f.depth 0) f.i₀ : ℕ) := by
  simp only [t₀, q₀, left, T₀]
  field_simp

theorem toChart_snd (p : α × ℝ) :
    (f.toChart p).2 = (2 : ℝ) ^ f.T₀ * p.2 - (D.j k (f.depth 0) f.i₀ : ℕ) :=
  f.time_eq p.2

theorem ql_pos (h : ℕ) : 0 < f.ql h := by unfold ql; positivity

theorem q₀_eq : f.q₀ = f.ql 0 := by
  simp [q₀, ql, T₀, zpow_neg, zpow_natCast]

/-- The parent block exponent is at most that of a node meeting the core. -/
theorem T₀_le {h : ℕ} {i : Fin (f.nl h)} (hsub : f.block h i ⊆ f.block 0 f.i₀) :
    f.T₀ ≤ f.Tl h :=
  dyadic_exponent_le hsub

/-- The residual block index, without the reduction modulo the block count. -/
theorem resj_val {h : ℕ} {i : Fin (f.retained h).card}
    (hsub : f.block h (f.node h i).1 ⊆ f.block 0 f.i₀) :
    (((f.level h).j i : ℕ)) =
      (D.j k (f.depth h) (f.node h i).1 : ℕ) - (D.j k (f.depth 0) f.i₀ : ℕ) * 2 ^ f.resT h := by
  have hoff := dyadic_offset hsub
  simp only [level]
  exact Nat.mod_eq_of_lt hoff.2

/-- In parent time the residual block of a retained label is its original block. -/
theorem mem_resBlock_time {h : ℕ} {i : Fin (f.retained h).card}
    (hsub : f.block h (f.node h i).1 ⊆ f.block 0 f.i₀) (t : ℝ) :
    (t - f.t₀) / f.q₀ ∈ Data.I (f.level h).T ((f.level h).j i) ↔
      t ∈ f.block h (f.node h i).1 := by
  rw [time_eq, block_eq_dyadic, dyadic_parent_time hsub t]
  have hj := f.resj_val hsub
  change _ ∈ dyadicBlock (f.resT h) ((f.level h).j i : ℕ) ↔ _
  rw [hj]
  rfl

theorem mem_resBlock_iff {h : ℕ} {i : Fin (f.retained h).card}
    (hsub : f.block h (f.node h i).1 ⊆ f.block 0 f.i₀) (p : α × ℝ) :
    (f.toChart p).2 ∈ Data.I (f.level h).T ((f.level h).j i) ↔
      p.2 ∈ f.block h (f.node h i).1 := by
  rw [toChart_snd, block_eq_dyadic, dyadic_parent_time hsub p.2]
  have hj := f.resj_val hsub
  change _ ∈ dyadicBlock (f.resT h) ((f.level h).j i : ℕ) ↔ _
  rw [hj]
  rfl

end Frame

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
