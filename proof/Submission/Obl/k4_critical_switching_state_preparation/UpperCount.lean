/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/UpperCount.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/UpperCount.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.TrueDescendants
import Submission.Obl.k4_critical_switching_state_preparation.TrueBoxes
import Submission.Obl.k4_critical_switching_state_preparation.ContactReference
import Submission.Obl.k4_critical_switching_state_preparation.PairBudget

namespace Submission.Obl.k4_critical_switching_state_preparation

open Inherited Finset Set

noncomputable section

/-- The geometric certificate supplied by one normalized true descendant.
The midpoint intercept remains in the original hidden-variable units. -/
structure ContactPiece (K δ a H : ℝ) where
  pairs : Finset (ℤ × (Fin 3 → ℤ))
  point : ℤ × (Fin 3 → ℤ) → Fin 3 → ℝ
  value : ℤ × (Fin 3 → ℤ) → ℝ
  predictor : Fin 4 → ℝ
  box : Fin 5 → ℝ
  midpoint : ℝ
  slopeBound : ℝ
  slope_nonneg : 0 ≤ slopeBound
  time_bound : |midpoint| ≤ 1
  velocity_bound : |box 1| ≤ K
  position_bound : |box 0 + midpoint * box 1| ≤ K
  center_bound : |box 3 + box 0 + midpoint * box 1| ≤ K * H
  tilt_bound : |box 4 - midpoint| ≤ K * H
  predictor_bound : ∀ i : Fin 3, |predictor i.succ| ≤ slopeBound
  mesh_bound : 3 * slopeBound * δ ≤ K * a
  point_mem : ∀ u ∈ pairs, point u ∈ contactGridCell δ u.2 ∧
    point u ∈ horizontalTrueBox box midpoint H K
  bin_eq : ∀ u ∈ pairs, ⌊value u / a⌋ = u.1
  fitted : ∀ u ∈ pairs, |value u - affineBaseEval predictor (point u)| ≤ 2 * K * a

/-- Every certified descendant pays its complete fourth-power domain volume. -/
theorem ContactPiece.pair_count {K δ a H : ℝ} (p : ContactPiece K δ a H)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ)
    (hδH : δ ≤ H ^ 2) (ha : 0 < a) :
    (p.pairs.card : ℝ) * δ ^ 3 ≤ 4194304 * K ^ 4 * H ^ 4 :=
  true_box_intercept_pair_count p.pairs p.point p.value p.predictor p.box
    p.midpoint H K δ a p.slopeBound hH hH1 hK hδ hδH ha p.slope_nonneg
    p.time_bound p.velocity_bound p.position_bound p.center_bound p.tilt_bound
    p.predictor_bound p.mesh_bound p.point_mem p.bin_eq p.fitted

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The complete occupied-pair upper count: original full assignment floors,
actual nested time blocks, and one contact certificate per true descendant.
The auxiliary grid cancels, leaving exactly the hidden-depth ratio. -/
theorem AssignmentLevel.occupied_pair_upper_bound (h : cfg.Valid) {k : ℕ} {s t : ℝ}
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k t)
    (ip : Fin (cfg.n k s)) (S : Finset (Fin (cfg.n k t)))
    (hsub : ∀ i ∈ S, cfg.A k t i ⊆ cfg.A k s ip)
    (htime : ∀ i ∈ S,
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip))
    (K δ a : ℝ) (hK : 1 ≤ K) (hδ : 0 < δ) (ha : 0 < a)
    (hH1 : cfg.timeLength k t / cfg.timeLength k s ≤ 1)
    (hmesh : δ ≤ (cfg.timeLength k t / cfg.timeLength k s) ^ 2)
    (pieces : Fin (cfg.n k t) → ContactPiece K δ a
      (cfg.timeLength k t / cfg.timeLength k s))
    (F : Finset (ℤ × (Fin 3 → ℤ))) (hcover : F ⊆ S.biUnion (fun i => (pieces i).pairs)) :
    (F.card : ℝ) * δ ^ 3 ≤ 4194304 * K ^ 4 * cfg.K k ^ 4 *
      (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hq : 0 < cfg.timeLength k t := cfg.timeLength_pos k t
  have hqp : 0 < cfg.timeLength k s := cfg.timeLength_pos k s
  have hD : 0 ≤ (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by positivity
  have hcount := parent.true_descendant_count h child ip S hsub htime
  have hratio : (2 : ℝ) ^ cfg.T k t / (2 : ℝ) ^ cfg.T k s =
      cfg.timeLength k s / cfg.timeLength k t := by
    simp [timeLength, div_eq_mul_inv, mul_comm]
  rw [hratio] at hcount
  have hcount' : (S.card : ℝ) ≤ (cfg.K k ^ 2) ^ 2 *
      (cfg.timeLength k s / cfg.timeLength k t) ^ 4 *
      (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by
    convert hcount using 1
    ring
  have hlocal (i : Fin (cfg.n k t)) (hi : i ∈ S) :
      ((pieces i).pairs.card : ℝ) ≤ (4194304 * K ^ 4) *
        (cfg.timeLength k t / cfg.timeLength k s) ^ 4 / δ ^ 3 := by
    exact (le_div_iff₀ (by positivity : 0 < δ ^ 3)).mpr
      ((pieces i).pair_count (div_pos hq hqp) hH1 hK hδ hmesh ha)
  have hbudget := occupied_pair_budget_cancel S (fun i => (pieces i).pairs) F
    (K := cfg.K k ^ 2) (C := 4194304 * K ^ 4)
    (q := cfg.timeLength k t) (qp := cfg.timeLength k s)
    (D := (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d)
    (ω := δ) (by positivity) (by positivity) hq hqp hD hδ hcount' hcover hlocal
  convert hbudget using 1
  ring

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
