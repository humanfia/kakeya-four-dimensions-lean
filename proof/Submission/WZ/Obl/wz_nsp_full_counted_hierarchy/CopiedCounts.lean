-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.CopiedCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Motions

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The local count furnished by the single-scale theorem survives every outer
motion and the copied-parent indexing. -/
theorem copied_convex_counts (D n : ℕ → ℕ)
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space))
    (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (j : ℕ) (r L : ℝ)
    (hlocal : ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {q : Fin (D j) × Fin (n (j + 1)) |
        f j q.2 = k ∧ Tube r (A j q.1 (x (j + 1) q.2))
          ((A j q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * r ^ 2) ≤
        ENNReal.ofReal L * volume W)
    (u : MotionWord D j) (k : Fin (n j)) (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal ((Set.ncard {s : MotionWord D (j + 1) × Fin (n (j + 1)) |
      copiedParent f j s = (u, k) ∧
      Tube r (composedMotion D A (j + 1) s.1 (x (j + 1) s.2))
        ((composedMotion D A (j + 1) s.1).linear (v (j + 1) s.2)) ⊆ W} : ℝ) * r ^ 2) ≤
      ENNReal.ofReal L * volume W := by
  let P : Fin (D j) → Fin (n (j + 1)) → Prop := fun a i =>
    Tube r (composedMotion D A j u (A j a (x (j + 1) i)))
      ((composedMotion D A j u).linear ((A j a).linear (v (j + 1) i))) ⊆ W
  have he : {s : MotionWord D (j + 1) × Fin (n (j + 1)) |
      copiedParent f j s = (u, k) ∧
      Tube r (composedMotion D A (j + 1) s.1 (x (j + 1) s.2))
        ((composedMotion D A (j + 1) s.1).linear (v (j + 1) s.2)) ⊆ W} =
      {s | copiedParent f j s = (u, k) ∧ P (s.1 (Fin.last j)) s.2} := by
    ext s
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro hs
    have hu : Fin.init s.1 = u := congrArg Prod.fst hs
    change (Tube r (composedMotion D A j (Fin.init s.1)
      (A j (s.1 (Fin.last j)) (x (j + 1) s.2)))
      ((composedMotion D A j (Fin.init s.1)).linear
        ((A j (s.1 (Fin.last j))).linear (v (j + 1) s.2))) ⊆ W) ↔ _
    rw [hu]
  rw [he, copied_fiber_pred f j u k P]
  exact rigid_convex_counts
    (fun q : Fin (D j) × Fin (n (j + 1)) => A j q.1 (x (j + 1) q.2))
    (fun q : Fin (D j) × Fin (n (j + 1)) => (A j q.1).linear (v (j + 1) q.2))
    (fun q => f j q.2 = k) (composedMotion D A j u) (hlocal k) W hW

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
