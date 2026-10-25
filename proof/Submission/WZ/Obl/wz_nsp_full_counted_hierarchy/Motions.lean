-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Motions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Equivariance

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped BigOperators

abbrev MotionWord (D : ℕ → ℕ) (j : ℕ) := (i : Fin j) → Fin (D i)

/-- Compose one motion at every edge, keeping the coarser motions outermost. -/
noncomputable def composedMotion (D : ℕ → ℕ) (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)) :
    (j : ℕ) → MotionWord D j → (Space ≃ᵃⁱ[ℝ] Space)
  | 0, _ => AffineIsometryEquiv.refl ℝ Space
  | j + 1, u => (A j (u (Fin.last j))).trans (composedMotion D A j (Fin.init u))

/-- Isometry lets the displacement bounds add at the same original point. -/
theorem composed_displacement (D : ℕ → ℕ)
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)) (t : ℕ → ℝ)
    (J : ℕ) (hA : ∀ j, j < J → ∀ u p, ‖p‖ < 1 → ‖A j u p - p‖ ≤ t j)
    {j : ℕ} (hj : j ≤ J) (u : MotionWord D j) {p : Space} (hp : ‖p‖ < 1) :
    ‖composedMotion D A j u p - p‖ ≤ ∑ i ∈ Finset.range j, t i := by
  induction j with
  | zero => simp [composedMotion]
  | succ j ih =>
      have hij := ih (by omega) (Fin.init u)
      have hij' : dist (composedMotion D A j (Fin.init u) p) p ≤
          ∑ i ∈ Finset.range j, t i := by simpa only [dist_eq_norm] using hij
      have ha := hA j (by omega) (u (Fin.last j)) p hp
      have ha' : dist (A j (u (Fin.last j)) p) p ≤ t j := by
        simpa only [dist_eq_norm] using ha
      change dist (composedMotion D A j (Fin.init u) (A j (u (Fin.last j)) p)) p ≤ _
      calc
        dist (composedMotion D A j (Fin.init u) (A j (u (Fin.last j)) p)) p ≤
            dist (A j (u (Fin.last j)) p) p + dist (composedMotion D A j (Fin.init u) p) p := by
          simpa only [AffineIsometryEquiv.dist_map] using
            dist_triangle (composedMotion D A j (Fin.init u) (A j (u (Fin.last j)) p))
              (composedMotion D A j (Fin.init u) p) p
        _ ≤ t j + ∑ i ∈ Finset.range j, t i := add_le_add ha' hij'
        _ = ∑ i ∈ Finset.range (j + 1), t i := by rw [Finset.sum_range_succ, add_comm]

/-- The prefix determines the copied parent; the last motion labels siblings. -/
def copiedParent {D n : ℕ → ℕ} (f : ∀ j, Fin (n (j + 1)) → Fin (n j)) (j : ℕ)
    (s : MotionWord D (j + 1) × Fin (n (j + 1))) : MotionWord D j × Fin (n j) :=
  ⟨Fin.init s.1, f j s.2⟩

/-- Count an arbitrary predicate on the children of one copied parent. -/
theorem copied_fiber_pred {D n : ℕ → ℕ}
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j)) (j : ℕ)
    (u : MotionWord D j) (k : Fin (n j)) (P : Fin (D j) → Fin (n (j + 1)) → Prop) :
    Set.ncard {s : MotionWord D (j + 1) × Fin (n (j + 1)) |
      copiedParent f j s = (u, k) ∧ P (s.1 (Fin.last j)) s.2} =
      Set.ncard {s : Fin (D j) × Fin (n (j + 1)) | f j s.2 = k ∧ P s.1 s.2} := by
  classical
  apply Set.ncard_congr (fun s _ => (s.1 (Fin.last j), s.2))
  · intro s hs
    exact ⟨congrArg Prod.snd hs.1, hs.2⟩
  · intro s s' hs hs' he
    apply Prod.ext
    · have hi : Fin.init s.1 = Fin.init s'.1 :=
        (congrArg Prod.fst hs.1).trans (congrArg Prod.fst hs'.1).symm
      have hl : s.1 (Fin.last j) = s'.1 (Fin.last j) := congrArg Prod.fst he
      funext t
      exact Fin.lastCases hl (fun i => congrFun hi i) t
    · exact congrArg (fun q : Fin (D j) × Fin (n (j + 1)) => q.2) he
  · intro s hs
    refine ⟨(Fin.snoc (α := fun i : Fin (j + 1) => Fin (D i)) u s.1, s.2), ?_, ?_⟩
    · change (Fin.init (Fin.snoc (α := fun i : Fin (j + 1) => Fin (D i)) u s.1), f j s.2) = (u, k) ∧
        P ((Fin.snoc (α := fun i : Fin (j + 1) => Fin (D i)) u s.1) (Fin.last j)) s.2
      simpa only [Fin.init_snoc, Fin.snoc_last, Prod.mk.injEq, true_and, Set.mem_ofPred_eq] using hs
    · simp only [Fin.snoc_last]

/-- Cardinality of the motion words is exactly the product of stage counts. -/
theorem card_motionWord (D : ℕ → ℕ) (j : ℕ) :
    Fintype.card (MotionWord D j) = ∏ i ∈ Finset.range j, D i := by
  simp only [MotionWord, Fintype.card_pi, Fintype.card_fin]
  exact Fin.prod_univ_eq_prod_range D j

/-- Every copied parent receives one copy of its original fiber for each new motion. -/
theorem copied_fiber_card {D n : ℕ → ℕ}
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j)) (j : ℕ)
    (u : MotionWord D j) (k : Fin (n j)) :
    Set.ncard {s : MotionWord D (j + 1) × Fin (n (j + 1)) | copiedParent f j s = (u, k)} =
      D j * Set.ncard {i | f j i = k} := by
  classical
  have hc := copied_fiber_pred f j u k (fun _ _ => True)
  simp only [and_true] at hc
  rw [hc]
  have he : {s : Fin (D j) × Fin (n (j + 1)) | f j s.2 = k} =
      (Set.univ : Set (Fin (D j))) ×ˢ {i | f j i = k} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [he, Set.ncard_prod]
  simp

/-- Apply all coarser motions to each local buffered containment. -/
theorem copied_containment (D n : ℕ → ℕ)
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space))
    (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j)) (r : ℕ → ℝ)
    (j : ℕ)
    (hsub : ∀ a i, Tube (r (j + 1)) (A j a (x (j + 1) i))
      ((A j a).linear (v (j + 1) i)) ⊆ Tube (r j) (x j (f j i)) (v j (f j i)))
    (s : MotionWord D (j + 1) × Fin (n (j + 1))) :
    Tube (r (j + 1)) (composedMotion D A (j + 1) s.1 (x (j + 1) s.2))
      ((composedMotion D A (j + 1) s.1).linear (v (j + 1) s.2)) ⊆
    Tube (r j) (composedMotion D A j (copiedParent f j s).1 (x j (copiedParent f j s).2))
      ((composedMotion D A j (copiedParent f j s).1).linear (v j (copiedParent f j s).2)) := by
  exact rigid_containment (composedMotion D A j (Fin.init s.1))
    (hsub (s.1 (Fin.last j)) s.2)

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
