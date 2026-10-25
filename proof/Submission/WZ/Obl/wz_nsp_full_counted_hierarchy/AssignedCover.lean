-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.AssignedCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.RegularSource
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Equivariance

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts counts_mono)
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- A cover with all unused indices removed, recording counts at an enlarged radius. -/
structure AssignedCover (δ ρ R L : ℝ) (m : ℕ) (x v : Fin m → Space) where
  n : ℕ
  z : Fin n → Space
  w : Fin n → Space
  assign : Fin m → Fin n
  onto : Function.Surjective assign
  unit : ∀ i, ‖w i‖ = 1
  contains : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (assign i)) (w (assign i))
  counts : Counts R L n z w

/-- Restrict any assigned cover to its occupied indices. -/
theorem occupied_cover {δ ρ R L : ℝ} {m n : ℕ} {x v : Fin m → Space}
    (y w : Fin n → Space) (f : Fin m → Fin n)
    (hw : ∀ i, ‖w i‖ = 1)
    (hsub : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i)))
    (hcount : Counts R L n y w) : Nonempty (AssignedCover δ ρ R L m x v) := by
  classical
  let I := Set.range f
  let k := Fintype.card I
  let e : Fin k ≃ I := (Fintype.equivFin I).symm
  let q : Fin k → Fin n := fun i => (e i).val
  let g : Fin m → Fin k := fun i => e.symm ⟨f i, ⟨i, rfl⟩⟩
  have hqg (i) : q (g i) = f i := by simp [q, g]
  have hg : Function.Surjective g := by
    intro i
    obtain ⟨s, hs⟩ := (e i).property
    refine ⟨s, ?_⟩
    apply e.injective
    apply Subtype.val_injective
    simpa only [g, Equiv.apply_symm_apply] using hs
  exact ⟨⟨k, y ∘ q, w ∘ q, g, hg, (fun i => hw (q i)),
    (fun i => by simpa only [Function.comp_apply, hqg] using hsub i),
    counts_injective y w q (Subtype.val_injective.comp e.injective) hcount⟩⟩

/-- Global convex counts are invariant under a common rigid motion. -/
theorem counts_rigid {r L : ℝ} {m : ℕ} {x v : Fin m → Space}
    (A : Space ≃ᵃⁱ[ℝ] Space) (hc : Counts r L m x v) :
    Counts r L m (fun i => A (x i)) (fun i => A.linear (v i)) := by
  have hh := rigid_convex_counts (r := r) (L := L) x v (fun _ => True) A
    (by simpa only [Counts, true_and] using hc)
  simpa only [Counts, true_and] using hh

/-- A collection of occupied raw covers yields a buffered tree by choosing a
fine representative for each child and using its assignment at the parent scale. -/
theorem regularize_assigned_covers {δ a u : ℝ} {B J Q m : ℕ}
    (hδ : 0 < δ) (hJ : 0 < J) (hJB : J + 2 ≤ B) (hQ : 0 < Q)
    (x v : Fin m → Space) (hm : 0 < m) (hv : ∀ i, ‖v i‖ = 1)
    (s r : ℕ → ℝ) (H : ∀ j, AssignedCover δ (s j) (r j) (δ ^ (-u)) m x v)
    (e : Fin m ≃ Fin (H J).n)
    (he : ∀ i, (H J).z (e i) = x i ∧ (H J).w (e i) = v i)
    (hroot : (H 0).n = 1)
    (hr0 : r 0 = (1 / 100 : ℝ)) (hrJ : r J = δ)
    (htop : δ ^ (a / 2) ≤ (1 / 100 : ℝ)) (hcard : (m : ℝ) ≤ δ ^ (-7 : ℝ))
    (hscale : ∀ j, j ≤ J → 0 < s j ∧ r j ≤ 32 * s j ∧ δ ≤ r j ∧ r j ≤ 1 / 100)
    (hball : ∀ j, j ≤ J → ∀ i, Tube (r j) ((H j).z i) ((H j).w i) ⊆
      Metric.ball 0 (3 / 4 : ℝ))
    (hedge : ∀ j, j < J → r j = 32 * s j ∧ 16 * s (j + 1) ≤ s j ∧
      16 * r (j + 1) ≤ r j ∧ δ ^ (a / 2) * r j ≤ r (j + 1))
    (color : ℕ → Fin Q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ m → 0 < b → b ≤ m →
      color a = color b → (a : ℝ) ≤ (4 / 3 : ℝ) * b) :
    ∃ (m' : ℕ) (c : Fin m' → Fin m), Function.Injective c ∧
      m ≤ Q ^ (J + 1) * m' ∧ SourceTower Tube δ a u B m' (x ∘ c) (v ∘ c) := by
  classical
  let n (j) := (H j).n
  let z (j) := (H j).z
  let w (j) := (H j).w
  let rep (j) := Function.surjInv (H j).onto
  have hrep (j) (i) : (H j).assign (rep j i) = i := Function.surjInv_eq (H j).onto i
  let f (j) (i : Fin (n (j + 1))) : Fin (n j) := (H j).assign (rep (j + 1) i)
  let p (j) (i : Fin (n J)) : Fin (n j) :=
    if hj : j ≤ J then ancestor f hj i else (H j).assign (e.symm i)
  have hp (j) (hj : j ≤ J) (i) : p j i = ancestor f hj i := dite_eq_left hj
  have hcoh (j) (hj : j < J) (i) : f j (p (j + 1) i) = p j i := by
    rw [hp (j + 1) (by omega), hp j (by omega)]
    have hcomp := ancestor_comp f (show j ≤ j + 1 by omega) (show j + 1 ≤ J by omega) i
    simpa only [ancestor_succ f (Nat.le_refl j), ancestor_self] using hcomp
  have hnest (j k) (hjk : j ≤ k) (hk : k < J + 1) (i i')
      (hi : p k i = p k i') : p j i = p j i' := by
    calc
      p j i = ancestor f hjk (p k i) := by
        rw [hp j (by omega), hp k (by omega), ancestor_comp]
      _ = ancestor f hjk (p k i') := congrArg (ancestor f hjk) hi
      _ = p j i' := by
        rw [hp j (by omega), hp k (by omega), ancestor_comp]
  have hmJ : m = n J := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hbuf (j) (hj : j < J) (i : Fin (n (j + 1))) :
      Tube (r (j + 1)) (z (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j / 4) (z j (f j i)) (w j (f j i)) := by
    have hc := (H (j + 1)).contains (rep (j + 1) i)
    rw [hrep] at hc
    apply (enlarged_common_descendant (R := r (j + 1)) hδ
      (hscale (j + 1) (by omega)).1 (hv _) ((H (j + 1)).unit i)
      hc ((H j).contains (rep (j + 1) i))).trans
    apply Metric.thickening_mono
    obtain ⟨hr, hs, _, _⟩ := hedge j hj
    have hb := (hscale (j + 1) (by omega)).2.1
    have hspos := (hscale j (by omega)).1
    rw [hr]
    linarith
  obtain ⟨m', c, hc, hmass, hsource⟩ := regularize_source_tower hJ hJB hQ r n z w f p
    hcoh (fun i => by rw [hp J le_rfl]; exact ancestor_self f J i) hnest color
    (by simpa only [← hmJ] using hcolor) hr0 hrJ hroot (hmJ ▸ hm) htop (hmJ ▸ hcard)
    (fun j hj => ⟨(hscale j hj).2.2.1, (hscale j hj).2.2.2,
      (fun i => ⟨(H j).unit i, hball j hj i⟩), (H j).counts⟩)
    (fun j hj => ⟨(hedge j hj).2.2.1, (hedge j hj).2.2.2, hbuf j hj⟩)
  have hz : z J ∘ c = x ∘ (e.symm ∘ c) := by
    funext i
    simpa only [z, Function.comp_apply, Equiv.apply_symm_apply] using (he (e.symm (c i))).1
  have hw : w J ∘ c = v ∘ (e.symm ∘ c) := by
    funext i
    simpa only [w, Function.comp_apply, Equiv.apply_symm_apply] using (he (e.symm (c i))).2
  exact ⟨m', e.symm ∘ c, e.symm.injective.comp hc, hmJ ▸ hmass, hz ▸ hw ▸ hsource⟩

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
