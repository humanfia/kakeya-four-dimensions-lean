-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Tree, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Tree.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Tree.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Tree.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.NodeStep
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Dyadic
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.FirstJet

set_option autoImplicit false

/-!
# The time tree and the jet induction, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `ec0250f0`, `Jets/Tree.lean`,
for rows in `(ℝ²)^*` (budget constants follow `Jets2/NodeStep.lean`).

`TTree k`: a binary tree of times of depth `k` (`leaf t`, `node L R`); its root is the root of
its left subtree.  `TTree.Pairs H Kg`: at a node of depth `k + 1` the roots of the two subtrees
are at distance in `[H (k+1) / Kg, H (k+1)]`.

`jet_tree`: given the first-jet inputs (a row `A`, Taylor estimates at the pair scales, and the
lists of `J_1` at every good time) and a per-level budget, every well-formed tree of good times
carries, at its root, rows `F, A, F_2, …, F_{k+1}` and lists of all jets `J_1, …, J_{k+1}` at
width `W k`, on a large subset of any set of trajectories labelled at all its times.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

/-- Binary trees of times. -/
inductive TTree : ℕ → Type
  | leaf (t : ℝ) : TTree 0
  | node {k : ℕ} (L R : TTree k) : TTree (k + 1)

namespace TTree

/-- The root time. -/
def root : {k : ℕ} → TTree k → ℝ
  | _, leaf t => t
  | _, node L _ => L.root

/-- The times of the tree. -/
def Mem (s : ℝ) : {k : ℕ} → TTree k → Prop
  | _, leaf t => s = t
  | _, node L R => L.Mem s ∨ R.Mem s

theorem mem_root : {k : ℕ} → (T : TTree k) → T.Mem T.root
  | _, leaf _ => rfl
  | _, node L _ => Or.inl (mem_root L)

/-- The pair conditions at every node. -/
def Pairs (H : ℕ → ℝ) (Kg : ℝ) : {k : ℕ} → TTree k → Prop
  | _, leaf _ => True
  | _, node (k := k) L R => L.Pairs H Kg ∧ R.Pairs H Kg ∧
      H (k + 1) / Kg ≤ |R.root - L.root| ∧ |R.root - L.root| ≤ H (k + 1)

/-- At every node of depth `k + 1` the two roots lie in a common dyadic cell of level `Tl (k+1)`. -/
def Cells (Tl : ℕ → ℕ) : {k : ℕ} → TTree k → Prop
  | _, leaf _ => True
  | _, node (k := k) L R => L.Cells Tl ∧ R.Cells Tl ∧
      ∃ j : ℤ, L.root ∈ dI (Tl (k + 1)) j ∧ R.root ∈ dI (Tl (k + 1)) j

end TTree

/-- First-jet inputs on a label set `E` (deterministic form of `prop:scalar-normal`): bounded
rows, the Taylor estimate on every dyadic cell of every pair level, and the fine cover of `J_1`
given the scalar bin at the fine width `q₁`. -/
structure FirstJetInput {Λ : Type*} [MeasurableSpace Λ] (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (c : Λ → Fin 7 → ℝ) (A : ℝ → Fin 2 → ℝ) (Good : Set ℝ) (Tl : ℕ → ℕ) (eT : ℕ → ℝ) (Dmax : ℕ)
    (q₁ p₁ : ℝ) (n₁ : ℕ) (B₀ : ℝ) : Prop where
  /-- Rows bounded at good times. -/
  rows_le : ∀ t ∈ Good, ‖F t‖ ≤ B₀ ∧ ‖A t‖ ≤ B₀
  /-- Taylor estimate on every dyadic cell of every pair level. -/
  taylor : ∀ k, 1 ≤ k → k ≤ Dmax → ∀ j : ℤ, ∀ t ∈ Good, ∀ s ∈ Good, t ∈ dI (Tl k) j →
    s ∈ dI (Tl k) j → ‖F s - F t - (s - t) • A t‖ ≤ eT k
  /-- The fine cover of the first jet at every good time. -/
  lists : ∀ t ∈ Good, Determined E (fun l => zS F (c l) t) univ t q₁
    (fun l => jet (leafRows F A t) (c l) t 1) p₁ n₁

/-- The per-level budget of the tree induction: at level `k` the jets are read at scalar width
`W k` with precision `w k`. -/
structure TreeBudget (K ζ Kg Kpop : ℝ) (H eT W w : ℕ → ℝ) (Dmax : ℕ) (n : ℕ → ℕ)
    (BR mass loss CJ : ℕ → ℝ) (Lam δc : ℕ → ℕ → ℝ) (q₁ p₁ : ℝ) (n₁ : ℕ) : Prop where
  hH : ∀ k, 1 ≤ k → k ≤ Dmax → 0 < H k
  hKg : 1 ≤ Kg
  kpop : 0 < Kpop
  pair : ∀ k, k + 1 ≤ Dmax →
    PairBudget K ζ (BR k) (H (k + 1)) Kg (eT (k + 1)) (W k) (w k) (W (k + 1)) (w (k + 1))
      (mass (k + 1) - 2 * loss k) (CJ (k + 1)) (n k) (k + 1) (Lam (k + 1)) (δc (k + 1))
  nstep : ∀ k, k + 1 ≤ Dmax →
    ⌊3 * K * ((4 * PairData.nGrad (n k) (W k) (W k + H (k + 1) * w k +
      PairData.errS K (BR k) (H (k + 1)) (eT (k + 1))) : ℕ) : ℝ) * Kpop⌋₊ ≤ n (k + 1)
  bstep : ∀ k, k + 1 ≤ Dmax → max (BR k) (Lam (k + 1) (k + 1)) ≤ BR (k + 1)
  lstep : ∀ k, k + 1 ≤ Dmax → 2 * loss k + ((k + 1 : ℕ) + 1) * (9600 * K ^ 3 / Kpop) ≤ loss (k + 1)
  mstep : ∀ k, k + 1 ≤ Dmax → mass k ≤ mass (k + 1) - loss k
  loss_nn : ∀ k, 0 ≤ loss k
  /-- the leaf coarsening from the fine first-jet cover -/
  hζq₁ : ζ ≤ q₁
  hq₁W : q₁ ≤ W 0
  hp₁ : 0 ≤ p₁
  hp₁w : p₁ ≤ w 0
  hW0 : W 0 ≤ 1
  hw0 : 0 < w 0
  hCJ0 : 3 + 4 * BR 0 + 2 * 1 * BR 0 ≤ CJ 0
  hwCJ0 : CJ 0 * W 0 ≤ w 0
  n0 : ⌊3 * K * ((n₁ * (⌊2 * p₁ / w 0⌋₊ + 2) : ℕ) : ℝ) * Kpop⌋₊ ≤ n 0
  loss0 : 9600 * K ^ 3 / Kpop ≤ loss 0

variable {Λ : Type*} [MeasurableSpace Λ]

/-- **The jet induction over the tree.** -/
theorem jet_tree {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    (hd1 : d ≤ 1) {A : ℝ → Fin 2 → ℝ} {Good : Set ℝ} {Tl : ℕ → ℕ} {H eT W w : ℕ → ℝ} {Kg Kpop : ℝ}
    {Dmax : ℕ} {n : ℕ → ℕ} {BR mass loss CJ : ℕ → ℝ} {Lam δc : ℕ → ℕ → ℝ} {q₁ p₁ : ℝ} {n₁ : ℕ}
    (hB : TreeBudget K ζ Kg Kpop H eT W w Dmax n BR mass loss CJ Lam δc q₁ p₁ n₁)
    (hFJ : FirstJetInput E F c A Good Tl eT Dmax q₁ p₁ n₁ (BR 0)) (hGood : Good ⊆ Icc 0 1) :
    ∀ k, k ≤ Dmax → ∀ T : TTree k, T.Pairs H Kg → T.Cells Tl → (∀ s, T.Mem s → s ∈ Good) →
      ∀ D : Set Λ, MeasurableSet D → (∀ l ∈ D, ∀ s, T.Mem s → (l, s) ∈ E) →
        ENNReal.ofReal (mass k) ≤ ν D →
      ∃ R : ℕ → Fin 2 → ℝ, R 0 = F T.root ∧ R 1 = A T.root ∧ (∀ i, ‖R i‖ ≤ BR k) ∧
        ∃ D' ⊆ D, MeasurableSet D' ∧ ν (D \ D') ≤ ENNReal.ofReal (loss k) ∧
          NodeLists E F c D' T.root R (k + 1) (W k) (w k) (n k) := by
  intro k
  induction k with
  | zero =>
    intro _ T _ _ hTgood D hD hlab _
    match T with
    | .leaf t =>
      have ht : t ∈ Good := hTgood t rfl
      obtain ⟨hF, hA⟩ := hFJ.rows_le t ht
      have hB0 : 0 ≤ BR 0 := le_trans (norm_nonneg _) hF
      have hRb : ∀ i, ‖leafRows F A t i‖ ≤ BR 0 := by
        intro i
        simp only [leafRows]
        split_ifs
        · exact hF
        · exact hA
        · simpa using hB0
      have hζW : ζ ≤ W 0 := hB.hζq₁.trans hB.hq₁W
      have hCJ : 0 ≤ CJ 0 := le_trans (by positivity) hB.hCJ0
      have hlip : ∀ l ∈ D, ∀ l' ∈ D, (l, t) ∈ E → (l', t) ∈ E → piece (W 0) l = piece (W 0) l' →
          |jet (leafRows F A t) (c l) t 1 - jet (leafRows F A t) (c l') t 1| ≤ CJ 0 * W 0 := by
        intro l _ l' _ hlt _ hpc
        have hdiam := hSN.piece_diam (W 0) hζW hB.hW0 l l' hpc
        have := abs_jet_sub_le (R := leafRows F A t) (j := 1) (hSN.time_mem _ hlt) hRb hdiam
        have hW0 : 0 ≤ W 0 := le_trans hSN.zeta_pos.le hζW
        calc _ ≤ (3 + 4 * BR 0 + 2 * (1 : ℕ) * BR 0) * W 0 := this
          _ ≤ CJ 0 * W 0 := by gcongr; simpa using hB.hCJ0
      obtain ⟨G, hGbad, hGdet, hGmeas⟩ := coarsen_determined hSN hB.hζq₁ hB.hq₁W hB.hW0 hB.hw0
        hB.hp₁ ((hFJ.lists t ht).mono_set (subset_univ D)) (CJ 0) hCJ hlip Kpop hB.kpop
      refine ⟨leafRows F A t, by simp [leafRows, TTree.root], by simp [leafRows, TTree.root],
        hRb, D ∩ G, inter_subset_left,
        hD.inter (hGmeas (measurable_jet hSN.measurable_c _ t 1)), ?_, ?_⟩
      · have hsub : D \ (D ∩ G) ⊆ {l | l ∈ D ∧ (l, t) ∈ E ∧ l ∉ G} := by
          intro l ⟨hl, hn⟩
          exact ⟨hl, hlab l hl t rfl, fun hg => hn ⟨hl, hg⟩⟩
        refine (measure_mono hsub).trans (hGbad.trans (ENNReal.ofReal_le_ofReal ?_))
        have : CJ 0 * W 0 / w 0 ≤ 1 := (div_le_one hB.hw0).mpr hB.hwCJ0
        have hK0 : 0 ≤ K := by linarith [hSN.one_le_K]
        have hKp := hB.kpop
        calc 4800 * K ^ 3 * (CJ 0 * W 0 / w 0 + 1) / Kpop =
              4800 * K ^ 3 / Kpop * (CJ 0 * W 0 / w 0 + 1) := by ring
          _ ≤ 4800 * K ^ 3 / Kpop * 2 := by gcongr; linarith
          _ = 9600 * K ^ 3 / Kpop := by ring
          _ ≤ loss 0 := hB.loss0
      · intro j hj1 hj2
        have hj : j = 1 := le_antisymm hj2 hj1
        subst hj
        exact hGdet.mono le_rfl hB.n0
  | succ k ih =>
    intro hk T hPairs hCells hTgood D hD hlab hmass
    match T, hPairs, hCells with
    | .node L R, ⟨hPL, hPR, hgap1, hgap2⟩, ⟨hCL, hCR, jc, hjL, hjR⟩ =>
      have hk' : k ≤ Dmax := by omega
      have hLgood : ∀ s, L.Mem s → s ∈ Good := fun s hs => hTgood s (Or.inl hs)
      have hRgood : ∀ s, R.Mem s → s ∈ Good := fun s hs => hTgood s (Or.inr hs)
      have hl0 : 0 ≤ loss k := hB.loss_nn k
      have hmk : ENNReal.ofReal (mass k) ≤ ν D := by
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
        have := hB.mstep k hk
        linarith
      -- left subtree
      obtain ⟨RL, hRL0, hRL1, hRLb, D1, hD1D, hD1m, hD1l, hLL⟩ :=
        ih hk' L hPL hCL hLgood D hD (fun l hl s hs => hlab l hl s (Or.inl hs)) hmk
      have hsplit : ∀ {X Y : Set Λ}, Y ⊆ X → ν X ≤ ν Y + ν (X \ Y) := by
        intro X Y hYX
        calc ν X = ν (Y ∪ (X \ Y)) := by rw [union_diff_cancel hYX]
          _ ≤ ν Y + ν (X \ Y) := measure_union_le _ _
      have hmk1 : ENNReal.ofReal (mass k) ≤ ν D1 := by
        have h1 := hsplit hD1D
        have h2 : ENNReal.ofReal (mass (k + 1)) ≤ ν D1 + ENNReal.ofReal (loss k) :=
          hmass.trans (h1.trans (add_le_add le_rfl hD1l))
        have h3 : ENNReal.ofReal (mass (k + 1)) - ENNReal.ofReal (loss k) ≤ ν D1 :=
          tsub_le_iff_right.mpr h2
        rw [← ENNReal.ofReal_sub _ hl0] at h3
        exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [hB.mstep k hk])) h3
      -- right subtree
      obtain ⟨RR, hRR0, hRR1, hRRb, D2, hD2D, hD2m, hD2l, hRL⟩ :=
        ih hk' R hPR hCR hRgood D1 hD1m (fun l hl s hs => hlab l (hD1D hl) s (Or.inr hs)) hmk1
      have hD2D' : D2 ⊆ D := hD2D.trans hD1D
      have hloss2 : ν (D \ D2) ≤ ENNReal.ofReal (2 * loss k) := by
        have : D \ D2 ⊆ (D \ D1) ∪ (D1 \ D2) := by
          intro l ⟨hl, hn⟩
          by_cases h1 : l ∈ D1
          · exact Or.inr ⟨h1, hn⟩
          · exact Or.inl ⟨hl, h1⟩
        calc ν (D \ D2) ≤ ν (D \ D1) + ν (D1 \ D2) := (measure_mono this).trans (measure_union_le _ _)
          _ ≤ ENNReal.ofReal (loss k) + ENNReal.ofReal (loss k) := add_le_add hD1l hD2l
          _ = ENNReal.ofReal (2 * loss k) := by rw [← ENNReal.ofReal_add hl0 hl0]; ring_nf
      have hmD : ENNReal.ofReal (mass (k + 1) - 2 * loss k) ≤ ν D2 := by
        have h1 := hsplit hD2D'
        have h2 : ENNReal.ofReal (mass (k + 1)) ≤ ν D2 + ENNReal.ofReal (2 * loss k) :=
          hmass.trans (h1.trans (add_le_add le_rfl hloss2))
        have h3 : ENNReal.ofReal (mass (k + 1)) - ENNReal.ofReal (2 * loss k) ≤ ν D2 :=
          tsub_le_iff_right.mpr h2
        rwa [← ENNReal.ofReal_sub _ (by linarith)] at h3
      -- the pair
      have hLg := hLgood L.root (TTree.mem_root L)
      have hRg := hRgood R.root (TTree.mem_root R)
      have P : PairData ν c E F piece K ζ d D2 L.root R.root (H (k + 1)) Kg RL RR (BR k)
          (eT (k + 1)) := {
        hSN := hSN, hd1 := hd1, ht := hGood hLg, hs := hGood hRg
        hH := hB.hH (k + 1) le_add_self hk, hKg := hB.hKg
        gap_lo := hgap1, gap_hi := hgap2
        lab := fun l hl => ⟨hlab l (hD2D' hl) L.root (Or.inl (TTree.mem_root L)),
          hlab l (hD2D' hl) R.root (Or.inr (TTree.mem_root R))⟩
        Rt0 := hRL0, Rs0 := hRR0, Rt_le := hRLb, Rs_le := hRRb
        taylor := by
          rw [hRL1]
          exact hFJ.taylor (k + 1) le_add_self hk jc L.root hLg R.root hRg hjL hjR }
      obtain ⟨hR'b, D', hD'D2, hD'l, hD'L, hD'm⟩ := P.node_step (hB.pair k hk) (by omega) hmD
        (hLL.mono_set hD2D) hRL Kpop hB.kpop
      refine ⟨Function.update RL (k + 1 + 1) (PairData.grad RL RR L.root R.root (k + 1)), ?_, ?_,
        fun i => (hR'b i).trans (hB.bstep k hk), D', hD'D2.trans hD2D', hD'm hD2m, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hRL0
      · rw [Function.update_of_ne (by omega)]; exact hRL1
      · -- total loss
        have hsub : D \ D' ⊆ (D \ D2) ∪ (D2 \ D') := by
          intro l ⟨hl, hn⟩
          by_cases h2 : l ∈ D2
          · exact Or.inr ⟨h2, hn⟩
          · exact Or.inl ⟨hl, h2⟩
        have hK0 : 0 ≤ K := by linarith [hSN.one_le_K]
        have hKp := hB.kpop
        have hpos : 0 ≤ ((k + 1 : ℕ) + 1) * (9600 * K ^ 3 / Kpop) := by positivity
        calc ν (D \ D') ≤ ν (D \ D2) + ν (D2 \ D') := (measure_mono hsub).trans (measure_union_le _ _)
          _ ≤ ENNReal.ofReal (2 * loss k) + ENNReal.ofReal (((k + 1 : ℕ) + 1) * (9600 * K ^ 3 / Kpop)) :=
              add_le_add hloss2 hD'l
          _ = ENNReal.ofReal (2 * loss k + ((k + 1 : ℕ) + 1) * (9600 * K ^ 3 / Kpop)) := by
              rw [ENNReal.ofReal_add (by linarith) hpos]
          _ ≤ ENNReal.ofReal (loss (k + 1)) := ENNReal.ofReal_le_ofReal (hB.lstep k hk)
      · intro j hj1 hj2
        exact (hD'L j hj1 hj2).mono le_rfl (hB.nstep k hk)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
