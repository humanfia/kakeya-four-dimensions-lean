-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Counting
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

abbrev Balanced {m k : ℕ} (S : Finset (Fin m)) (f : Fin m → Fin k) (R : ℝ) : Prop :=
  WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced S f R

/-- Pigeonhole the fine color and all parent colors in one step. -/
theorem common_colors {m J q : ℕ} (hq : 0 < q) (k : Fin J → ℕ)
    (f : (j : Fin J) → Fin m → Fin (k j))
    (fine : Fin m → Fin q) (color : (j : Fin J) → Fin (k j) → Fin q) :
    ∃ U : Finset (Fin m), (m : ℝ) ≤ (q : ℝ) ^ (J + 1) * U.card ∧
      (∀ s ∈ U, ∀ t ∈ U, fine s = fine t) ∧
      (∀ j, ∀ s ∈ U, ∀ t ∈ U, color j (f j s) = color j (f j t)) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let c : Fin m → Fin q × (Fin J → Fin q) := fun s => (fine s, fun j => color j (f j s))
  obtain ⟨a, ha⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.heavy_fibre c (fun _ => 1)
  let U := Finset.univ.filter (fun s => c s = a)
  have hsame : ∀ s ∈ U, ∀ t ∈ U, c s = c t := by
    intro s hs t ht
    exact (Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp ht).2.symm
  refine ⟨U, ?_, ?_, ?_⟩
  · have hh : (m : ℝ) ≤ (q : ℝ) ^ (J + 1) *
        ((Finset.univ.filter (fun s => c s = a)).card : ℝ) := by
      convert ha using 1 <;> simp [Fintype.card_prod, pow_succ, mul_comm]
      left
      congr 1
      ext s
      simp
    convert hh using 1
  · intro s hs t ht
    exact congrArg Prod.fst (hsame s hs t ht)
  · intro j s hs t ht
    exact congrFun (congrArg Prod.snd (hsame s hs t ht)) j

/-- Apply the accepted nested regularization lemma to a `Fin`-indexed hierarchy. -/
theorem regularize_layers {m J q : ℕ} (hJ : 0 < J) (hq : 0 < q)
    (k : Fin J → ℕ) (f : (j : Fin J) → Fin m → Fin (k j))
    (hnest : ∀ j j', j ≤ j' → ∀ s t, f j' s = f j' t → f j s = f j t)
    (R : ℝ) (color : ℕ → Fin q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ m → 0 < b → b ≤ m →
      color a = color b → (a : ℝ) ≤ R * b)
    (U : Finset (Fin m)) :
    ∃ S : Finset (Fin m), S ⊆ U ∧ (U.card : ℝ) ≤ (q : ℝ) ^ J * S.card ∧
      ∀ j : Fin J, Balanced S (f j) R := by
  classical
  let idx : ℕ → Fin J := fun j => ⟨min j (J - 1), by omega⟩
  let p : (j : ℕ) → Fin m → Fin (k (idx j)) := fun j => f (idx j)
  have hn : ∀ j l, j ≤ l → l < J → ∀ s t, p l s = p l t → p j s = p j t := by
    intro j l hjl _ s t hst
    exact hnest (idx j) (idx l) (by exact min_le_min_right (J - 1) hjl) s t hst
  obtain ⟨S, hSU, hmass, hbal⟩ :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.regularize_nested p J q m hq R color hcolor hn U
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ U) (fun _ => 1)
  refine ⟨S, hSU, ?_, ?_⟩
  · have he : (U.card : ENNReal) ≤ (q : ENNReal) ^ J * S.card := by simpa using hmass
    have h := ENNReal.toReal_mono (by finiteness) he
    simpa using h
  · intro j
    have he : idx j.val = j := by
      apply Fin.ext
      exact min_eq_left (by omega)
    have hb := hbal j.val j.isLt
    change WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced S (f (idx j.val)) R at hb
    rw [he] at hb
    exact hb

/-- Balance recovers a lower bound at each occupied fiber using just total retention. -/
theorem balanced_fullness {m k : ℕ} {δ r c t R : ℝ}
    (hk : 0 < k) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (f : Fin m → Fin k) (S : Finset (Fin m))
    (hfull : ∀ i, c * r ^ 2 ≤ (ncard {s | f s = i} : ℝ) * δ ^ 2)
    (hretain : t * m ≤ (S.card : ℝ)) (hbal : Balanced S f R)
    (s : Fin m) (hs : s ∈ S) :
    t * c * r ^ 2 ≤ R * ((S.filter (fun a => f a = f s)).card : ℝ) * δ ^ 2 := by
  classical
  have hsum (U : Finset (Fin m)) :
      (∑ i : Fin k, ((U.filter (fun a => f a = i)).card : ℝ)) = (U.card : ℝ) := by
    exact_mod_cast (by simpa using
      Finset.sum_card_fiberwise_eq_card_filter U (Finset.univ : Finset (Fin k)) f :
      (∑ i : Fin k, (U.filter (fun a => f a = i)).card) = U.card)
  have hraw : (k : ℝ) * (c * r ^ 2) ≤ (m : ℝ) * δ ^ 2 := by
    calc
      _ = ∑ _i : Fin k, c * r ^ 2 := by simp
      _ ≤ ∑ i : Fin k, (ncard {a | f a = i} : ℝ) * δ ^ 2 :=
        Finset.sum_le_sum fun i _ => hfull i
      _ = (m : ℝ) * δ ^ 2 := by
        simp_rw [WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
        rw [← Finset.sum_mul, hsum]
        simp
  have hupper : (S.card : ℝ) ≤
      (k : ℝ) * (R * ((S.filter (fun a => f a = f s)).card : ℝ)) := by
    rw [← hsum S]
    calc
      _ ≤ ∑ _i : Fin k, R * ((S.filter (fun a => f a = f s)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : (S.filter (fun a => f a = i)).Nonempty
        · obtain ⟨a, ha⟩ := h
          obtain ⟨haS, hai⟩ := Finset.mem_filter.mp ha
          have hb := hbal a haS s hs
          dsimp only [WangZahlLot.Obl.wz_tower_balanced_refinement.leafFiber] at hb
          rw [hai] at hb
          convert hb using 1 <;> congr 2 <;>
            (try apply congrArg Finset.card) <;> ext a <;> simp
        · rw [Finset.not_nonempty_iff_eq_empty.mp h]
          simp only [Finset.card_empty, Nat.cast_zero]
          positivity
      _ = _ := by simp
  have hδ2 := sq_nonneg δ
  have h1 := mul_le_mul_of_nonneg_left hraw ht
  have h2 := mul_le_mul_of_nonneg_right hretain hδ2
  have h3 := mul_le_mul_of_nonneg_right hupper hδ2
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < k by exact_mod_cast hk)).mp
  nlinarith only [h1, h2, h3]

end WangZahlLot.Obl.wz_nsp_separated_full_subtree
