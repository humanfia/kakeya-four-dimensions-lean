-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.Collision.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_kaufman_projection_count.Basic

/- Adapted from this tree’s o103 branch x0272, commit f2e1c96. -/

namespace WangZahlLot.Obl.wz_kaufman_projection_count

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable def equalPairs {X I : Type*} [Fintype X] (g : X → I) : Finset (X × X) :=
  Finset.univ.filter (fun p => g p.1 = g p.2)

/-- Cauchy--Schwarz in the form that counts pairs in the same fiber. -/
theorem card_sq_le_card_mul_equalPairs {X I : Type*} [Fintype X] [Fintype I]
    (g : X → I) :
    (Fintype.card X : ℝ) ^ 2 ≤ (Fintype.card I : ℝ) * ((equalPairs g).card : ℝ) := by
  classical
  let A (i : I) := Finset.univ.filter (fun x : X => g x = i)
  have hN : ∑ i, (A i).card = Fintype.card X := by
    simpa only [A, Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := g) (fun _ _ => Finset.mem_univ _)).symm
  have hP : (equalPairs g).card = ∑ i, (A i).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (s := equalPairs g) (t := Finset.univ)
      (f := fun p => g p.1) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro i hi
    have hfilter : (equalPairs g).filter (fun p => g p.1 = i) = A i ×ˢ A i := by
      ext p
      simp only [equalPairs, A, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product]
      constructor
      · rintro ⟨h, hi⟩
        exact ⟨hi, h.symm.trans hi⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁.trans h₂.symm, h₁⟩
    rw [hfilter, Finset.card_product, pow_two]
  have hN' : ∑ i, ((A i).card : ℝ) = (Fintype.card X : ℝ) := by exact_mod_cast hN
  have hP' : ((equalPairs g).card : ℝ) = ∑ i, ((A i).card : ℝ) ^ 2 := by exact_mod_cast hP
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ((A i).card : ℝ))
  simpa only [Finset.card_univ, hN', ← hP'] using h

noncomputable def closePairs {X Y : Type*} [Fintype X] [PseudoMetricSpace Y]
    (f : X → Y) (r : ℝ) : Finset (X × X) :=
  Finset.univ.filter (fun p => dist (f p.1) (f p.2) ≤ r)

/-- Covering the image by m radius-r balls forces at least card(X)^2/m
pairs of source points whose images are within distance 2r. -/
theorem card_sq_le_cover_mul_closePairs {X Y : Type*} [Fintype X] [PseudoMetricSpace Y]
    (f : X → Y) (r : ℝ) {m : ℕ} {c : Fin m → Y}
    (hcover : Covers r (Set.range f) c) :
    (Fintype.card X : ℝ) ^ 2 ≤ (m : ℝ) * ((closePairs f (2 * r)).card : ℝ) := by
  classical
  have hchoice : ∀ x : X, ∃ i : Fin m, dist (f x) (c i) ≤ r := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self x))
    exact ⟨i, hi⟩
  choose g hg using hchoice
  have hsub : equalPairs g ⊆ closePairs f (2 * r) := by
    intro p hp
    have heq : g p.1 = g p.2 := by
      simpa only [equalPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    calc dist (f p.1) (f p.2) ≤ dist (f p.1) (c (g p.1)) + dist (f p.2) (c (g p.1)) := by
          simpa only [dist_comm (c (g p.1)) (f p.2)] using dist_triangle (f p.1) (c (g p.1)) (f p.2)
      _ ≤ r + r := add_le_add (hg p.1) (by rw [heq]; exact hg p.2)
      _ = 2 * r := by ring
  have hcard : ((equalPairs g).card : ℝ) ≤ ((closePairs f (2 * r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc (Fintype.card X : ℝ) ^ 2 ≤ (Fintype.card (Fin m) : ℝ) * ((equalPairs g).card : ℝ) :=
      card_sq_le_card_mul_equalPairs g
    _ ≤ (m : ℝ) * ((closePairs f (2 * r)).card : ℝ) := by simpa using mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m)

end WangZahlLot.Obl.wz_kaufman_projection_count
