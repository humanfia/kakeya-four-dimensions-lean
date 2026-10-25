-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/CellRuzsa.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.CellDilate

/-!
# Ruzsa calculus for occupied cells

The covering-number forms of Ruzsa's triangle inequality, of the Plünnecke–Ruzsa inequality and
of Ruzsa's covering lemma used in paper Section 7 (displays `re:ruzsa-triangle`, `re:iterate`,
`re:covering`), for the occupied cells of finite planar sets. They are transferred from Mathlib's
finset versions in `ℤ × ℤ` through the error boxes of `Cells`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

theorem card_cells_sub_comm_le (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    (cells h (V - U)).card ≤ (cells h (U - V)).card * 4 := by
  rw [← neg_sub U V]
  exact card_cells_neg_le h (U - V)

/-- **Ruzsa's triangle inequality** for occupied cells (paper display `re:ruzsa-triangle`). -/
theorem cells_ruzsa (h : ℝ) (U V W : Finset (ℝ × ℝ)) :
    ((cells h (U - W)).card : ℝ) * (cells h V).card ≤
      256 * (cells h (U - V)).card * (cells h (V - W)).card := by
  have h1 := card_cells_sub_le h U W
  have h2 := Finset.ruzsa_triangle_inequality_sub_sub_sub (cells h U) (cells h V) (cells h W)
  have h3 := card_sub_cells_le h U V
  have h4 := card_sub_cells_le h W V
  have h5 := card_cells_sub_comm_le h V W
  have key : (cells h (U - W)).card * (cells h V).card ≤
      256 * (cells h (U - V)).card * (cells h (V - W)).card := by
    calc (cells h (U - W)).card * (cells h V).card
        ≤ ((cells h U - cells h W).card * 4) * (cells h V).card := Nat.mul_le_mul_right _ h1
      _ = 4 * ((cells h U - cells h W).card * (cells h V).card) := by ring
      _ ≤ 4 * ((cells h U - cells h V).card * (cells h W - cells h V).card) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ 4 * (((cells h (U - V)).card * 4) * ((cells h (W - V)).card * 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 h4)
      _ ≤ 4 * (((cells h (U - V)).card * 4) * (((cells h (V - W)).card * 4) * 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h5))
      _ = 256 * (cells h (U - V)).card * (cells h (V - W)).card := by ring
  exact_mod_cast key

/-- The Plünnecke–Ruzsa inequality in `ℤ × ℤ`, in real form. -/
theorem card_nsmul_sub_nsmul_le {Y : Finset (ℤ × ℤ)} (hY : Y.Nonempty) (m n : ℕ) :
    ((m • Y - n • Y).card : ℝ) ≤ (((Y - Y).card : ℝ) / Y.card) ^ (m + n) * Y.card := by
  have hh := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hY Y m n
  have hh' := (NNRat.cast_le (K := ℝ)).mpr hh
  push_cast at hh'
  exact hh'

theorem card_finset_sum_le {ι : Type*} [DecidableEq ι] (F : ι → Finset (ℤ × ℤ)) (s : Finset ι) :
    (∑ i ∈ s, F i).card ≤ ∏ i ∈ s, (F i).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Finset.card_add_le.trans (Nat.mul_le_mul_left _ ih)

theorem ebox_add_subset (n : ℕ) : ebox 0 n + ebox 0 1 ⊆ ebox 0 ((n + 1 : ℕ) : ℤ) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  simp only [ebox, Finset.mem_product, Finset.mem_Icc] at ha hb ⊢
  push_cast
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem cells_zero (h : ℝ) : cells h (0 : Finset (ℝ × ℝ)) = {0} := by
  rw [show (0 : Finset (ℝ × ℝ)) = {0} from rfl]
  simp [cells, cell]

/-- A sum of sets, each of whose cell sets is covered by translates of `Y - Y`, has its cells
covered by the sum of the translation sets plus a multiple of `Y - Y` and an error box. -/
theorem cells_sum_subset {ι : Type*} [DecidableEq ι] (h : ℝ) (Y : Finset (ℤ × ℤ))
    (U : ι → Finset (ℝ × ℝ)) (F : ι → Finset (ℤ × ℤ)) (s : Finset ι)
    (hU : ∀ i ∈ s, cells h (U i) ⊆ F i + (Y - Y)) :
    cells h (∑ i ∈ s, U i) ⊆ (∑ i ∈ s, F i) + s.card • (Y - Y) + ebox 0 s.card := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, cells_zero, Finset.card_empty, zero_nsmul]
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    refine Finset.mem_add.mpr ⟨0, ?_, 0, ?_, by simp⟩
    · simp
    · rw [ebox]; exact Finset.mem_product.mpr ⟨by simp, by simp⟩
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hU i (Finset.mem_insert_of_mem hi))
    have hUa := hU a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    calc cells h (U a + ∑ i ∈ s, U i)
        ⊆ cells h (U a) + cells h (∑ i ∈ s, U i) + ebox 0 1 := cells_add_subset h _ _
      _ ⊆ (F a + (Y - Y)) + ((∑ i ∈ s, F i) + s.card • (Y - Y) + ebox 0 s.card) + ebox 0 1 :=
          Finset.add_subset_add (Finset.add_subset_add hUa ih') le_rfl
      _ = (F a + ∑ i ∈ s, F i) + (s.card + 1) • (Y - Y) + (ebox 0 s.card + ebox 0 1) := by
          rw [succ_nsmul]; generalize Y - Y = D; abel
      _ ⊆ (F a + ∑ i ∈ s, F i) + (s.card + 1) • (Y - Y) + ebox 0 ((s.card + 1 : ℕ) : ℤ) :=
          Finset.add_subset_add le_rfl (ebox_add_subset s.card)

theorem nsmul_sub_finset (Y : Finset (ℤ × ℤ)) (n : ℕ) : n • (Y - Y) = n • Y - n • Y := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, sub_add_sub_comm]

theorem card_ebox_nat (n : ℕ) : ((ebox 0 (n : ℤ)).card : ℝ) = ((n : ℝ) + 1) ^ 2 := by
  rw [card_ebox]
  have : ((n : ℤ) + 1 - 0) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]
  push_cast
  ring

/-- **Covering a sum of sets** (paper display `re:covering` and the cover count in the proof of
Lemma 7.3): if every cell set `cells(U i)` has small sum with `Y`, the cells of `∑ U i` are few. -/
theorem card_cells_sum_le {ι : Type*} [DecidableEq ι] (h : ℝ) {Y : Finset (ℤ × ℤ)}
    (hY : Y.Nonempty) (U : ι → Finset (ℝ × ℝ)) (s : Finset ι) (Λ : ℝ)
    (hU : ∀ i ∈ s, ((cells h (U i) + Y).card : ℝ) ≤ Λ * Y.card) :
    ((cells h (∑ i ∈ s, U i)).card : ℝ) ≤
      Λ ^ s.card * (((Y - Y).card : ℝ) / Y.card) ^ (2 * s.card) * Y.card *
        ((s.card : ℝ) + 1) ^ 2 := by
  classical
  have hcov : ∀ i, ∃ F : Finset (ℤ × ℤ), i ∈ s →
      ((F.card : ℝ) ≤ Λ ∧ cells h (U i) ⊆ F + (Y - Y)) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨F, -, hFc, hFs⟩ := Finset.ruzsa_covering_add hY (hU i hi)
      exact ⟨F, fun _ => ⟨hFc, hFs⟩⟩
    · exact ⟨∅, fun h' => absurd h' hi⟩
  choose F hF using hcov
  have hsub := cells_sum_subset h Y U F s (fun i hi => (hF i hi).2)
  have hΛ : ∀ i ∈ s, 0 ≤ Λ := fun i hi => le_trans (by positivity) (hF i hi).1
  have hcard1 : ((∑ i ∈ s, F i).card : ℝ) ≤ Λ ^ s.card := by
    calc ((∑ i ∈ s, F i).card : ℝ) ≤ ∏ i ∈ s, ((F i).card : ℝ) := by
          exact_mod_cast card_finset_sum_le F s
      _ ≤ ∏ _i ∈ s, Λ := Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => (hF i hi).1)
      _ = Λ ^ s.card := Finset.prod_const Λ
  have hcard2 : ((s.card • (Y - Y)).card : ℝ) ≤
      (((Y - Y).card : ℝ) / Y.card) ^ (2 * s.card) * Y.card := by
    rw [nsmul_sub_finset, two_mul]
    exact card_nsmul_sub_nsmul_le hY _ _
  calc ((cells h (∑ i ∈ s, U i)).card : ℝ)
      ≤ ((∑ i ∈ s, F i) + s.card • (Y - Y) + ebox 0 s.card).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ i ∈ s, F i).card : ℝ) * (s.card • (Y - Y)).card * (ebox 0 s.card).card := by
        have := (Finset.card_add_le (s := (∑ i ∈ s, F i) + s.card • (Y - Y))
          (t := ebox 0 (s.card : ℤ))).trans (Nat.mul_le_mul_right _ Finset.card_add_le)
        exact_mod_cast this
    _ ≤ Λ ^ s.card * ((((Y - Y).card : ℝ) / Y.card) ^ (2 * s.card) * Y.card) *
          ((s.card : ℝ) + 1) ^ 2 := by
        have hΛpow : 0 ≤ Λ ^ s.card := by
          rcases s.eq_empty_or_nonempty with hs | ⟨i, hi⟩
          · simp [hs]
          · exact pow_nonneg (hΛ i hi) _
        rw [card_ebox_nat]
        gcongr
    _ = Λ ^ s.card * (((Y - Y).card : ℝ) / Y.card) ^ (2 * s.card) * Y.card *
          ((s.card : ℝ) + 1) ^ 2 := by ring

end

end Submission.Obl.k4_retained_edge_planar_rigidity
