-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.FourCycleCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

theorem square_eq_desc_two_add (n : ℕ) :
    (n : ℝ) ^ 2 = (n.descFactorial 2 : ℝ) + n := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.succ_sub_succ_eq_sub, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
    ring

private theorem card_neighbor_pairs {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (a : α) :
    Fintype.card {e : Fin 2 ↪ β // ∀ t, R a (e t)} =
      (Fintype.card {b // R a b}).descFactorial 2 := by
  calc
    _ = Fintype.card (Fin 2 ↪ {b // R a b}) := by
      apply Fintype.card_congr
      exact Equiv.codRestrict (Fin 2) {b | R a b}
    _ = _ := by simp only [Fintype.card_embedding_eq, Fintype.card_fin]

/-- Count ordered length-two paths using either their central vertex or their two
distinct endpoints. -/
theorem sum_common_neighbors_eq_sum_degree_pairs {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop) :
    (∑ e : Fin 2 ↪ β, Fintype.card {a // ∀ t, R a (e t)}) =
      ∑ a, (Fintype.card {b // R a b}).descFactorial 2 := by
  have hdouble :
      (∑ a, Fintype.card {e : Fin 2 ↪ β // ∀ t, R a (e t)}) =
      ∑ e : Fin 2 ↪ β, Fintype.card {a // ∀ t, R a (e t)} := by
    simpa only [Fintype.card_subtype, Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun a (e : Fin 2 ↪ β) => ∀ t, R a (e t))
        (s := Finset.univ) (t := Finset.univ))
  rw [← hdouble]
  exact Finset.sum_congr rfl (fun a _ => card_neighbor_pairs R a)

/-- The codegree expression counts ordered four-cycles with two distinct vertices
of each color. This form permits a geometric proof by an injection or bounded fibers. -/
theorem card_ordered_four_cycles_eq {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      ∀ s t, R (p.2 s) (p.1 t)} =
      ∑ e : Fin 2 ↪ β, (Fintype.card {a // ∀ t, R a (e t)}).descFactorial 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (e : Fin 2 ↪ β) (f : Fin 2 ↪ α) => ∀ s t, R (f s) (e t)))]
  simp only [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [← Nat.card_eq_fintype_card] using
    card_neighbor_pairs (fun (e : Fin 2 ↪ β) a => ∀ t, R a (e t)) e

private theorem fourth_bound_from_two_cauchy {N I S Q C : ℝ}
    (hN : 1 ≤ N) (hI : 0 ≤ I) (hS : 0 ≤ S) (_hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hfirst : I ^ 2 ≤ N * (S + I))
    (hsecond : S ^ 2 ≤ N ^ 2 * (Q + S)) (hcycles : Q ≤ C * N ^ 2) :
    I ^ 4 ≤ (16 + 8 * C) * N ^ 6 := by
  have hN0 : 0 ≤ N := by linarith
  by_cases hsmall : I ^ 2 ≤ 4 * N ^ 3
  · calc
      I ^ 4 = (I ^ 2) ^ 2 := by ring
      _ ≤ (4 * N ^ 3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hsmall 2
      _ = 16 * N ^ 6 := by ring
      _ ≤ (16 + 8 * C) * N ^ 6 := by gcongr; linarith
  · have hlarge : 4 * N ^ 3 < I ^ 2 := lt_of_not_ge hsmall
    have hNN : N ^ 2 ≤ N ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hN)]
    have hIN : 2 * N ≤ I := by nlinarith
    have hIS : I ^ 2 ≤ 2 * N * S := by
      nlinarith [mul_nonneg hI (sub_nonneg.mpr hIN)]
    have hSN : 2 * N ^ 2 ≤ S := by
      by_contra h
      have hh : S < 2 * N ^ 2 := lt_of_not_ge h
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hh.le)]
    have hSQ : S ^ 2 ≤ 2 * N ^ 2 * Q := by
      nlinarith [mul_nonneg hS (sub_nonneg.mpr hSN)]
    calc
      I ^ 4 = (I ^ 2) ^ 2 := by ring
      _ ≤ (2 * N * S) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hIS 2
      _ = 4 * N ^ 2 * S ^ 2 := by ring
      _ ≤ 4 * N ^ 2 * (2 * N ^ 2 * Q) := by gcongr
      _ ≤ 4 * N ^ 2 * (2 * N ^ 2 * (C * N ^ 2)) := by gcongr
      _ = 8 * C * N ^ 6 := by ring
      _ ≤ (16 + 8 * C) * N ^ 6 := by gcongr; linarith

/-- A quadratic bound for the total number of ordered nondegenerate four-cycles
implies the `N^(3/2)` incidence bound, stated without roots. The four-cycle count
is a hypothesis; in the lens application its geometric charging argument is separate. -/
theorem incidence_fourth_le_of_four_cycle_bound {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop) {C : ℝ} (hC : 0 ≤ C)
    (hcycles :
      (∑ e : Fin 2 ↪ β,
        ((Fintype.card {a // ∀ t, R a (e t)}).descFactorial 2 : ℝ)) ≤
      C * ((Fintype.card α : ℝ) + Fintype.card β) ^ 2) :
    (∑ a, (Fintype.card {b // R a b} : ℝ)) ^ 4 ≤
      (16 + 8 * C) * ((Fintype.card α : ℝ) + Fintype.card β) ^ 6 := by
  let N : ℝ := Fintype.card α + Fintype.card β
  let I : ℝ := ∑ a, (Fintype.card {b // R a b} : ℝ)
  let S : ℝ := ∑ e : Fin 2 ↪ β, (Fintype.card {a // ∀ t, R a (e t)} : ℝ)
  let Q : ℝ := ∑ e : Fin 2 ↪ β,
    ((Fintype.card {a // ∀ t, R a (e t)}).descFactorial 2 : ℝ)
  have hN0 : 0 ≤ N := by positivity
  have hI0 : 0 ≤ I := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hleft : (Fintype.card α : ℝ) ≤ N := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hright : (Fintype.card β : ℝ) ≤ N := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsum : (∑ a, (Fintype.card {b // R a b} : ℝ) ^ 2) = S + I := by
    simp_rw [square_eq_desc_two_add]
    rw [Finset.sum_add_distrib]
    congr 1
    dsimp [S]
    exact_mod_cast (sum_common_neighbors_eq_sum_degree_pairs R).symm
  have hfirst : I ^ 2 ≤ N * (S + I) := by
    calc
      _ ≤ (Fintype.card α : ℝ) * ∑ a, (Fintype.card {b // R a b} : ℝ) ^ 2 := by
        simpa only [I, Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun a : α => (Fintype.card {b // R a b} : ℝ)))
      _ = (Fintype.card α : ℝ) * (S + I) := by rw [hsum]
      _ ≤ N * (S + I) := mul_le_mul_of_nonneg_right hleft (add_nonneg hS0 hI0)
  have hpairs : (Fintype.card (Fin 2 ↪ β) : ℝ) ≤ N ^ 2 := by
    calc
      _ ≤ (Fintype.card β : ℝ) ^ 2 := by
        simp only [Fintype.card_embedding_eq, Fintype.card_fin]
        exact_mod_cast Nat.descFactorial_le_pow (Fintype.card β) 2
      _ ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hright 2
  have hsecond : S ^ 2 ≤ N ^ 2 * (Q + S) := by
    calc
      _ ≤ (Fintype.card (Fin 2 ↪ β) : ℝ) *
          ∑ e : Fin 2 ↪ β, (Fintype.card {a // ∀ t, R a (e t)} : ℝ) ^ 2 := by
        simpa only [S, Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun e : Fin 2 ↪ β => (Fintype.card {a // ∀ t, R a (e t)} : ℝ)))
      _ = (Fintype.card (Fin 2 ↪ β) : ℝ) * (Q + S) := by
        simp only [square_eq_desc_two_add, Finset.sum_add_distrib, Q, S]
      _ ≤ N ^ 2 * (Q + S) := mul_le_mul_of_nonneg_right hpairs (add_nonneg hQ0 hS0)
  change I ^ 4 ≤ (16 + 8 * C) * N ^ 6
  by_cases hz : Fintype.card α + Fintype.card β = 0
  · have hNz : N = 0 := by dsimp [N]; exact_mod_cast hz
    rw [hNz] at hfirst ⊢
    norm_num at hfirst ⊢
    have hIz : I = 0 := by nlinarith
    simp [hIz]
  · have hN1 : 1 ≤ N := by
      have hh : 1 ≤ Fintype.card α + Fintype.card β := by omega
      dsimp [N]
      exact_mod_cast hh
    exact fourth_bound_from_two_cauchy hN1 hI0 hS0 hQ0 hC hfirst hsecond hcycles

/-- The incidence form of the four-cycle estimate, with a polynomial constant.
No assertion about the number of geometric lens cycles is included. -/
theorem incidence_le_of_card_four_cycles {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop) {C : ℝ} (hC : 0 ≤ C)
    (hcycles :
      (Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
        ∀ s t, R (p.2 s) (p.1 t)} : ℝ) ≤
      C * ((Fintype.card α : ℝ) + Fintype.card β) ^ 2) :
    (∑ a, (Fintype.card {b // R a b} : ℝ)) ≤
      (16 + 8 * C) * ((Fintype.card α : ℝ) + Fintype.card β) *
        Real.sqrt ((Fintype.card α : ℝ) + Fintype.card β) := by
  rw [card_ordered_four_cycles_eq, Nat.cast_sum] at hcycles
  have hfour := incidence_fourth_le_of_four_cycle_bound R hC hcycles
  let N : ℝ := Fintype.card α + Fintype.card β
  let H : ℝ := 16 + 8 * C
  have hN : 0 ≤ N := by positivity
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH4 : H ≤ H ^ 4 := by
    calc
      H = H ^ 1 := by ring
      _ ≤ H ^ 4 := pow_le_pow_right₀ hH (by norm_num)
  have hroot : (Real.sqrt N) ^ 4 = N ^ 2 := by
    calc
      _ = ((Real.sqrt N) ^ 2) ^ 2 := by ring
      _ = N ^ 2 := by rw [Real.sq_sqrt hN]
  change (∑ a, (Fintype.card {b // R a b} : ℝ)) ≤ H * N * Real.sqrt N
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ H * N ^ 6 := hfour
    _ ≤ H ^ 4 * N ^ 6 := mul_le_mul_of_nonneg_right hH4 (by positivity)
    _ = (H * N * Real.sqrt N) ^ 4 := by rw [mul_pow, mul_pow, hroot]; ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
