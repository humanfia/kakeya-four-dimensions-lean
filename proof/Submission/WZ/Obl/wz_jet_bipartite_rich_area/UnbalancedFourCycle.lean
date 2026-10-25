-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.UnbalancedFourCycle.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FourCycleCount

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

private theorem fourth_bound_unbalanced {m n I S Q : ℝ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hI : 0 ≤ I) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hfirst : I^2 ≤ m*(S+I)) (hsecond : S^2 ≤ n^2*(Q+S)) :
    I^4 ≤ 16*m^2*n^2*(m+n)^2+8*m^2*n^2*Q := by
  have hm0 : 0 ≤ m := by linarith
  have hn0 : 0 ≤ n := by linarith
  by_cases hsmall : I^2 ≤ 4*m*n*(m+n)
  · have hh := pow_le_pow_left₀ (sq_nonneg I) hsmall 2
    have hpos : 0 ≤ 8*m^2*n^2*Q := by positivity
    nlinarith only [hh, hpos]
  · have hlarge : 4*m*n*(m+n) < I^2 := lt_of_not_ge hsmall
    have hmn : m ≤ m*n := by nlinarith only [mul_nonneg hm0 (sub_nonneg.mpr hn)]
    have hmN : m ≤ m+n := by linarith
    have hmm : m^2 ≤ m*n*(m+n) := by
      calc
        m^2 = m*m := by ring
        _ ≤ (m*n)*(m+n) := mul_le_mul hmn hmN hm0 (by positivity)
    have hIm : 2*m ≤ I := by nlinarith only [hlarge, hmm, hI, hm0]
    have hIS : I^2 ≤ 2*m*S := by
      nlinarith only [hfirst, mul_nonneg hI (sub_nonneg.mpr hIm)]
    have hSm : 2*n^2 ≤ S := by
      have hN : 4*m*n^2 ≤ 4*m*n*(m+n) := by
        have := mul_nonneg (show 0 ≤ 4*m*n by positivity) hm0
        nlinarith only [this]
      by_contra h
      have hh : S<2*n^2 := lt_of_not_ge h
      have hmul := mul_le_mul_of_nonneg_left hh.le (show 0 ≤ 2*m by positivity)
      nlinarith only [hlarge, hN, hIS, hmul]
    have hSQ : S^2 ≤ 2*n^2*Q := by
      nlinarith only [hsecond, mul_nonneg hS (sub_nonneg.mpr hSm)]
    calc
      I^4 = (I^2)^2 := by ring
      _ ≤ (2*m*S)^2 := pow_le_pow_left₀ (sq_nonneg I) hIS 2
      _ = 4*m^2*S^2 := by ring
      _ ≤ 4*m^2*(2*n^2*Q) := mul_le_mul_of_nonneg_left hSQ (by positivity)
      _ ≤ 16*m^2*n^2*(m+n)^2+8*m^2*n^2*Q := by
        nlinarith only [show 0 ≤ 16*m^2*n^2*(m+n)^2 by positivity]

/-- Four-cycle supersaturation retaining the two vertex-set sizes separately.
The additive term handles graphs below the natural incidence threshold. -/
theorem incidence_fourth_le_unbalanced_cycles {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop) :
    (∑ a, (Fintype.card {b // R a b}:ℝ))^4 ≤
      16*(Fintype.card α:ℝ)^2*(Fintype.card β:ℝ)^2*
        ((Fintype.card α:ℝ)+(Fintype.card β:ℝ))^2+
      8*(Fintype.card α:ℝ)^2*(Fintype.card β:ℝ)^2*
        (Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
          ∀ s t, R (p.2 s) (p.1 t)} : ℝ) := by
  classical
  let m : ℝ := Fintype.card α
  let n : ℝ := Fintype.card β
  let I : ℝ := ∑ a, (Fintype.card {b // R a b}:ℝ)
  let S : ℝ := ∑ e : Fin 2 ↪ β, (Fintype.card {a // ∀ t, R a (e t)}:ℝ)
  let Q : ℝ := ∑ e : Fin 2 ↪ β,
    ((Fintype.card {a // ∀ t, R a (e t)}).descFactorial 2:ℝ)
  have hI : 0 ≤ I := by positivity
  have hS : 0 ≤ S := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hsum : (∑ a, (Fintype.card {b // R a b}:ℝ)^2)=S+I := by
    simp_rw [square_eq_desc_two_add]
    rw [Finset.sum_add_distrib]
    congr 1
    dsimp [S]
    exact_mod_cast (sum_common_neighbors_eq_sum_degree_pairs R).symm
  have hfirst : I^2 ≤ m*(S+I) := by
    rw [← hsum]
    simpa only [I, m, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun a : α => (Fintype.card {b // R a b}:ℝ)))
  have hpairs : (Fintype.card (Fin 2 ↪ β):ℝ) ≤ n^2 := by
    simp only [Fintype.card_embedding_eq, Fintype.card_fin, n]
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card β) 2
  have hsecond : S^2 ≤ n^2*(Q+S) := by
    calc
      _ ≤ (Fintype.card (Fin 2 ↪ β):ℝ)*
          ∑ e : Fin 2 ↪ β, (Fintype.card {a // ∀ t, R a (e t)}:ℝ)^2 := by
        simpa only [S, Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun e : Fin 2 ↪ β => (Fintype.card {a // ∀ t, R a (e t)}:ℝ)))
      _ = (Fintype.card (Fin 2 ↪ β):ℝ)*(Q+S) := by
        simp only [square_eq_desc_two_add, Finset.sum_add_distrib, Q, S]
      _ ≤ n^2*(Q+S) := mul_le_mul_of_nonneg_right hpairs (add_nonneg hQ hS)
  rw [card_ordered_four_cycles_eq, Nat.cast_sum]
  change I^4 ≤ 16*m^2*n^2*(m+n)^2+8*m^2*n^2*Q
  by_cases hmz : Fintype.card α=0
  · have hm : m=0 := by simp [m, hmz]
    rw [hm] at hfirst ⊢
    have hIz : I=0 := by nlinarith only [hfirst, hI]
    simp [hIz]
  by_cases hnz : Fintype.card β=0
  · have hn : n=0 := by simp [n, hnz]
    have hIz : I=0 := by
      have : IsEmpty β := Fintype.card_eq_zero_iff.mp hnz
      simp [I]
    simp [hIz, hn]
  exact fourth_bound_unbalanced (by dsimp [m]; exact_mod_cast (by omega : 1 ≤ Fintype.card α))
    (by dsimp [n]; exact_mod_cast (by omega : 1 ≤ Fintype.card β)) hI hS hQ hfirst hsecond

private theorem quadratic_bound {X B U V : ℝ}
    (_hX : 0 ≤ X) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hh : X^2 ≤ U*B^2+V*X*B) : X ≤ (U+V+1)*B := by
  by_contra h
  have hlt : (U+V+1)*B<X := lt_of_not_ge h
  have hXB : B ≤ X := by nlinarith only [hlt, mul_nonneg hU hB, mul_nonneg hV hB]
  have hXpos : 0<X := by nlinarith only [hlt, hB, mul_nonneg hU hB, mul_nonneg hV hB]
  have hUB : U*B^2 ≤ U*X*B := by
    have hh := mul_le_mul_of_nonneg_left hXB (mul_nonneg hU hB)
    nlinarith only [hh]
  have hstrict : (U+V)*B<X := by linarith
  have hprod := mul_lt_mul_of_pos_right hstrict hXpos
  nlinarith only [hh, hUB, hprod]

/-- If exceptional four-cycles are bounded by short wedges times the
maximum degree, the incidence estimate loses only the square root of
the local crowding factor. This statement records the squared bound. -/
theorem incidence_sq_le_of_degree_scaled_cycle_bound
    {m n I Q L H G dA dB : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hI : 0 ≤ I)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hfour : I^4 ≤ 16*m^2*n^2*(m+n)^2+8*m^2*n^2*Q)
    (hcycles : Q ≤ L*((m+n)^2+H*I*(dA+dB)))
    (hdegA : m*dA ≤ G*I) (hdegB : n*dB ≤ G*I) :
    I^2 ≤ (17+8*L+8*L*H*G)*(m*n*(m+n)) := by
  let B := m*n*(m+n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm : m^2*n^2*I*(dA+dB) ≤ G*I^2*B := by
    have ha := mul_le_mul_of_nonneg_left hdegA (show 0 ≤ m*n^2*I by positivity)
    have hb := mul_le_mul_of_nonneg_left hdegB (show 0 ≤ m^2*n*I by positivity)
    dsimp [B]
    nlinarith only [ha, hb]
  have hcycle_mul := mul_le_mul_of_nonneg_left hcycles
    (show 0 ≤ 8*m^2*n^2 by positivity)
  have hterm_mul := mul_le_mul_of_nonneg_left hterm
    (show 0 ≤ 8*L*H by positivity)
  have hquad : (I^2)^2 ≤ (16+8*L)*B^2+(8*L*H*G)*(I^2)*B := by
    dsimp [B] at *
    nlinarith only [hfour, hcycle_mul, hterm_mul]
  have hbound := quadratic_bound (sq_nonneg I) hB
    (show 0 ≤ 16+8*L by positivity) (show 0 ≤ 8*L*H*G by positivity) hquad
  convert hbound using 1; ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
