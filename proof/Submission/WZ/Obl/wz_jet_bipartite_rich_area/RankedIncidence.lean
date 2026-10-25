-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.RankedIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.TwoClassRank
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.UnbalancedFourCycle

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

/-- The finite incidence estimate with a rank descent and an explicit
short-contact budget. The crowding factor enters through its square root. -/
theorem incidence_le_of_ranked_cycles {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop)
    (rA : (Fin 2 ↪ α) → ℕ) (rB : (Fin 2 ↪ β) → ℕ) (h : ℕ)
    (hrA : ∀ e, rA e ≤ h) (hrB : ∀ e, rB e ≤ h)
    (colorA : (Fin 2 ↪ α) → β → Bool) (colorB : (Fin 2 ↪ β) → α → Bool)
    (Bad : (Fin 2 ↪ α) → (Fin 2 ↪ β) → Prop)
    (hgoodA : ∀ e f, (∀ s t, R (e s) (f t)) →
      colorA e (f 0)=colorA e (f 1) → ¬Bad e f → rB f<rA e)
    (hgoodB : ∀ e f, (∀ s t, R (e s) (f t)) →
      colorB f (e 0)=colorB f (e 1) → ¬Bad e f → rA e<rB f)
    {H G dA dB : ℝ} (hH : 1 ≤ H) (hG : 1 ≤ G)
    (hbad : (∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
        if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0) ≤
      H*(∑ a, (Fintype.card {b // R a b}:ℝ))*(dA+dB))
    (hdegA : (Fintype.card α:ℝ)*dA ≤ G*(∑ a, (Fintype.card {b // R a b}:ℝ)))
    (hdegB : (Fintype.card β:ℝ)*dB ≤ G*(∑ a, (Fintype.card {b // R a b}:ℝ))) :
    (∑ a, (Fintype.card {b // R a b}:ℝ)) ≤
      8*((4:ℝ)^(h+1)+1)*G*Real.sqrt H*
        ((Fintype.card α:ℝ)+(Fintype.card β:ℝ))*
        Real.sqrt ((Fintype.card α:ℝ)+(Fintype.card β:ℝ)) := by
  let m : ℝ := Fintype.card α
  let n : ℝ := Fintype.card β
  let N := m+n
  let I : ℝ := ∑ a, (Fintype.card {b // R a b}:ℝ)
  let Q : ℝ := Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
    ∀ s t, R (p.2 s) (p.1 t)}
  let L : ℝ := (4:ℝ)^(h+1)+1
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hN : 0 ≤ N := add_nonneg hm hn
  have hI : 0 ≤ I := by positivity
  have hL : 1 ≤ L := by
    have hp : 0 ≤ (4:ℝ)^(h+1) := by positivity
    dsimp [L]
    linarith
  have hcycles : Q ≤ L*((m+n)^2+(4*H)*I*(dA+dB)) := by
    have hh := four_cycle_count_le_of_two_class_rank R rA rB h hrA hrB
      colorA colorB Bad hgoodA hgoodB
    have hmul := mul_le_mul_of_nonneg_left hbad (show 0 ≤ L*4 by positivity)
    dsimp [Q, L, m, n, I] at *
    nlinarith only [hh, hmul]
  have hfour : I^4 ≤16*m^2*n^2*(m+n)^2+8*m^2*n^2*Q :=
    incidence_fourth_le_unbalanced_cycles R
  have hsquare := incidence_sq_le_of_degree_scaled_cycle_bound hm hn hI
    (show 0 ≤ L by linarith) (show 0 ≤ 4*H by linarith) (show 0 ≤ G by linarith)
    hfour hcycles hdegA hdegB
  have hLGH : 1 ≤ L*G*H := by
    calc
      1 = 1*1*1 := by norm_num
      _ ≤ L*G*H := mul_le_mul (mul_le_mul hL hG (by norm_num) (by linarith)) hH
        (by norm_num) (by positivity)
  have hL_LGH : L ≤ L*G*H := by
    have hGH : 1 ≤ G*H := by nlinarith [mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hH)]
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hGH)]
  have hcoef : 17+8*L+8*L*(4*H)*G ≤64*L*G*H := by
    nlinarith only [hLGH, hL_LGH]
  have hmn : m*n ≤ N^2 := by dsimp [N]; nlinarith only [sq_nonneg m, sq_nonneg n, mul_nonneg hm hn]
  have hsquare' : I^2 ≤64*L*G*H*N^3 := by
    calc
      _ ≤ (17+8*L+8*L*(4*H)*G)*(m*n*(m+n)) := hsquare
      _ ≤ (64*L*G*H)*(N^2*N) := by
        apply mul_le_mul hcoef _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmn hN
      _ = _ := by ring
  have hLsq : L ≤ L^2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hL)]
  have hGsq : G ≤ G^2 := by nlinarith [mul_nonneg (show 0 ≤ G by linarith) (sub_nonneg.mpr hG)]
  have hbig : I^2 ≤(8*L*G*Real.sqrt H*N*Real.sqrt N)^2 := by
    calc
      _ ≤ 64*L*G*H*N^3 := hsquare'
      _ ≤64*L^2*G^2*H*N^3 := by gcongr
      _ = _ := by
        simp only [mul_pow, Real.sq_sqrt (show 0 ≤ H by linarith), Real.sq_sqrt hN]
        ring
  change I ≤8*L*G*Real.sqrt H*N*Real.sqrt N
  exact le_of_sq_le_sq hbig (by positivity)

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
