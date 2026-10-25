-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.EndpointSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CommonNeighbors

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Removing right vertices with less than half the average degree preserves
half of the incidence density. -/
theorem dense_relation_high_right {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) {d : ℝ} (hd : 0 ≤ d)
    (hdensity : d * (Fintype.card I : ℝ) * Fintype.card J ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ)) :
    d / 2 * (Fintype.card I : ℝ) * Fintype.card J ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2 ∧
        d / 2 * (Fintype.card I : ℝ) ≤
          ((Finset.univ.filter (fun i : I => R i p.2)).card : ℝ))).card : ℝ) := by
  classical
  let n (j : J) : ℝ := (Finset.univ.filter (fun i : I => R i j)).card
  let R' (i : I) (j : J) := R i j ∧ d / 2 * (Fintype.card I : ℝ) ≤ n j
  have hn (j : J) : n j ≤
      ((Finset.univ.filter (fun i : I => R' i j)).card : ℝ) +
        d / 2 * (Fintype.card I : ℝ) := by
    by_cases hj : d / 2 * (Fintype.card I : ℝ) ≤ n j
    · simp only [R', hj, and_true]
      change n j ≤ n j + _
      have : 0 ≤ d / 2 * (Fintype.card I : ℝ) := by positivity
      linarith
    · simp only [R', hj, and_false, Finset.filter_false, Finset.card_empty,
        Nat.cast_zero, zero_add]
      exact (lt_of_not_ge hj).le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hn j)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hsum := WangZahlLot.Obl.wz_nonconcentrated_dot_products.sum_relation_degree R
  have hsum' := WangZahlLot.Obl.wz_nonconcentrated_dot_products.sum_relation_degree R'
  change (∑ j, n j) = _ at hsum
  rw [hsum] at hs
  dsimp [R', n] at hs
  have hsum_eq : (∑ x : J, ((Finset.univ.filter (fun i : I =>
      R i x ∧ d / 2 * (Fintype.card I : ℝ) ≤ n x)).card : ℝ)) =
      ((Finset.univ.filter (fun p : I × J => R' p.1 p.2)).card : ℝ) := by
    simpa only [R', n] using hsum'
  rw [hsum_eq] at hs
  change d / 2 * (Fintype.card I : ℝ) * Fintype.card J ≤
    ((Finset.univ.filter (fun p : I × J => R' p.1 p.2)).card : ℝ)
  dsimp [R', n]
  nlinarith

/-- A dense relation has a large common neighborhood at a pair outside any
prescribed sparse relation. No symmetry of the excluded relation is needed. -/
theorem dense_relation_avoiding_pair {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (R : I → J → Prop) (Bad : I → I → Prop) {d : ℝ} (hd : 0 < d)
    (hdensity : d * (Fintype.card I : ℝ) * Fintype.card J ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ))
    (hbad : ∀ i, ((Finset.univ.filter (Bad i)).card : ℝ) ≤
      d ^ 2 / 4 * Fintype.card I) :
    ∃ i i', ¬ Bad i i' ∧ d ^ 2 / 2 * (Fintype.card J : ℝ) ≤
      ((Finset.univ.filter (fun j : J => R i j ∧ R i' j)).card : ℝ) := by
  classical
  let N : ℝ := Fintype.card I
  let M : ℝ := Fintype.card J
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  let c (i i' : I) : ℝ := (Finset.univ.filter (fun j : J => R i j ∧ R i' j)).card
  have hc (i i' : I) : c i i' ≤ M := by
    dsimp [c, M]
    exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun j : J => R i j ∧ R i' j))
  have hlow := WangZahlLot.Obl.wz_nonconcentrated_dot_products.dense_relation_common_neighbors
    R hd.le hdensity
  by_contra hn
  push Not at hn
  have hrow (i : I) : (∑ i', c i i') ≤ 3 * d ^ 2 / 4 * N * M := by
    have hp (i' : I) : c i i' ≤
        (if Bad i i' then M else 0) + d ^ 2 / 2 * M := by
      by_cases hb : Bad i i'
      · rw [ite_eq_left hb]
        exact (hc i i').trans (le_add_of_nonneg_right (by positivity))
      · rw [ite_eq_right hb, zero_add]
        exact (hn i i' hb).le
    calc
      (∑ i', c i i') ≤ ∑ i', ((if Bad i i' then M else 0) + d ^ 2 / 2 * M) :=
        Finset.sum_le_sum fun i' _ => hp i'
      _ = ((Finset.univ.filter (Bad i)).card : ℝ) * M + N * (d ^ 2 / 2 * M) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [N]
      _ ≤ (d ^ 2 / 4 * N) * M + N * (d ^ 2 / 2 * M) :=
        add_le_add (mul_le_mul_of_nonneg_right (hbad i) hM.le) le_rfl
      _ = _ := by ring
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  change d ^ 2 * N ^ 2 * M ≤ ∑ i, ∑ i', c i i' at hlow
  change (∑ i, ∑ i', c i i') ≤ N * (3 * d ^ 2 / 4 * N * M) at hu
  have hp : 0 < d ^ 2 * N ^ 2 * M := by positivity
  nlinarith

/-- Two separated columns retain a dense common line family. A positive
fraction of the remaining columns meets a positive fraction of that family.
The exclusion relation permits deleting neighborhoods of both endpoints. -/
theorem dense_endpoint_family {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (R : I → J → Prop) (Bad : I → I → Prop) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hdensity : d * (Fintype.card I : ℝ) * Fintype.card J ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ))
    (hbad : ∀ i, ((Finset.univ.filter (Bad i)).card : ℝ) ≤
      d ^ 2 / 16 * Fintype.card I) :
    ∃ i₀ i₁, ∃ G : Finset J, ∃ S : Finset I,
      ¬ Bad i₀ i₁ ∧
      (∀ j ∈ G, R i₀ j ∧ R i₁ j) ∧
      d ^ 2 / 8 * (Fintype.card J : ℝ) ≤ G.card ∧
      d / 4 * (Fintype.card I : ℝ) ≤ S.card ∧
      (∀ i ∈ S, ¬ Bad i₀ i ∧ ¬ Bad i₁ i ∧
        d / 8 * (G.card : ℝ) ≤ ((G.filter (R i)).card : ℝ)) := by
  classical
  let N : ℝ := Fintype.card I
  let M : ℝ := Fintype.card J
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  let R' (i : I) (j : J) := R i j ∧ d / 2 * N ≤
    ((Finset.univ.filter (fun i : I => R i j)).card : ℝ)
  have hdense' : d / 2 * N * M ≤
      ((Finset.univ.filter (fun p : I × J => R' p.1 p.2)).card : ℝ) :=
    dense_relation_high_right R hd.le hdensity
  have hbad' (i : I) : ((Finset.univ.filter (Bad i)).card : ℝ) ≤
      (d / 2) ^ 2 / 4 * N := by
    simpa only [show (d / 2) ^ 2 / 4 = d ^ 2 / 16 by ring, N] using hbad i
  obtain ⟨i₀, i₁, hi, hG⟩ := dense_relation_avoiding_pair R' Bad
    (by positivity : 0 < d / 2) (by simpa only [N, M, R'] using hdense') hbad'
  let G := Finset.univ.filter (fun j : J => R' i₀ j ∧ R' i₁ j)
  have hGc : d ^ 2 / 8 * M ≤ (G.card : ℝ) := by
    simpa only [show (d / 2) ^ 2 / 2 = d ^ 2 / 8 by ring, M, G, R', N] using hG
  have hGp : 0 < (G.card : ℝ) := lt_of_lt_of_le (by positivity) hGc
  let S := Finset.univ.filter (fun i : I => ¬ Bad i₀ i ∧ ¬ Bad i₁ i ∧
    d / 8 * (G.card : ℝ) ≤ ((G.filter (R i)).card : ℝ))
  have hdeg (j : J) (hj : j ∈ G) : d / 2 * N ≤
      ((Finset.univ.filter (fun i : I => R i j)).card : ℝ) :=
    (Finset.mem_filter.mp hj).2.1.2
  have hlower : d / 2 * N * (G.card : ℝ) ≤
      ∑ i : I, ((G.filter (R i)).card : ℝ) := by
    have hh := Finset.sum_le_sum (s := G) (fun j hj => hdeg j hj)
    have hid : (∑ j ∈ G, ((Finset.univ.filter (fun i : I => R i j)).card : ℝ)) =
        ∑ i : I, ((G.filter (R i)).card : ℝ) := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Finset.sum_comm]
    rw [hid] at hh
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm (G.card : ℝ)] using hh
  have hupper (i : I) : ((G.filter (R i)).card : ℝ) ≤
      (if Bad i₀ i then (G.card : ℝ) else 0) +
      (if Bad i₁ i then (G.card : ℝ) else 0) +
      (if i ∈ S then (G.card : ℝ) else 0) + d / 8 * (G.card : ℝ) := by
    have hb : ((G.filter (R i)).card : ℝ) ≤ (G.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le G (R i)
    by_cases h₀ : Bad i₀ i
    · rw [ite_eq_left h₀]
      have h₁ : 0 ≤ (if Bad i₁ i then (G.card : ℝ) else 0) := by split_ifs <;> positivity
      have h₂ : 0 ≤ (if i ∈ S then (G.card : ℝ) else 0) := by split_ifs <;> positivity
      have h₃ : 0 ≤ d / 8 * (G.card : ℝ) := by positivity
      linarith
    by_cases h₁ : Bad i₁ i
    · rw [ite_eq_right h₀, ite_eq_left h₁]
      have h₂ : 0 ≤ (if i ∈ S then (G.card : ℝ) else 0) := by split_ifs <;> positivity
      have h₃ : 0 ≤ d / 8 * (G.card : ℝ) := by positivity
      linarith
    by_cases hiS : i ∈ S
    · rw [ite_eq_right h₀, ite_eq_right h₁, ite_eq_left hiS]
      have h₃ : 0 ≤ d / 8 * (G.card : ℝ) := by positivity
      linarith
    · rw [ite_eq_right h₀, ite_eq_right h₁, ite_eq_right hiS]
      have hh : ¬ d / 8 * (G.card : ℝ) ≤ ((G.filter (R i)).card : ℝ) := by
        intro hh
        exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₀, h₁, hh⟩)
      simpa only [zero_add] using (lt_of_not_ge hh).le
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hupper i)
  simp only [Finset.sum_add_distrib] at hu
  simp only [← Finset.sum_filter, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter] at hu
  have hb₀ := mul_le_mul_of_nonneg_right (hbad i₀) hGp.le
  have hb₁ := mul_le_mul_of_nonneg_right (hbad i₁) hGp.le
  have hdd : d ^ 2 ≤ d := by nlinarith
  have hdd' := mul_le_mul_of_nonneg_right hdd (mul_nonneg hN.le hGp.le)
  have hSc : d / 4 * N ≤ (S.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hGp).mp
    change _ ≤ (G.card : ℝ) * (S.card : ℝ)
    dsimp [N] at hlower ⊢
    nlinarith
  refine ⟨i₀, i₁, G, S, hi, ?_, hGc, hSc, ?_⟩
  · intro j hj
    exact ⟨(Finset.mem_filter.mp hj).2.1.1, (Finset.mem_filter.mp hj).2.2.1⟩
  · intro i hiS
    exact (Finset.mem_filter.mp hiS).2

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
