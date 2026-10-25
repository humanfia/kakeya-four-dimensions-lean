-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.CriticalEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.Counting
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open Metric

/-- A finite geometric decomposition bounds the critical inverse-distance
energy, losing an arbitrarily small power in place of a logarithm. -/
theorem sum_inv_le_of_linear_count {ι : Type*} [Fintype ι]
    (d : ι → ℝ) {δ A : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hd : ∀ i, δ ≤ d i) (_hA : 0 ≤ A)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => d i ≤ r)).card : ℝ) ≤ A*r) (K : ℕ) :
    ∑ i, (d i)⁻¹ ≤ (Fintype.card ι : ℝ) +
      ((K : ℝ)+1)*A*δ^(-1/((K : ℝ)+1)) := by
  classical
  let L : ℝ := (K : ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let t : ℕ → ℝ := fun j => δ^(-((j : ℝ)/L))
  let r : ℕ → ℝ := fun j => δ^((j : ℝ)/L)
  let W : ℕ → ι → ℝ := fun j i => if d i ≤ r j then t (j+1) else 0
  have ht : ∀ j, 0 < t j := fun _ => Real.rpow_pos_of_pos hδ _
  have hr : ∀ j, 0 < r j := fun _ => Real.rpow_pos_of_pos hδ _
  have hW : ∀ j i, 0 ≤ W j i := by intro j i; dsimp [W]; split_ifs <;> positivity
  have hpoint : ∀ i, (d i)⁻¹ ≤ 1 + ∑ j ∈ Finset.range (K+1), W j i := by
    intro i
    have hdpos : 0 < d i := hδ.trans_le (hd i)
    by_cases hsmall : (d i)⁻¹ ≤ 1
    · exact hsmall.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hW j i)))
    have ht0 : t 0 ≤ (d i)⁻¹ := by simpa [t] using (le_of_not_ge hsmall)
    have htK : (d i)⁻¹ ≤ t (K+1) := by
      have htK' : t (K+1) = δ⁻¹ := by
        dsimp [t, L]
        rw [Nat.cast_add, Nat.cast_one, div_self (by positivity), Real.rpow_neg_one]
      rw [htK']
      exact inv_anti₀ hδ (hd i)
    obtain ⟨j, hj, hlo, hup⟩ :=
      WangZahlLot.Obl.wz_parameter_weak_strong_reduction.exists_band t ((d i)⁻¹) K ht0 htK
    have hdir : d i ≤ r j := by
      have he : t j = (r j)⁻¹ := by simp only [t, r, Real.rpow_neg hδ.le]
      rw [he] at hlo
      exact (inv_le_inv₀ (hr j) hdpos).mp hlo
    calc
      (d i)⁻¹ ≤ t (j+1) := hup
      _ = W j i := by simp [W, hdir]
      _ ≤ ∑ k ∈ Finset.range (K+1), W k i :=
        Finset.single_le_sum (fun k _ => hW k i) hj
      _ ≤ 1 + ∑ k ∈ Finset.range (K+1), W k i := by linarith
  have hlayer : ∀ j, ∑ i, W j i ≤ A*δ^(-1/L) := by
    intro j
    have hrcount := hcount (r j) (hr j)
    calc
      ∑ i, W j i = ((Finset.univ.filter (fun i => d i ≤ r j)).card : ℝ)*t (j+1) := by
        simp [W, Finset.sum_ite, nsmul_eq_mul]
      _ ≤ (A*r j)*t (j+1) := mul_le_mul_of_nonneg_right hrcount (ht _).le
      _ = A*δ^(-1/L) := by
        rw [mul_assoc]
        congr 1
        dsimp [r, t]
        rw [← Real.rpow_add hδ]
        congr 1
        push_cast
        ring
  calc
    ∑ i, (d i)⁻¹ ≤ ∑ i, (1 + ∑ j ∈ Finset.range (K+1), W j i) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (Fintype.card ι : ℝ) + ∑ j ∈ Finset.range (K+1), ∑ i, W j i := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp
    _ ≤ (Fintype.card ι : ℝ) + ∑ _j ∈ Finset.range (K+1), A*δ^(-1/L) := by
      gcongr with j hj
      exact hlayer j
    _ = (Fintype.card ι : ℝ) + ((K : ℝ)+1)*A*δ^(-1/((K : ℝ)+1)) := by
      simp [L]
      ring

/-- The coefficient nonconcentration bound controls critical energy around
every coefficient, with an arbitrarily small power loss. -/
theorem coefficient_inverse_energy (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ η : ℝ},
      0 < δ → δ ≤ 1 → (∀ i, ‖q i‖ ≤ 10) →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
    ∀ i : Fin n, ∑ j, (dist (q i) (q j))⁻¹ ≤ C*δ^(-η-1-τ) := by
  classical
  obtain ⟨N, hN, hglobal⟩ := coefficient_card_bound
  obtain ⟨K, hK⟩ := exists_nat_gt (1/τ)
  have hK' : 1/((K : ℝ)+1) ≤ τ := by
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ)+1)).mpr
    have h := (div_lt_iff₀ hτ).mp hK
    nlinarith
  refine ⟨N+((K : ℝ)+1)*(2*N+2), by positivity, ?_⟩
  intro n q δ η hδ hδ1 hq hsep hcount i
  let B := δ^(-η)/δ
  have hB : 0 < B := by dsimp [B]; positivity
  have hn : (n : ℝ) ≤ N*B := hglobal hδ hδ1 hq hcount
  let d : Fin n → ℝ := fun j => if j=i then 1 else dist (q i) (q j)
  have hd : ∀ j, δ ≤ d j := by
    intro j
    by_cases hji : j=i
    · simpa [d, hji] using hδ1
    · simpa only [d, ite_eq_right hji] using hsep i j (Ne.symm hji)
  have hcounts : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun j => d j ≤ r)).card : ℝ) ≤ ((2*N+2)*B)*r := by
    intro r hr
    by_cases hδr : δ ≤ r
    · by_cases hrhalf : (1/2 : ℝ) ≤ r
      · have hc : ((Finset.univ.filter (fun j => d j ≤ r)).card : ℝ) ≤ (n : ℝ) := by
          have hc := Nat.cast_le (α := ℝ).mpr
            (Finset.card_filter_le (s := Finset.univ) (p := fun j => d j ≤ r))
          simpa only [Finset.card_univ, Fintype.card_fin] using hc
        apply (hc.trans hn).trans
        have hm := mul_le_mul_of_nonneg_left hrhalf (by positivity : 0 ≤ (2*N+2)*B)
        nlinarith
      let F := Finset.univ.filter (fun j => q j ∈ ball (q i) (2*r))
      have hF : (↑F : Set (Fin n)) = {j | q j ∈ ball (q i) (2*r)} := by ext j; simp [F]
      have hsub : Finset.univ.filter (fun j => d j ≤ r) ⊆ F := by
        intro j hj
        have hdj : d j ≤ r := (Finset.mem_filter.mp hj).2
        have hne : j ≠ i := by
          intro heq
          have he : d j = 1 := by simp [d, heq]
          linarith
        have hdj' : dist (q i) (q j) ≤ r := by simpa [d, hne] using hdj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [mem_ball, dist_comm]
          linarith⟩
      have hc := hcount (q i) (2*r) (by linarith) (by linarith)
      rw [← hF, Set.ncard_coe_finset] at hc
      have hcard : ((Finset.univ.filter (fun j => d j ≤ r)).card : ℝ) ≤ (F.card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      apply (hcard.trans hc).trans
      have he : δ^(-η)*(2*r/δ) = 2*B*r := by dsimp [B]; ring
      rw [he]
      nlinarith [mul_pos hB hr, mul_pos hN (mul_pos hB hr)]
    · have he : Finset.univ.filter (fun j => d j ≤ r) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj hdj
        exact hδr ((hd j).trans hdj)
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  have hb := sum_inv_le_of_linear_count d hδ hδ1 hd
    (by positivity : 0 ≤ (2*N+2)*B) hcounts K
  have hcomp : ∑ j, (dist (q i) (q j))⁻¹ ≤ ∑ j, (d j)⁻¹ := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j=i
    · simp [hji, d]
    · simp [d, hji]
  have hp : δ^(-1/((K : ℝ)+1)) ≤ δ^(-τ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by simpa only [neg_div] using neg_le_neg hK')
  have hp1 : 1 ≤ δ^(-τ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  simp only [Fintype.card_fin] at hb
  calc
    ∑ j, (dist (q i) (q j))⁻¹ ≤ (n : ℝ)+((K : ℝ)+1)*((2*N+2)*B)*δ^(-1/((K : ℝ)+1)) :=
      hcomp.trans hb
    _ ≤ N*B+((K : ℝ)+1)*((2*N+2)*B)*δ^(-τ) := by gcongr
    _ ≤ (N+((K : ℝ)+1)*(2*N+2))*(B*δ^(-τ)) := by
      have h := mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ N*B)
      nlinarith
    _ = (N+((K : ℝ)+1)*(2*N+2))*δ^(-η-1-τ) := by
      congr 1
      dsimp [B]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one δ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
