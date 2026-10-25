-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.Energy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Counting

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory Metric

private theorem inv_sqrt_le_dyadic {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (Real.sqrt x)⁻¹ ≤ 2 +
      ∑' k : ℕ, if x < (1/4 : ℝ)^k then ENNReal.ofReal (2^(k+2) : ℝ) else 0 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  by_cases hs1 : Real.sqrt x ≤ 1
  · obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hs hs1
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    cases k with
    | zero =>
      have hinv : (Real.sqrt x)⁻¹ ≤ 2 := by
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < (1/2)^1) hk1.le
      exact (ENNReal.ofReal_le_ofReal hinv).trans (by simp)
    | succ k =>
      have hhalf : Real.sqrt x < (1/2 : ℝ)^k := by
        have hp : (0 : ℝ) < (1/2)^k := by positivity
        rw [pow_succ] at hk2
        nlinarith
      have hxk : x < (1/4 : ℝ)^k := by
        have hsq := mul_self_lt_mul_self hs.le hhalf
        rw [← pow_two, Real.sq_sqrt hx.le, ← pow_two, ← pow_mul, mul_comm k 2, pow_mul] at hsq
        norm_num at hsq ⊢
        exact hsq
      have hinv : (Real.sqrt x)⁻¹ ≤ (2 : ℝ)^(k+2) := by
        have h := inv_anti₀ (by positivity : (0 : ℝ) < (1/2)^(k+1+1)) hk1.le
        simpa [inv_pow] using h
      have ht := ENNReal.le_tsum (f := fun m : ℕ =>
        if x < (1/4 : ℝ)^m then ENNReal.ofReal (2^(m+2) : ℝ) else 0) k
      rw [ite_eq_left hxk] at ht
      exact (ENNReal.ofReal_le_ofReal hinv).trans (ht.trans (le_add_left le_rfl))
  · have hinv : (Real.sqrt x)⁻¹ ≤ 1 := (inv_le_one₀ hs).mpr (le_of_not_ge hs1)
    exact (ENNReal.ofReal_le_ofReal hinv).trans
      ((by norm_num : ENNReal.ofReal 1 ≤ 2).trans (le_add_right le_rfl))

/-- A linear count of small distances bounds the inverse-square-root energy.
The factor eight is the sum of a dyadic geometric series. -/
theorem sum_inv_sqrt_le_of_count {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) {A : ℝ} (hA : 0 ≤ A)
    (hcount : ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((Finset.univ.filter (fun i => d i < r)).card : ℝ) ≤ A*r) :
    ∑ i, (Real.sqrt (d i))⁻¹ ≤ 2*(Fintype.card ι : ℝ) + 8*A := by
  classical
  let W : ℕ → ι → ENNReal := fun k i =>
    if d i < (1/4 : ℝ)^k then ENNReal.ofReal (2^(k+2) : ℝ) else 0
  have hW : ∀ k, ∑ i, W k i ≤ ENNReal.ofReal (4*A) * (1/2 : ENNReal)^k := by
    intro k
    have hcountk := hcount ((1/4 : ℝ)^k) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    have he : ((1/4 : ℝ)^k) * 2^(k+2) = 4*(1/2 : ℝ)^k := by
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num
      ring
    calc
      ∑ i, W k i =
          ((Finset.univ.filter (fun i => d i < (1/4 : ℝ)^k)).card : ENNReal) *
            ENNReal.ofReal (2^(k+2) : ℝ) := by
        simp [W, Finset.sum_ite, nsmul_eq_mul]
      _ = ENNReal.ofReal (((Finset.univ.filter (fun i => d i < (1/4 : ℝ)^k)).card : ℝ) *
          (2^(k+2) : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((A*(1/4 : ℝ)^k) * (2^(k+2) : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ = ENNReal.ofReal (4*A) * (1/2 : ENNReal)^k := by
        rw [mul_assoc, he]
        rw [show A*(4*(1/2 : ℝ)^k) = (4*A)*(1/2 : ℝ)^k by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num [ENNReal.ofReal_div_of_pos]
  have htsum : (∑' k, ∑ i, W k i) ≤ ENNReal.ofReal (8*A) := by
    apply (ENNReal.tsum_le_tsum hW).trans
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    norm_num
    ring_nf
    exact le_rfl
  have hswap : ∑ i, ∑' k, W k i = ∑' k, ∑ i, W k i := by
    simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun i k => W k i))
  have hsum : ENNReal.ofReal (∑ i, (Real.sqrt (d i))⁻¹) ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) + 8*A) := by
    rw [ENNReal.ofReal_sum_of_nonneg (by intro i hi; positivity)]
    calc
      ∑ i, ENNReal.ofReal (Real.sqrt (d i))⁻¹ ≤ ∑ i, (2 + ∑' k, W k i) :=
        Finset.sum_le_sum (fun i _ => inv_sqrt_le_dyadic (hd i))
      _ = 2*(Fintype.card ι : ENNReal) + ∑' k, ∑ i, W k i := by
        rw [Finset.sum_add_distrib, hswap]
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ 2*(Fintype.card ι : ENNReal) + ENNReal.ofReal (8*A) := add_le_add le_rfl htsum
      _ = ENNReal.ofReal (2*(Fintype.card ι : ℝ) + 8*A) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast]
        norm_num
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum

/-- Coefficient nonconcentration controls the inverse-square-root energy
around every parameter. The diagonal contributes zero. -/
theorem coefficient_inverse_sqrt_energy : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ η : ℝ},
      0 < δ → δ ≤ 1 → (∀ i, ‖q i‖ ≤ 10) →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ ball q0 r} : ℝ) ≤ δ ^ (-η) * (r/δ)) →
    ∀ i : Fin n, ∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ ≤ C*(δ^(-η)/δ) := by
  classical
  obtain ⟨C, hC, hglobal⟩ := coefficient_card_bound
  refine ⟨2*C+8, by positivity, ?_⟩
  intro n q δ η hδ hδ1 hq hsep hcount i
  let d : Fin n → ℝ := fun j => if j=i then 1 else dist (q i) (q j)
  have hd : ∀ j, 0 < d j := by
    intro j
    by_cases hj : j=i
    · simp [d, hj]
    · simpa only [d, ite_eq_right hj] using hδ.trans_le (hsep i j (Ne.symm hj))
  have hA : 0 ≤ δ^(-η)/δ := by positivity
  have hcounts : ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((Finset.univ.filter (fun j => d j < r)).card : ℝ) ≤ (δ^(-η)/δ)*r := by
    intro r hr hr1
    by_cases hδr : δ ≤ r
    · let F := Finset.univ.filter (fun j => q j ∈ ball (q i) r)
      have hF : (↑F : Set (Fin n)) = {j | q j ∈ ball (q i) r} := by ext j; simp [F]
      have hsub : Finset.univ.filter (fun j => d j < r) ⊆ F := by
        intro j hj
        have hdj : d j < r := (Finset.mem_filter.mp hj).2
        have hne : j ≠ i := by
          intro heq
          have hdi : d j = 1 := by simp [d, heq]
          linarith
        have hmem : q j ∈ ball (q i) r := by
          simpa only [d, ite_eq_right hne, mem_ball, dist_comm] using hdj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have hlocal := hcount (q i) r hδr hr1
      rw [← hF, Set.ncard_coe_finset] at hlocal
      calc
        ((Finset.univ.filter (fun j => d j < r)).card : ℝ) ≤ (F.card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
        _ ≤ δ^(-η)*(r/δ) := hlocal
        _ = (δ^(-η)/δ)*r := by ring
    · have hnil : Finset.univ.filter (fun j => d j < r) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj hlt
        by_cases hji : j=i
        · have he : d j = 1 := by simp [d, hji]
          linarith
        · have hdj : d j = dist (q i) (q j) := by simp [d, hji]
          have hdist := hsep i j (Ne.symm hji)
          linarith
      rw [hnil, Finset.card_empty, Nat.cast_zero]
      positivity
  have henergy := sum_inv_sqrt_le_of_count d hd hA hcounts
  have hcomp : ∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ ≤ ∑ j, (Real.sqrt (d j))⁻¹ := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j=i
    · simp [hji, d]
    · simp [d, hji]
  have hn := hglobal hδ hδ1 hq hcount
  simp only [Fintype.card_fin] at henergy
  calc
    ∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ ≤ 2*(n : ℝ)+8*(δ^(-η)/δ) :=
      hcomp.trans henergy
    _ ≤ (2*C+8)*(δ^(-η)/δ) := by nlinarith

end WangZahlLot.Obl.wz_jet_close_pair_moment
