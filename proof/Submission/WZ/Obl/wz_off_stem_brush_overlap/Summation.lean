-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_off_stem_brush_overlap.Summation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_off_stem_brush_overlap

/-- The number of dyadic scales costs an arbitrarily small negative power. -/
lemma dyadic_length_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (N : ℕ), 0 < δ →
      (2 : ℝ) ^ N ≤ 2 / δ → (N + 1 : ℝ) ≤ C * δ ^ (-ε) := by
  let q : ℝ := (2 : ℝ) ^ ε
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hε
  refine ⟨(4 : ℝ) ^ ε / (q - 1), by positivity, ?_⟩
  intro δ N hδ hN
  have hp : (2 : ℝ) ^ (N + 1) ≤ 4 / δ := by
    rw [pow_succ]
    calc
      _ ≤ (2 / δ) * 2 := mul_le_mul_of_nonneg_right hN (by norm_num)
      _ = _ := by ring
  have hpr : q ^ (N + 1) ≤ (4 / δ) ^ ε := by
    have heq : q ^ (N + 1) = ((2 : ℝ) ^ (N + 1)) ^ ε := by
      change ((2 : ℝ) ^ ε) ^ (N + 1) = ((2 : ℝ) ^ (N + 1)) ^ ε
      rw [← Real.rpow_mul_natCast (by norm_num),
        ← Real.rpow_natCast_mul (by norm_num)]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow (by positivity) hp hε.le
  have hsum : (N + 1 : ℝ) ≤ ∑ k ∈ Finset.range (N + 1), q ^ k := by
    calc
      _ = ∑ k ∈ Finset.range (N + 1), (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => one_le_pow₀ hq.le)
  calc
    (N + 1 : ℝ) ≤ (q ^ (N + 1) - 1) / (q - 1) := by
      rwa [geom_sum_eq hq.ne'] at hsum
    _ ≤ (4 / δ) ^ ε / (q - 1) := by gcongr; linarith
    _ = (4 : ℝ) ^ ε / (q - 1) * δ ^ (-ε) := by
      rw [Real.div_rpow (by norm_num) hδ.le, Real.rpow_neg hδ.le]
      ring

/-- A cumulative linear count and reciprocal weights give a dyadic logarithmic bound. -/
lemma dyadic_weighted_sum {ι : Type*} (F : Finset ι) (a d : ι → ℝ)
    {δ A B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ j ∈ F, 0 ≤ a j) (hd : ∀ j ∈ F, δ ≤ d j ∧ d j ≤ 2)
    (hab : ∀ j ∈ F, a j ≤ B / d j)
    (hc : ∀ θ : ℝ, δ ≤ θ → ((F.filter (fun j => d j ≤ θ)).card : ℝ) ≤ A * θ) :
    ∃ N : ℕ, (2 : ℝ) ^ N ≤ 2 / δ ∧
      ∑ j ∈ F, a j ≤ (N + 1 : ℝ) * (2 * A * B) := by
  classical
  obtain ⟨N, hN, hN'⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 2 / δ by rw [le_div_iff₀ hδ]; linarith) (by norm_num : (1 : ℝ) < 2)
  let s : ℕ → Finset ι := fun k => F.filter (fun j => δ * 2 ^ k ≤ d j ∧ d j < δ * 2 ^ (k + 1))
  have hcover : ∀ j ∈ F, ∃ k ∈ Finset.range (N + 1), δ * 2 ^ k ≤ d j ∧ d j < δ * 2 ^ (k + 1) := by
    intro j hj
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
      (show (1 : ℝ) ≤ d j / δ by rw [le_div_iff₀ hδ]; simpa using (hd j hj).1)
      (by norm_num : (1 : ℝ) < 2)
    have hkN : k < N + 1 := by
      by_contra! h
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
      have hdiv : d j / δ ≤ 2 / δ := div_le_div_of_nonneg_right (hd j hj).2 hδ.le
      linarith
    refine ⟨k, Finset.mem_range.mpr hkN, ?_, ?_⟩
    · have := (le_div_iff₀ hδ).mp hk
      nlinarith
    · have := (div_lt_iff₀ hδ).mp hk'
      nlinarith
  have hdecomp : ∑ j ∈ F, a j ≤ ∑ k ∈ Finset.range (N + 1), ∑ j ∈ s k, a j := by
    simp only [s, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨k, hk, hkj⟩ := hcover j hj
    calc
      a j = (if δ * 2 ^ k ≤ d j ∧ d j < δ * 2 ^ (k + 1) then a j else 0) := (ite_eq_left hkj).symm
      _ ≤ _ := Finset.single_le_sum
        (f := fun l : ℕ => if δ * 2 ^ l ≤ d j ∧ d j < δ * 2 ^ (l + 1) then a j else 0)
        (fun l _ => by split_ifs <;> simp [ha j hj]) hk
  have hpiece : ∀ k : ℕ, ∑ j ∈ s k, a j ≤ 2 * A * B := by
    intro k
    have hkpos : 0 < δ * (2 : ℝ) ^ k := by positivity
    have hθ : δ ≤ δ * (2 : ℝ) ^ (k + 1) := by
      have := one_le_pow₀ (n := k + 1) (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    have hsc : ((s k).card : ℝ) ≤ A * (δ * 2 ^ (k + 1)) := by
      refine le_trans ?_ (hc _ hθ)
      exact_mod_cast Finset.card_le_card (show s k ⊆ F.filter (fun j => d j ≤ δ * 2 ^ (k + 1)) by
        intro j hj
        obtain ⟨hjF, hj₁, hj₂⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hjF, hj₂.le⟩)
    calc
      ∑ j ∈ s k, a j ≤ ∑ j ∈ s k, B / (δ * 2 ^ k) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hjF, hj₁, hj₂⟩ := Finset.mem_filter.mp hj
        exact (hab j hjF).trans (div_le_div_of_nonneg_left hB hkpos hj₁)
      _ = ((s k).card : ℝ) * (B / (δ * 2 ^ k)) := by simp
      _ ≤ (A * (δ * 2 ^ (k + 1))) * (B / (δ * 2 ^ k)) := by gcongr
      _ = 2 * A * B := by rw [pow_succ]; field_simp
  refine ⟨N, hN, hdecomp.trans ?_⟩
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), 2 * A * B := Finset.sum_le_sum (fun k _ => hpiece k)
    _ = _ := by simp

lemma power_weighted_sum (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (F : Finset ι) (a d : ι → ℝ)
      (δ A B : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ A → 0 ≤ B →
      (∀ j ∈ F, 0 ≤ a j) → (∀ j ∈ F, δ ≤ d j ∧ d j ≤ 2) →
      (∀ j ∈ F, a j ≤ B / d j) →
      (∀ θ : ℝ, δ ≤ θ → ((F.filter (fun j => d j ≤ θ)).card : ℝ) ≤ A * θ) →
      ∑ j ∈ F, a j ≤ C * δ ^ (-ε) * (2 * A * B) := by
  obtain ⟨C, hC, hlen⟩ := dyadic_length_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro ι F a d δ A B hδ hδ1 hA hB ha hd hab hc
  obtain ⟨N, hN, hs⟩ := dyadic_weighted_sum F a d hδ hδ1 hA hB ha hd hab hc
  exact hs.trans (mul_le_mul_of_nonneg_right (hlen δ N hδ hN) (by positivity))

end WangZahlLot.Obl.wz_off_stem_brush_overlap
