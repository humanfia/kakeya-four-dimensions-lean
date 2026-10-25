import Submission.Obl.k4_oss_unit_decay.Chain

/-!
# The Cauchy–Schwarz chain along a mixing tower (x0074)

For `μ : Fin (m+2) → Measure ℝ` and a tower `lam 0 = halfLaw (μ 0)`,
`lam (k+1) = mix (lam k) (μ (k+1))`:

* `cs_chain`: the full chain `‖T(μ)(ξ)‖^(2^m) ≤ ‖∫ e(2·4^m ξ z y) d(lam m ⊗ μ (last))‖`.
* `chain_to_stage`: `‖T(μ)(ξ)‖^(2^k) ≤ ‖∫ e(2·4^k ξ z w) d(lam k ⊗ prodLaw (μ_{k+1},…,μ_{m+1}))‖`.
* `chain_stage_bound` (early stop): if `‖∫ e(2·4^k ξ w z y) d(lam k ⊗ μ_{k+1})‖ ≤ B` for every
  `w ∈ [1, 2^r]`, `k + r = m`, then `‖T(μ)(ξ)‖^(2^k) ≤ B`.
-/

open MeasureTheory

namespace Submission.Obl.k4_oss_unit_decay


theorem prodLaw_one (μ : Fin 1 → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j)) :
    prodLaw 1 μ = μ 0 := by
  have := hμ
  rw [prodLaw, prodLaw, Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun p : ℝ × ℝ => p.1 * p.2) ∘ fun x : ℝ => (x, (1 : ℝ))) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

/-- The measures of the slots `k+1, …, m+1` of `μ : Fin (m+2) → _`, as `Fin (r+1) → _`. -/
def tailFrom {m : ℕ} (μ : Fin (m + 2) → Measure ℝ) (k r : ℕ) (h : k + r = m) :
    Fin (r + 1) → Measure ℝ :=
  fun j => μ ⟨k + 1 + j, by omega⟩

theorem chain_aux (m : ℕ) (μ : Fin (m + 2) → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (lam : ℕ → Measure ℝ) (hlam : ∀ k, k ≤ m → IsProbabilityMeasure (lam k))
    (hstep : ∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) (ξ : ℝ) :
    ∀ r k (h : k + r = m),
      ‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ k) * ξ) (p.1 * p.2)
          ∂((lam k).prod (prodLaw (r + 1) (tailFrom μ k r h)))‖ ^ (2 ^ r) ≤
        ‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ m) * ξ) (p.1 * p.2)
          ∂((lam m).prod (μ (Fin.last (m + 1))))‖
  | 0, k, h => by
      have hk : k = m := by omega
      subst hk
      have h1 : prodLaw 1 (tailFrom μ k 0 h) = μ (Fin.last (k + 1)) := by
        rw [prodLaw_one (tailFrom μ k 0 h) (fun j => hμ _)]
        simp only [tailFrom]
        congr 1
      rw [h1, pow_zero, pow_one]
  | r + 1, k, h => by
      have hk : k < m := by omega
      have := hlam k hk.le
      have hstep' := hstep k hk
      have ih := chain_aux m μ hμ lam hlam hstep ξ r (k + 1) (by omega)
      have hcs := cs_step (r + 1) (lam k) (tailFrom μ k (r + 1) h) (fun j => hμ _)
        ((2 * (4 : ℝ) ^ k) * ξ)
      have e0 : tailFrom μ k (r + 1) h 0 = μ (Fin.ofNat (m + 2) (k + 1)) := by
        simp only [tailFrom]
        congr 1
        ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt (show k + 1 < m + 2 by omega)]
      have e1 : mix (lam k) (tailFrom μ k (r + 1) h 0) = lam (k + 1) := by
        rw [e0, hstep']
      have e2 : (fun j : Fin (r + 1) => tailFrom μ k (r + 1) h j.succ) =
          tailFrom μ (k + 1) r (by omega) := by
        funext j
        simp only [tailFrom]
        congr 1
        ext
        simp only [Fin.val_succ]
        omega
      have e3 : 4 * ((2 * (4 : ℝ) ^ k) * ξ) = (2 * (4 : ℝ) ^ (k + 1)) * ξ := by ring
      rw [e1, e2, e3] at hcs
      calc _ = (‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ k) * ξ) (p.1 * p.2)
              ∂((lam k).prod (prodLaw (r + 1 + 1) (tailFrom μ k (r + 1) h)))‖ ^ 2) ^ (2 ^ r) := by
            rw [← pow_mul, ← pow_succ']
        _ ≤ (‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ (k + 1)) * ξ) (p.1 * p.2)
              ∂((lam (k + 1)).prod (prodLaw (r + 1) (tailFrom μ (k + 1) r (by omega))))‖) ^ (2 ^ r) :=
            pow_le_pow_left₀ (by positivity) hcs _
        _ ≤ _ := ih

/-- The full Cauchy–Schwarz chain: `‖T(μ)(ξ)‖^(2^m) ≤ ‖T(λ_m, μ_{m+1})(2·4^m ξ)‖`. -/
theorem cs_chain (m : ℕ) (μ : Fin (m + 2) → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (lam : ℕ → Measure ℝ) (hlam0 : lam 0 = halfLaw (μ 0))
    (hstep : ∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) (ξ : ℝ) :
    ‖∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ)‖ ^ (2 ^ m) ≤
      ‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ m) * ξ) (p.1 * p.2)
        ∂((lam m).prod (μ (Fin.last (m + 1))))‖ := by
  have := hμ
  have hlam : ∀ k, k ≤ m → IsProbabilityMeasure (lam k) := by
    intro k
    induction k with
    | zero => intro _; rw [hlam0]; unfold halfLaw; infer_instance
    | succ k ih =>
      intro hk
      have := ih (by omega)
      rw [hstep k (by omega)]
      unfold mix
      infer_instance
  have h0 := chain_aux m μ hμ lam hlam hstep ξ m 0 (by omega)
  have e : tailFrom μ 0 m (by omega) = fun j => μ j.succ := by
    funext j
    simp only [tailFrom]
    congr 1
    ext
    simp only [Fin.val_succ]
    omega
  rw [e, hlam0, pow_zero, mul_one, ← integral_pi_eq_start m μ hμ ξ] at h0
  exact h0


theorem tower_isProb (m : ℕ) (μ : Fin (m + 2) → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (lam : ℕ → Measure ℝ) (hlam0 : lam 0 = halfLaw (μ 0))
    (hstep : ∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) :
    ∀ k, k ≤ m → IsProbabilityMeasure (lam k) := by
  have := hμ
  intro k
  induction k with
  | zero => intro _; rw [hlam0]; unfold halfLaw; infer_instance
  | succ k ih =>
    intro hk
    have := ih (by omega)
    rw [hstep k (by omega)]
    unfold mix
    infer_instance

/-- The chain up to stage `k`: `‖T(μ)(ξ)‖^(2^k) ≤ ‖∫ e(2·4^k ξ z w) d(λ_k ⊗ prodLaw (μ_{k+1}, …, μ_{m+1}))‖`. -/
theorem chain_to_stage (m : ℕ) (μ : Fin (m + 2) → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (lam : ℕ → Measure ℝ) (hlam0 : lam 0 = halfLaw (μ 0))
    (hstep : ∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) (ξ : ℝ) :
    ∀ k r (h : k + r = m),
      ‖∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ)‖ ^ (2 ^ k) ≤
        ‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ k) * ξ) (p.1 * p.2)
          ∂((lam k).prod (prodLaw (r + 1) (tailFrom μ k r h)))‖
  | 0, r, h => by
      have hr : r = m := by omega
      subst hr
      have e : tailFrom μ 0 r h = fun j => μ j.succ := by
        funext j
        simp only [tailFrom]
        congr 1
        ext
        simp only [Fin.val_succ]
        omega
      rw [e, hlam0, integral_pi_eq_start r μ hμ ξ]
      simp only [pow_zero, mul_one, pow_one, le_refl]
  | k + 1, r, h => by
      have hlam := tower_isProb m μ hμ lam hlam0 hstep
      have hk : k < m := by omega
      have := hlam k hk.le
      have ih := chain_to_stage m μ hμ lam hlam0 hstep ξ k (r + 1) (by omega)
      have hcs := cs_step (r + 1) (lam k) (tailFrom μ k (r + 1) (by omega)) (fun j => hμ _)
        ((2 * (4 : ℝ) ^ k) * ξ)
      have e0 : tailFrom μ k (r + 1) (by omega) 0 = μ (Fin.ofNat (m + 2) (k + 1)) := by
        simp only [tailFrom]
        congr 1
        ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt (show k + 1 < m + 2 by omega)]
      have e1 : mix (lam k) (tailFrom μ k (r + 1) (by omega) 0) = lam (k + 1) := by
        rw [e0, hstep k hk]
      have e2 : (fun j : Fin (r + 1) => tailFrom μ k (r + 1) (by omega) j.succ) =
          tailFrom μ (k + 1) r h := by
        funext j
        simp only [tailFrom]
        congr 1
        ext
        simp only [Fin.val_succ]
        omega
      have e3 : 4 * ((2 * (4 : ℝ) ^ k) * ξ) = (2 * (4 : ℝ) ^ (k + 1)) * ξ := by ring
      rw [e1, e2, e3] at hcs
      calc _ = (‖∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ)‖ ^ (2 ^ k)) ^ 2 := by
            rw [← pow_mul, ← pow_succ]
        _ ≤ (‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ k) * ξ) (p.1 * p.2)
              ∂((lam k).prod (prodLaw (r + 1 + 1) (tailFrom μ k (r + 1) (by omega))))‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) ih _
        _ ≤ _ := hcs

/-- Early stop: if at stage `k` every bilinear form `‖∫ e(2·4^k ξ w z y) d(λ_k ⊗ μ_{k+1})‖`,
`w ∈ [1, 2^r]` (`r = m - k`), is at most `B`, then `‖T(μ)(ξ)‖^(2^k) ≤ B`. -/
theorem chain_stage_bound (m : ℕ) (μ : Fin (m + 2) → Measure ℝ)
    (hμ : ∀ j, IsProbabilityMeasure (μ j)) (hsupp : ∀ j, μ j (Set.Icc (1 : ℝ) 2)ᶜ = 0)
    (lam : ℕ → Measure ℝ) (hlam0 : lam 0 = halfLaw (μ 0))
    (hstep : ∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) (ξ : ℝ)
    (k r : ℕ) (h : k + r = m) (B : ℝ)
    (hB : ∀ w : ℝ, 1 ≤ w → w ≤ 2 ^ r →
      ‖∫ p : ℝ × ℝ, phase ((2 * (4 : ℝ) ^ k) * ξ * w) (p.1 * p.2)
        ∂((lam k).prod (μ (Fin.ofNat (m + 2) (k + 1))))‖ ≤ B) :
    ‖∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ)‖ ^ (2 ^ k) ≤ B := by
  have hlam := tower_isProb m μ hμ lam hlam0 hstep
  have := hlam k (by omega)
  refine (chain_to_stage m μ hμ lam hlam0 hstep ξ k r h).trans ?_
  have e0 : tailFrom μ k r h 0 = μ (Fin.ofNat (m + 2) (k + 1)) := by
    simp only [tailFrom]
    congr 1
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (show k + 1 < m + 2 by omega)]
  refine flat_bound r (lam k) (tailFrom μ k r h) (fun j => hμ _) (fun j => hsupp _) _ B ?_
  intro w hw1 hw2
  rw [e0]
  exact hB w hw1 hw2

end Submission.Obl.k4_oss_unit_decay
