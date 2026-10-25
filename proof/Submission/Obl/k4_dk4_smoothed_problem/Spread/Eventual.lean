import Submission.Obl.k4_dk4_smoothed_problem.Spread.Finite
import Submission.Obl.k4_dk4_smoothed_problem.Growth

/-!
# From the projected multiplicity bound to the spread property

Applying the multiplicity bound (MULT) with `α/2` at the threshold `T = 2^((1+α/2)k)`
in the finite-scale spread estimate gives, along any sequence of scales tending to
infinity, the power decay of the incidence mass over base sets of volume `≤ N^(-α)`:
the low-multiplicity term is `≤ 36 (k+1)² / c · N^(-α/2)`, the high-multiplicity term is
`≤ N^(-θ₀)`. All proofs here are original Mathlib proofs.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Spread

open Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

/-- `2^(a k) = (2^k)^a`. -/
theorem two_rpow_mul_nat (a : ℝ) (K : ℕ) : (2 : ℝ) ^ (a * (K : ℝ)) = ((2 : ℝ) ^ K) ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-- The real inequality behind the spread bound at one scale `N`. -/
theorem spread_real_bound {N n c θ₀ α θ P : ℝ} (hN : 1 ≤ N) (hn : 0 < n) (hc : 0 < c)
    (hlow : c * N ^ (3 : ℝ) ≤ n * P) (hθ1 : θ ≤ θ₀ / 2) (hθ2 : θ ≤ α / 4)
    (h2 : N ^ (-(θ₀ / 2)) ≤ 1 / 2) (h3 : 72 / c * P ≤ N ^ (α / 4)) :
    n⁻¹ * (n * N ^ (-θ₀) + 36 * N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α)) ≤ N ^ (-θ) := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hP : 0 ≤ P := by
    have : 0 < n * P := lt_of_lt_of_le (by positivity) hlow
    exact (pos_of_mul_pos_right this hn.le).le
  have e2 : N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α) = N ^ (3 : ℝ) * N ^ (-(α / 2)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  have e1 : n⁻¹ * (n * N ^ (-θ₀) + 36 * N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α)) =
      N ^ (-θ₀) + 36 * (n⁻¹ * N ^ (3 : ℝ)) * N ^ (-(α / 2)) := by
    rw [show 36 * N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α) =
      36 * (N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α)) by ring, e2]
    field_simp
  have e3 : n⁻¹ * N ^ (3 : ℝ) ≤ P / c := by
    rw [inv_mul_le_iff₀ hn, mul_div_assoc', le_div_iff₀ hc]
    linarith
  have hθ0 : N ^ (-θ₀) ≤ N ^ (-θ) * (1 / 2) := by
    have : N ^ (-θ₀) = N ^ (-θ) * N ^ (-(θ₀ - θ)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [this]
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans h2
  have hα0 : 36 * (P / c) * N ^ (-(α / 2)) ≤ N ^ (-θ) * (1 / 2) := by
    have hsplit : N ^ (-(α / 2)) = N ^ (-θ) * N ^ (-(α / 2 - θ)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hle : N ^ (-(α / 2 - θ)) ≤ N ^ (-(α / 4)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have hq : 36 * (P / c) * N ^ (-(α / 4)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hNpos.le]
      have hpos : 0 < N ^ (α / 4) := Real.rpow_pos_of_pos hNpos _
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      have : 72 / c * P = 2 * (36 * (P / c)) := by ring
      linarith
    calc 36 * (P / c) * N ^ (-(α / 2)) = N ^ (-θ) * (36 * (P / c) * N ^ (-(α / 2 - θ))) := by
          rw [hsplit]; ring
      _ ≤ N ^ (-θ) * (36 * (P / c) * N ^ (-(α / 4))) := by gcongr
      _ ≤ N ^ (-θ) * (1 / 2) := by gcongr
  rw [e1]
  have : 36 * (n⁻¹ * N ^ (3 : ℝ)) * N ^ (-(α / 2)) ≤ 36 * (P / c) * N ^ (-(α / 2)) := by
    gcongr
  linarith


/-- The conclusion of `k4_plank_projected_multiplicity` (MULT), verbatim. -/
def MultiplicityBound : Prop :=
  ∀ c R α : ℝ, 0 < c → 1 ≤ R → 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 4)),
      c * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2 ≤ (n : ℝ) →
      (∀ i : Fin n, x i 0 = 0 ∧ v i 0 = 1 ∧ ‖v i‖ ≤ 2) →
      (∀ i j : Fin n, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖) →
      (∀ i : Fin n, ‖x i‖ ≤ R) →
      ∑ i : Fin n, MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
        (2 : ℝ) ^ ((1 + α) * (k : ℝ)) ≤ (((Finset.univ : Finset (Fin n)).filter (fun j =>
          |(x j 1 + t * v j 1) - (x i 1 + t * v i 1)| ≤ (2 : ℝ) ^ (-(k : ℤ)) ∧
          |(x j 2 + t * v j 2) - (x i 2 + t * v i 2)| ≤ (2 : ℝ) ^ (-(k : ℤ)))).card : ℝ)} ≤
        ENNReal.ofReal ((n : ℝ) * (2 : ℝ) ^ (-(θ * (k : ℝ))))

/-- **Spread along a sequence of scales.** Given MULT and line families at scales
`κ j → ∞` satisfying the DK4 hypotheses (with `c`, `R` fixed), the smoothed priors with
box radius `2^(-κ j)/12` have the spread property at the scales `N_j = 2^(κ j)`. Only the
two observed coordinates of the intercepts `b` and slopes `s` matter. -/
theorem smoothedPrior_spread_eventually (hMULT : MultiplicityBound)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R)
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (n : ℕ → ℕ) (x v : (j : ℕ) → Fin (n j) → EuclideanSpace ℝ (Fin 4))
    (b s : (j : ℕ) → Fin (n j) → Fin 3 → ℝ)
    (hb : ∀ j i, b j i 0 = x j i 1 ∧ b j i 1 = x j i 2)
    (hs : ∀ j i, s j i 0 = v j i 1 ∧ s j i 1 = v j i 2)
    (hlow : ∀ j, c * (2 : ℝ) ^ (3 * κ j) / ((κ j : ℝ) + 1) ^ 2 ≤ (n j : ℝ))
    (hcoord : ∀ j i, x j i 0 = 0 ∧ v j i 0 = 1 ∧ ‖v j i‖ ≤ 2)
    (hsep : ∀ j (i i' : Fin (n j)), i ≠ i' → (2 : ℝ) ^ (-(κ j : ℤ)) ≤ ‖v j i - v j i'‖)
    (hbdd : ∀ j i, ‖x j i‖ ≤ R) :
    ∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ j in atTop, ∀ U : Set (EuclideanSpace ℝ (Fin 3)),
      volume U ≤ ENNReal.ofReal (((2 : ℝ) ^ (κ j)) ^ (-α)) →
      ((smoothedPrior ((2 : ℝ) ^ (-(κ j : ℤ)) / 12) (b j) (s j)).prod volume) (pairSpread U) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (κ j)) ^ (-θ)) := by
  intro α hα
  obtain ⟨θ₀, hθ₀, k₀, hk₀⟩ := hMULT c R (α / 2) hc hR (by positivity)
  refine ⟨min (α / 4) (θ₀ / 2), lt_min (by positivity) (by positivity), ?_⟩
  have ev2 : ∀ᶠ K : ℕ in atTop, ((2 : ℝ) ^ K) ^ (-(θ₀ / 2)) ≤ 1 / 2 := by
    obtain ⟨K₁, hK₁⟩ := exists_nat_ge (2 / θ₀)
    filter_upwards [eventually_ge_atTop K₁] with K hK
    rw [← two_rpow_mul_nat]
    have hKr : (2 / θ₀ : ℝ) ≤ K := hK₁.trans (by exact_mod_cast hK)
    have hexp : -(θ₀ / 2) * (K : ℝ) ≤ -1 := by
      have : 2 ≤ θ₀ * K := by
        have := mul_le_mul_of_nonneg_left hKr hθ₀.le
        rwa [mul_div_cancel₀ _ hθ₀.ne'] at this
      linarith
    calc (2 : ℝ) ^ (-(θ₀ / 2) * (K : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 / 2 := by norm_num [Real.rpow_neg_one]
  have ev3 : ∀ᶠ K : ℕ in atTop, 72 / c * ((K : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ K) ^ (α / 4) :=
    eventually_poly_le_dyadic_rpow (72 / c) (by positivity) 2 (by positivity)
  filter_upwards [hκ.eventually ((eventually_ge_atTop k₀).and (ev2.and ev3))] with j hj
  obtain ⟨h1, h2, h3⟩ := hj
  intro U hU
  set K := κ j with hKdef
  set N : ℝ := (2 : ℝ) ^ K with hNdef
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hNpos : 0 < N := by positivity
  have hnpos : (0 : ℝ) < n j := lt_of_lt_of_le (by positivity) (hlow j)
  have hδ : (2 : ℝ) ^ (-(K : ℤ)) = N⁻¹ := by rw [zpow_neg, zpow_natCast]
  set r : ℝ := (2 : ℝ) ^ (-(K : ℤ)) / 12 with hrdef
  have hδpos : 0 < (2 : ℝ) ^ (-(K : ℤ)) := by positivity
  have hr : 0 < r := by positivity
  have h4r : 4 * r ≤ (2 : ℝ) ^ (-(K : ℤ)) := by rw [hrdef]; linarith
  set T : ℝ := (2 : ℝ) ^ ((1 + α / 2) * (K : ℝ)) with hTdef
  have hT : 0 ≤ T := by positivity
  have hfin := smoothedPrior_spread_le (b j) (s j) hr h4r hT U
  have hmult := hk₀ K h1 (n j) (x j) (v j) (hlow j) (hcoord j) (hsep j) (hbdd j)
  have hsets : ∑ i, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        T ≤ (mult (b j) (s j) ((2 : ℝ) ^ (-(K : ℤ))) i t : ℝ)} =
      ∑ i : Fin (n j), volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
        (2 : ℝ) ^ ((1 + α / 2) * (K : ℝ)) ≤ (((Finset.univ : Finset (Fin (n j)))).filter
          (fun i' => |(x j i' 1 + t * v j i' 1) - (x j i 1 + t * v j i 1)| ≤ (2 : ℝ) ^ (-(K : ℤ)) ∧
          |(x j i' 2 + t * v j i' 2) - (x j i 2 + t * v j i 2)| ≤ (2 : ℝ) ^ (-(K : ℤ)))).card} := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext t
    simp only [mult, (hb j _).1, (hb j _).2, (hs j _).1, (hs j _).2, hTdef]
  rw [hsets] at hfin
  have hA : (ENNReal.ofReal (2 * r) ^ 2)⁻¹ = ENNReal.ofReal (36 * N ^ (2 : ℝ)) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [hrdef, hδ, Real.rpow_two]
    field_simp
    ring
  have hninv : ((n j : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n j : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
  have hθ₀N : (2 : ℝ) ^ (-(θ₀ * (K : ℝ))) = N ^ (-θ₀) := by
    rw [hNdef, ← two_rpow_mul_nat]
    ring_nf
  have hTN : T = N ^ (1 + α / 2) := by rw [hTdef, hNdef, two_rpow_mul_nat]
  have hlow' : c * N ^ (3 : ℝ) ≤ (n j : ℝ) * ((K : ℝ) + 1) ^ 2 := by
    have h := hlow j
    have hK1 : (0 : ℝ) < ((K : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hK1] at h
    have : N ^ (3 : ℝ) = (2 : ℝ) ^ (3 * K) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hNdef, ← pow_mul,
        mul_comm]
    rw [this]
    exact h
  rw [hθ₀N] at hmult
  calc ((smoothedPrior r (b j) (s j)).prod volume) (pairSpread U)
      ≤ (n j : ℝ≥0∞)⁻¹ * (∑ i : Fin (n j), volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
          (2 : ℝ) ^ ((1 + α / 2) * (K : ℝ)) ≤ (((Finset.univ : Finset (Fin (n j)))).filter
            (fun i' => |(x j i' 1 + t * v j i' 1) - (x j i 1 + t * v j i 1)| ≤
              (2 : ℝ) ^ (-(K : ℤ)) ∧
            |(x j i' 2 + t * v j i' 2) - (x j i 2 + t * v j i 2)| ≤
              (2 : ℝ) ^ (-(K : ℤ)))).card} +
          (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * (ENNReal.ofReal T * volume U)) := hfin
    _ ≤ ENNReal.ofReal ((n j : ℝ)⁻¹) * (ENNReal.ofReal ((n j : ℝ) * N ^ (-θ₀)) +
          ENNReal.ofReal (36 * N ^ (2 : ℝ)) * (ENNReal.ofReal (N ^ (1 + α / 2)) *
            ENNReal.ofReal (N ^ (-α)))) := by
        rw [hninv, hA, ← hTN]
        gcongr
    _ = ENNReal.ofReal ((n j : ℝ)⁻¹ * ((n j : ℝ) * N ^ (-θ₀) +
          36 * N ^ (2 : ℝ) * N ^ (1 + α / 2) * N ^ (-α))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (N ^ (-min (α / 4) (θ₀ / 2))) :=
        ENNReal.ofReal_le_ofReal (spread_real_bound hN hnpos hc hlow'
          (min_le_right _ _) (min_le_left _ _) h2 h3)

end Submission.Obl.k4_dk4_smoothed_problem.Spread
