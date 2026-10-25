-- Adapted from this LOT tree, o265, branch x1031, commit 47a52845:
-- Broad/Filling/BroadCells.lean and BaseFilling.lean.
-- Those files adapted o106, branch x0352, commit dcdf5bd50e74,
-- Submission/Obl/k4_isotropic_path_improvement/BroadCells.lean and BaseFilling.lean.
-- The determinant-success hypothesis is exposed here to use the accepted planar
-- strip-breadth sampling API directly, without duplicating direction capture.
import Submission.Lib.K4ContinuousKakeya.Incidence

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya
open scoped NNReal ENNReal

noncomputable section

/-- Power mean combines local lower bounds with a summed upper budget. -/
theorem finite_power_mean_budget {α : Type*} [Fintype α]
    (mass F : α → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (p c B : ℝ) (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hcell : ∀ q, c * mass q ^ p ≤ F q) (hbudget : ∑ q, F q ≤ B) :
    c * (∑ q, mass q) ^ p ≤ (Fintype.card α : ℝ) ^ (p - 1) * B := by
  classical
  calc
    c * (∑ q, mass q) ^ p ≤
        c * ((Fintype.card α : ℝ) ^ (p - 1) * ∑ q, mass q ^ p) := by
      apply mul_le_mul_of_nonneg_left _ hc
      simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
        Finset.univ (f := mass) hp (fun q _ => hmass q)
    _ = (Fintype.card α : ℝ) ^ (p - 1) * (∑ q, c * mass q ^ p) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card α : ℝ) ^ (p - 1) * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_le_sum (fun q _ => hcell q)).trans hbudget

/-- A cellwise determinant lower bound forces a cardinality constraint.
For the velocity-graph argument `θ` is the successful determinant fraction
and `mass` is the cell incidence mass divided by its crossing duration. -/
theorem broad_cell_power_budget {n m : ℕ} (hn : 2 ≤ n)
    (mass F : Fin m → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (θ B : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ q, θ * mass q ^ n ≤ F q)
    (hbudget : ∑ q, F q ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤ B) :
    θ ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
      (∑ q, mass q) ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤
      (m : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) * B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) - 1 := by linarith
  have hp : 1 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn0]
    linarith
  have heq : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by
    field_simp
    ring
  have hlocal (q : Fin m) : θ ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
      mass q ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤ F q ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
    have h := Real.rpow_le_rpow (mul_nonneg hθ (pow_nonneg (hmass q) n))
      (hcell q) (by positivity : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1))
    rw [Real.mul_rpow hθ (pow_nonneg (hmass q) n),
      ← Real.rpow_natCast_mul (hmass q) n] at h
    simpa only [mul_one_div] using h
  have hmean := finite_power_mean_budget mass
    (fun q => F q ^ ((1 : ℝ) / ((n : ℝ) - 1))) hmass
    ((n : ℝ) / ((n : ℝ) - 1)) (θ ^ ((1 : ℝ) / ((n : ℝ) - 1))) B
    hp (Real.rpow_nonneg hθ _) hlocal hbudget
  simpa only [Fintype.card_fin, heq] using hmean

/-- The base-filling step uses the corresponding three-dimensional moment. -/
theorem broad_cell_constraint_three {m : ℕ}
    (mass F : Fin m → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (θ B : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ q, θ * mass q ^ 3 ≤ F q)
    (hbudget : ∑ q, F q ^ ((1 : ℝ) / 2) ≤ B) :
    θ * (∑ q, mass q) ^ 3 ≤ (m : ℝ) * B ^ 2 := by
  have h := broad_cell_power_budget (n := 3) (by decide) mass F hmass θ B hθ hcell
    (by norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num]; exact hbudget)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] at h
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hθ _) (Real.rpow_nonneg
      (Finset.sum_nonneg (fun q _ => hmass q)) _)) h 2
  simp only [mul_pow] at hpow
  rw [← Real.rpow_mul_natCast hθ,
    ← Real.rpow_mul_natCast (Finset.sum_nonneg (fun q _ => hmass q)),
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ m)] at hpow
  norm_num at hpow
  exact hpow


theorem cubic_incidence_moment {m : ℕ} (mass : Fin m → ℝ)
    (hmass : ∀ j, 0 ≤ mass j) (θ D A V : ℝ) (hθ : 0 ≤ θ) (hD : 0 < D) (hV : 0 ≤ V)
    (hbudget : (∑ j, (θ * (mass j / D) ^ 3) ^ ((1 : ℝ) / 2)) ≤
      A * V ^ ((3 : ℝ) / 2)) :
    θ * (∑ j, mass j) ^ 3 ≤ (m : ℝ) * A ^ 2 * D ^ 3 * V ^ 3 := by
  have h := broad_cell_constraint_three (fun j => mass j / D)
    (fun j => θ * (mass j / D) ^ 3) (fun j => div_nonneg (hmass j) hD.le)
    θ (A * V ^ ((3 : ℝ) / 2)) hθ (fun _ => le_rfl) hbudget
  rw [← Finset.sum_div, mul_pow, ← Real.rpow_mul_natCast hV] at h
  norm_num at h
  have hs := mul_le_mul_of_nonneg_right h (pow_nonneg hD.le 3)
  have heq : θ * ((∑ j, mass j) / D) ^ 3 * D ^ 3 = θ * (∑ j, mass j) ^ 3 := by
    field_simp
  rw [heq] at hs
  nlinarith only [hs]

/-- Quantitative base filling in three dimensions, for arbitrary finite
trajectory and incidence laws. The prior and cell masses remain unchanged. -/
theorem base_incidence_filling_of_determinant_mass {α : Type*} [MeasurableSpace α] {m : ℕ}
    (θ : Measure α) [IsFiniteMeasure θ] (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 3)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 3)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) (anchorBound : ℝ) (hanchor : ∀ l, ‖a l‖ ≤ anchorBound)
    (Λ : Set α) (hΛ : MeasurableSet Λ)
    (E : Fin m → Set (EuclideanSpace ℝ (Fin 3))) (hE : ∀ j, MeasurableSet (E j))
    (hdisj : Pairwise (Function.onFun Disjoint E)) (boxBound : ℝ)
    (hbox : ∀ j, E j ⊆ Metric.closedBall 0 boxBound)
    (p R C β c : ℝ) (hp : 0 < p) (hR : 0 < R) (hC : 0 ≤ C)
    (hMK : FiniteMK 3 C) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (D : ℝ≥0) (hD : 0 < D)
    (hvol : ∀ j, volume (E j) = ENNReal.ofReal (p ^ 3))
    (hpush : ∀ j,
      (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤ D • θ.restrict Λ)
    (htube : ∀ j, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ x ∈ E j,
      x ∈ tube (R * p) (a ω.1) (e ω.1))
    (hsuccess : ∀ j, ENNReal.ofReal ((c * inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}) ^ 3) ≤
      Measure.pi (fun _ : Fin 3 => inc)
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          β ≤ |(Matrix.of fun i k : Fin 3 => e (ω i).1 k).det|}) :
    (β * c ^ 3) *
      (∑ j, inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}) ^ 3 ≤
      (m : ℝ) * (8 * C * R ^ 3) ^ 2 * (D : ℝ) ^ 3 * (θ.real Λ) ^ 3 := by
  let S : Fin m → Set (α × ℝ) := fun j => {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}
  let mass : Fin m → ℝ := fun j => inc.real (S j)
  let q : Fin m → ENNReal := fun j => ENNReal.ofReal ((c * mass j) ^ 3)
  have hsucc (j : Fin m) : q j ≤ (Measure.pi (fun _ : Fin 3 => inc))
      {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
        β ≤ |(Matrix.of fun i k : Fin 3 => e (ω i).1 k).det|} := by
    exact hsuccess j
  have h := incidence_kakeya (by decide : 2 ≤ (3 : ℕ)) hC hMK θ inc Φ hΦ a e ha he he1 hanchor
    (mul_pos hR hp) boxBound Λ hΛ Finset.univ E (fun j _ => hE j)
    (by intro j _ j' _ hne; exact hdisj hne)
    (fun j _ => hbox j) D hD (fun j _ => hpush j)
    (fun j _ => htube j) β q (fun j _ => hsucc j)
  have hfin : ENNReal.ofReal (2 ^ 3 * C * (R * p) ^ 3) *
      ∏ _i : Fin 3, (θ Λ) ^ ((1 : ℝ) / ((3 : ℝ) - 1)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.prod_ne_top
    intro i _
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hfin h
  have htermfin (j : Fin m) : volume (E j) *
      (ENNReal.ofReal β * q j / (D : ENNReal) ^ 3) ^ ((1 : ℝ) / ((3 : ℝ) - 1)) ≠ ⊤ := by
    rw [hvol]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    rw [div_eq_mul_inv]
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero 3 (by exact_mod_cast hD.ne')
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] at hreal htermfin
  rw [ENNReal.toReal_sum (fun j _ => htermfin j)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_prod,
    ENNReal.toReal_pow, ENNReal.coe_toReal, ← ENNReal.toReal_rpow] at hreal
  simp only [hvol, ENNReal.toReal_ofReal (pow_nonneg hp.le 3), q,
    ENNReal.toReal_ofReal hβ]
      at hreal
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hreal
  have hqreal (j : Fin m) : (ENNReal.ofReal ((c * mass j) ^ 3)).toReal = (c * mass j) ^ 3 :=
    ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg hc (show 0 ≤ mass j from measureReal_nonneg)) 3)
  simp_rw [hqreal, ENNReal.toReal_ofReal (by positivity : 0 ≤ 8 * C * (R * p) ^ 3)] at hreal
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (θ Λ).toReal)] at hreal
  norm_num only [show (1 / 2 : ℝ) * (3 : ℕ) = 3 / 2 by norm_num] at hreal
  have hleft : (∑ j, p ^ 3 * (β * ((c * mass j) ^ 3) / (D : ℝ) ^ 3) ^ ((1 : ℝ) / 2)) =
      p ^ 3 * ∑ j, (β * c ^ 3 * (mass j / (D : ℝ)) ^ 3) ^ ((1 : ℝ) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ring
  rw [hleft] at hreal
  have hbudget : (∑ j, (β * c ^ 3 * (mass j / (D : ℝ)) ^ 3) ^ ((1 : ℝ) / 2)) ≤
      (8 * C * R ^ 3) * (θ.real Λ) ^ ((3 : ℝ) / 2) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hp 3)).mp
    convert hreal using 1
    simp only [measureReal_def]
    ring
  exact cubic_incidence_moment mass (fun _ => measureReal_nonneg)
    (β * c ^ 3) D (8 * C * R ^ 3) (θ.real Λ) (by positivity)
    (by exact_mod_cast hD) measureReal_nonneg hbudget

/-- Retained mass and a duration-derived prior ceiling turn the cubic
moment estimate into a lower bound for the number of occupied base cells. -/
theorem base_support_lower_bound
    {X V M cells A K p w β : ℝ}
    (hV : 0 ≤ V) (hcells : 0 ≤ cells) (hM : 0 < M)
    (hK : 0 < K) (hp : 0 < p) (hw : 0 < w) (hβ : 0 ≤ β)
    (hmass : M / K ≤ X) (hprior : V ≤ K * M / w)
    (hbudget : β * X ^ 3 ≤ cells * A ^ 2 * (K * p) ^ 3 * V ^ 3) :
    β * (w / p) ^ 3 ≤ cells * A ^ 2 * K ^ 9 := by
  have hlow := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg hM.le hK.le) hmass 3) hβ
  have hhigh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV hprior 3)
    (show 0 ≤ cells * A ^ 2 * (K * p) ^ 3 by positivity)
  have h := mul_le_mul_of_nonneg_right (hlow.trans (hbudget.trans hhigh))
    (show 0 ≤ (K * w / (M * p)) ^ 3 by positivity)
  have hleft : β * (M / K) ^ 3 * (K * w / (M * p)) ^ 3 = β * (w / p) ^ 3 := by
    field_simp
  have hright : cells * A ^ 2 * (K * p) ^ 3 * (K * M / w) ^ 3 *
      (K * w / (M * p)) ^ 3 = cells * A ^ 2 * K ^ 9 := by
    field_simp
  rwa [hleft, hright] at h

end

end Submission.Obl.k4_physical_parent_potential_candidates
