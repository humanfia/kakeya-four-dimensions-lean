import Mathlib

/-!
# The frozen interface X: its applied lambdas as definitions

The frozen statements stated with the interface X (o064's children o105, o106, o107 and their
descendants) bind the graph point `x`, the planar position `y`, the velocity `v`, the dyadic
thickness `δ`, the observation `obs`, the Boolean format `fmt` and the single-chart conditions
`chart` by immediately applied lambdas. `gx`, `gy`, `gv`, `gδ`, `gobs`, `gfmt`, `gchart` are
these lambdas as definitions (`gchart_eq_frozen` checks `chart` by `rfl`), and `gobs_coarsen`
reads the observation at a coarser depth off the terminal one.

All code here was written in this tree by x0359 (o107); `floor_div_gδ_refine` reproves the
dyadic refinement of o086's `floor_dyadicWidth_refinement` without importing it.
-/

namespace Submission.Lib.K4XInterface

open MeasureTheory

/-- The frozen graph point `x l t = (t, y₁, y₂, w)` of a line. -/
def gx (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

/-- The frozen planar position `y l t`. -/
def gy (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(gx l t) 1, (gx l t) 2]

/-- The frozen planar velocity `v l`. -/
def gv (l : ℕ × (Fin 6 → ℝ)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![l.2 3, l.2 4]

/-- The frozen dyadic thickness `δ N r = 2^(-⌊r log₂ N⌋)`. -/
noncomputable def gδ (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

/-- The frozen observation `obs B a p`: exact base point and hidden bin of width `a / B`. -/
noncomputable def gobs (B a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    EuclideanSpace ℝ (Fin 3) × ℤ :=
  (WithLp.toLp 2 ![p.2, (gx p.1 p.2) 1, (gx p.1 p.2) 2], ⌊B * (gx p.1 p.2) 3 / a⌋)

/-- The frozen Boolean polynomial format. -/
def gfmt (n : ℕ) (H : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ,
    (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool,
      ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true

/-- The frozen single-chart conditions, with the extra conjunct `ex`. -/
def gchart (Nk : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) (j r Bv : ℝ)
    (Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (A : Set (ℕ × (Fin 6 → ℝ)))
    (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ex : Prop) : Prop :=
  Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧
    (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧
    (∀ i, gfmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧
      gfmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧
    (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧
      ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ ∧
        |MvPolynomial.eval (gx l t) R| ≤ κ * gδ Nk r ∧
        |MvPolynomial.eval (gx l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧
        |MvPolynomial.eval (gx l t)
            (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤
          κ * Bv ^ 2 / gδ Nk r) ∧
    (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
      Bv / κ ≤ |MvPolynomial.eval (gx p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex

/-- The frozen `chart` lambda, with the frozen `x`, `y`, `δ`, `fmt` substituted, is `gchart`. -/
theorem gchart_eq_frozen (Nk : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) (j r Bv : ℝ)
    (Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (A : Set (ℕ × (Fin 6 → ℝ)))
    (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ex : Prop) :
    ((fun x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ =>
      (fun y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) =>
        (fun δ : ℝ → ℝ → ℝ =>
          (fun fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop =>
            (fun chart : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop =>
              chart Nk M D κ T j r Bv Ev c u Q R A F ex)
            (fun Nk M D κ T j r Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex))
            (fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true))
          (fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))))
        (fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2]))
      (fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]))
      = gchart Nk M D κ T j r Bv Ev c u Q R A F ex :=
  rfl

/-- Floor division by a power of two: `⌊x / 2^n⌋ = ⌊x⌋ / 2^n`. -/
theorem floor_div_two_pow (x : ℝ) (n : ℕ) : ⌊x / (2 : ℝ) ^ n⌋ = ⌊x⌋ / (2 : ℤ) ^ n := by
  have h := Int.floor_div_natCast x (2 ^ n)
  push_cast at h
  exact h

/-- The frozen thickness `2^(-⌊r log₂ N⌋)` at a coarser depth `r ≤ s`: the hidden bin at depth `r`
is the floor quotient of the hidden bin at depth `s`. -/
theorem floor_div_gδ_refine {N r s : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (hrs : r ≤ s) (x : ℝ) :
    ⌊x / (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))⌋ =
      ⌊x / (2 : ℝ) ^ (-(⌊s * Real.log N / Real.log 2⌋ : ℤ))⌋ /
        (2 : ℤ) ^ (⌊s * Real.log N / Real.log 2⌋₊ - ⌊r * Real.log N / Real.log 2⌋₊) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hr' : 0 ≤ r * Real.log N / Real.log 2 := div_nonneg (mul_nonneg hr hlN) hl2.le
  have hs' : 0 ≤ s * Real.log N / Real.log 2 :=
    div_nonneg (mul_nonneg (hr.trans hrs) hlN) hl2.le
  have hle : r * Real.log N / Real.log 2 ≤ s * Real.log N / Real.log 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrs hlN) hl2.le
  set a := ⌊r * Real.log N / Real.log 2⌋₊ with ha
  set b := ⌊s * Real.log N / Real.log 2⌋₊ with hb
  have hab : a ≤ b := Nat.floor_le_floor hle
  have hza : (⌊r * Real.log N / Real.log 2⌋ : ℤ) = a := (Int.natCast_floor_eq_floor hr').symm
  have hzb : (⌊s * Real.log N / Real.log 2⌋ : ℤ) = b := (Int.natCast_floor_eq_floor hs').symm
  rw [hza, hzb, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, div_inv_eq_mul, div_inv_eq_mul,
    ← floor_div_two_pow]
  congr 1
  rw [mul_div_assoc]
  congr 1
  rw [eq_div_iff (by positivity), ← pow_add, Nat.add_sub_cancel' hab]

theorem gδ_pos (N r : ℝ) : 0 < gδ N r := by
  unfold gδ
  positivity

/-- Coarsening a terminal observation to depth index difference `n`. -/
def coarsenObs (n : ℕ) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  (o.1, o.2 / (2 : ℤ) ^ n)

/-- The depth index `⌊r log₂ N⌋₊` of the frozen thickness. -/
noncomputable def depthIdx (N r : ℝ) : ℕ := ⌊r * Real.log N / Real.log 2⌋₊

/-- The observation at depth `r ≤ L` is a function of the observation at depth `L`. -/
theorem gobs_coarsen {N r L : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (hrL : r ≤ L) (B : ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    gobs B (gδ N r) p = coarsenObs (depthIdx N L - depthIdx N r) (gobs B (gδ N L) p) := by
  unfold gobs coarsenObs gδ depthIdx
  rw [floor_div_gδ_refine hN hr hrL]

end Submission.Lib.K4XInterface
