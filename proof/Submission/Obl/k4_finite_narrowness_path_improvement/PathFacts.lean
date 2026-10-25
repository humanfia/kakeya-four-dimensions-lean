import Mathlib
import Submission.Obl.k4_native_grid_profile_extension.Dyadic

/-!
# Elementary facts about the critical-path data of the frozen interface X

The frozen statement of o107 (and of every child or sibling stated with the interface X)
binds the graph point `x`, the planar position `y`, the velocity `v`, the dyadic thickness
`δ`, the observation `obs`, the Boolean format `fmt` and the single-chart conditions `chart`
by immediately applied lambdas. `gx`, `gy`, `gv`, `gδ`, `gobs`, `gfmt` and `gchart` are
these lambdas as definitions; after beta reduction the frozen terms are these definitions
applied, by `rfl` (see `gchart_eq_frozen`).

* `gchart_velocity`: the two endpoints of the dyadic block confine the velocity of every
  assigned line to the ellipse `u + Q (ball 0 (2 κ 2^T))`.
* `gy_sub_extend_le`: the chart parallelogram on a block, extended to any time.
* `gobs_coarsen`: the observation at depth `r` is a function of the observation at a finer
  depth `L`, so terminal lists can be read through coarser ones.
* `gchart_mono`, `gchart_restrict`: enlarging slack and format bounds, and passing to
  measurable sub-assignments in format.
* `floor_fill`: the true floor and the saturation bound of a path chart give
  `ν(A) ≤ κ² 2^T (ν × dt)(F)`.
* `tilted_box_of_frame`: a chart frame confines the major coordinate and the transverse
  combination `w₁ - λ w₀` (tilted boxes of the candidate model).
* `frame_comp_apply`, `norm_le_of_rows`, `sum_abs_inv_fin2`, `sum_abs_mul_fin2`: building
  output frames from a parent frame and normalized row functionals.
-/

namespace Submission.Obl.k4_finite_narrowness_path_improvement

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

/-- Positions of a line move with its velocity. -/
theorem gy_sub_gy (l : ℕ × (Fin 6 → ℝ)) (s t : ℝ) : gy l t - gy l s = (t - s) • gv l := by
  ext i
  fin_cases i <;> simp [gy, gx, gv] <;> ring

/-- The moving-center offset at time `t`, expressed from time `s`. -/
theorem gy_offset_eq (l : ℕ × (Fin 6 → ℝ)) (c u : EuclideanSpace ℝ (Fin 2)) (s t : ℝ) :
    gy l t - c - t • u = (gy l s - c - s • u) + (t - s) • (gv l - u) := by
  have h := gy_sub_gy l s t
  rw [smul_sub, ← h, sub_smul]
  abel

/-- Two times in the chart parallelogram confine the velocity. -/
theorem velocity_le_of_two_times (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (l : ℕ × (Fin 6 → ℝ)) {t₁ t₂ κ : ℝ} (h12 : t₁ < t₂)
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (gy l t₁ - c - t₁ • u)‖ ≤ κ)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (gy l t₂ - c - t₂ • u)‖ ≤ κ) :
    ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ 2 * κ / (t₂ - t₁) := by
  have hpos : 0 < t₂ - t₁ := sub_pos.mpr h12
  have heq : (t₂ - t₁) • Matrix.toEuclideanLin Q⁻¹ (gv l - u) =
      Matrix.toEuclideanLin Q⁻¹ (gy l t₂ - c - t₂ • u) -
        Matrix.toEuclideanLin Q⁻¹ (gy l t₁ - c - t₁ • u) := by
    rw [← map_smul, ← map_sub, gy_offset_eq l c u t₁ t₂]
    abel_nf
  have hnorm : (t₂ - t₁) * ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ 2 * κ := by
    have := norm_sub_le (Matrix.toEuclideanLin Q⁻¹ (gy l t₂ - c - t₂ • u))
      (Matrix.toEuclideanLin Q⁻¹ (gy l t₁ - c - t₁ • u))
    rw [← heq, norm_smul, Real.norm_of_nonneg hpos.le] at this
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- The chart parallelogram of a block, extended to an arbitrary time `t`. -/
theorem gy_sub_extend_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (l : ℕ × (Fin 6 → ℝ)) {s κ V : ℝ}
    (hs : ‖Matrix.toEuclideanLin Q⁻¹ (gy l s - c - s • u)‖ ≤ κ)
    (hv : ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ V) (t : ℝ) :
    ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ + |t - s| * V := by
  rw [gy_offset_eq l c u s t, map_add, map_smul]
  calc _ ≤ ‖Matrix.toEuclideanLin Q⁻¹ (gy l s - c - s • u)‖ +
          ‖(t - s) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ := norm_add_le _ _
    _ ≤ κ + |t - s| * V := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add hs (mul_le_mul_of_nonneg_left hv (abs_nonneg _))

/-- Every line assigned to a chart has velocity in `u + Q (ball 0 (2 κ 2^T))`. -/
theorem gchart_velocity {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) :
    ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ 2 * κ * (2 : ℝ) ^ T := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hA, -⟩ := h
  obtain ⟨-, -, hl⟩ := hA l hl
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hlt : j / (2 : ℝ) ^ T < (j + 1) / (2 : ℝ) ^ T :=
    div_lt_div_of_pos_right (by linarith) h2
  have h₁ := (hl _ ⟨le_rfl, hlt.le⟩).1
  have h₂ := (hl _ ⟨hlt.le, le_rfl⟩).1
  have := velocity_le_of_two_times Q c u l hlt h₁ h₂
  have hdiff : (j + 1) / (2 : ℝ) ^ T - j / (2 : ℝ) ^ T = 1 / (2 : ℝ) ^ T := by
    field_simp
    ring
  rw [hdiff] at this
  calc _ ≤ 2 * κ / (1 / (2 : ℝ) ^ T) := this
    _ = 2 * κ * (2 : ℝ) ^ T := by field_simp

/-- The frozen `δ` is the dyadic width of o086. -/
theorem gδ_eq_dyadicWidth (N r : ℝ) :
    gδ N r = Submission.Obl.k4_native_grid_profile_extension.dyadicWidth N r := rfl

theorem gδ_pos (N r : ℝ) : 0 < gδ N r := by
  unfold gδ
  positivity

/-- Coarsening a terminal observation to depth index difference `n`. -/
def coarsenObs (n : ℕ) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  (o.1, o.2 / (2 : ℤ) ^ n)

/-- The observation at depth `r ≤ L` is a function of the observation at depth `L`. -/
theorem gobs_coarsen {N r L : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (hrL : r ≤ L) (B : ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    gobs B (gδ N r) p =
      coarsenObs (Submission.Obl.k4_native_grid_profile_extension.depthIndex N L -
        Submission.Obl.k4_native_grid_profile_extension.depthIndex N r) (gobs B (gδ N L) p) := by
  unfold gobs coarsenObs
  rw [gδ_eq_dyadicWidth, gδ_eq_dyadicWidth,
    Submission.Obl.k4_native_grid_profile_extension.floor_dyadicWidth_refinement hN hr hrL]

/-- Enlarging the format bounds keeps the Boolean format. -/
theorem gfmt_mono {n : ℕ} {H H' : ℝ} {D D' : ℕ} {A : Set (Fin n → ℝ)} (hH : H ≤ H')
    (hD : D ≤ D') (h : gfmt n H D A) : gfmt n H' D' A := by
  obtain ⟨m₀, hm, p₀, hp, b₀, hb⟩ := h
  exact ⟨m₀, hm.trans hH, p₀, fun i => (hp i).trans hD, b₀, hb⟩

/-- Charts stay charts for larger slack, complexity and degree bounds. -/
theorem gchart_mono {Nk : ℝ} {M M' D D' : ℕ} {κ κ' : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) (hNk : 1 ≤ Nk) (hM : M ≤ M')
    (hD : D ≤ D') (hκ : 0 < κ) (hκκ : κ ≤ κ') (hBv : 0 ≤ Bv) (hex : ex → ex') :
    gchart Nk M' D' κ' T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hA, hF, hfmt, hAl, hFp, hx⟩ := h
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hNk hM
  have hδ := gδ_pos Nk r
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  refine ⟨hQ, hcu.trans hpow, hQQ.trans hpow, hQs.trans ?_, hdeg, fun e => (hcoef e).trans hpow,
    hA, hF, fun i => ⟨gfmt_mono hpow hD (hfmt i).1, gfmt_mono hpow hD (hfmt i).2⟩, ?_, ?_,
    hex hx⟩
  · exact div_le_div_of_nonneg_right hκκ h2.le
  · intro l hl
    obtain ⟨h1, h2', h3⟩ := hAl l hl
    refine ⟨h1.trans hpow, fun e => (h2' e).trans hpow, fun t ht => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := h3 t ht
    refine ⟨a1.trans hκκ, a2.trans ?_, a3.trans ?_, a4.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hκκ hδ.le
    · exact mul_le_mul_of_nonneg_right hκκ hBv
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hκκ (sq_nonneg _)) hδ.le
  · intro p hp
    obtain ⟨b1, b2, b3, b4⟩ := hFp p hp
    exact ⟨b1, b2, b3, (div_le_div_of_nonneg_left hBv hκ hκκ).trans b4⟩

/-- A chart restricted to measurable sub-assignments in format is a chart. -/
theorem gchart_restrict {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A A' : Set (ℕ × (Fin 6 → ℝ))}
    {F F' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) (hA : A' ⊆ A) (hF : F' ⊆ F)
    (hF'A' : ∀ p ∈ F', p.1 ∈ A') (hmA : MeasurableSet A') (hmF : MeasurableSet F')
    (hfmt : ∀ i, gfmt 6 (Nk ^ M) D {x | (i, x) ∈ A'} ∧
      gfmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F'})
    (hex : ex') : gchart Nk M D κ T j r Bv Ev c u Q R A' F' ex' := by
  obtain ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, -, -, -, hAl, hFp, -⟩ := h
  refine ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hmA, hmF, hfmt, fun l hl => hAl l (hA hl), ?_, hex⟩
  intro p hp
  obtain ⟨b1, -, b3, b4⟩ := hFp p (hF hp)
  exact ⟨b1, hF'A' p hp, b3, b4⟩

/-- The true floor and the saturation bound of a path chart: the selected incidences fill
the assigned lines times the block, `ν(A) ≤ κ² 2^T (ν × dt)(F)`. -/
theorem floor_fill {nuA nuF : ENNReal} {f D κ : ℝ} (T : ℕ) (hκ : 0 < κ) (hD : 0 < D)
    (hfloor : ENNReal.ofReal (f * D / ((2 : ℝ) ^ T * κ)) ≤ nuF)
    (hsat : nuA ≤ ENNReal.ofReal (κ * f * D)) :
    nuA ≤ ENNReal.ofReal (κ ^ 2 * (2 : ℝ) ^ T) * nuF := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  calc nuA ≤ ENNReal.ofReal (κ * f * D) := hsat
    _ = ENNReal.ofReal (κ ^ 2 * (2 : ℝ) ^ T) * ENNReal.ofReal (f * D / ((2 : ℝ) ^ T * κ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (κ ^ 2 * (2 : ℝ) ^ T) * nuF := by gcongr

/-- Components of a `2 × 2` matrix acting on the Euclidean plane. -/
theorem toEuclideanLin_apply_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) (a : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : (Matrix.toEuclideanLin M a) i = M i 0 * a 0 + M i 1 * a 1 := by
  fin_cases i <;> simp [Matrix.toLpLin_apply]

/-- `Q (Q⁻¹ w) = w` for an invertible frame. -/
theorem toEuclideanLin_inv_cancel (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ w) = w := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr hQ)]
  simp

/-- The squared Euclidean norm in the plane. -/
theorem norm_sq_fin2 (a : EuclideanSpace ℝ (Fin 2)) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

/-- A square bound `x² ≤ y z` with `z ≤ κ²` gives `|x| ≤ κ √y`. -/
theorem abs_le_of_sq {x y z κ : ℝ} (h : x ^ 2 ≤ y * z) (hy : 0 ≤ y) (hz : z ≤ κ ^ 2)
    (hκ : 0 ≤ κ) : |x| ≤ κ * Real.sqrt y := by
  have h1 : x ^ 2 ≤ (κ * Real.sqrt y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hy]
    calc x ^ 2 ≤ y * z := h
      _ ≤ y * κ ^ 2 := mul_le_mul_of_nonneg_left hz hy
      _ = κ ^ 2 * y := by ring
  exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (by positivity))

/-- Rows of a chart frame (paper Prop. 4.7, tilted boxes): a point `w` with `‖Q⁻¹ w‖ ≤ κ`
has major component `|w₀| ≤ κ ‖row₀‖`, and the transverse combination `w₁ - λ w₀`, with
`λ = ⟨row₁, row₀⟩ / ‖row₀‖²`, is at most `κ |det Q| / ‖row₀‖`; here
`‖row₀‖² = Q₀₀² + Q₀₁²`. -/
theorem tilted_box_of_frame (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) {κ : ℝ} (hw : ‖Matrix.toEuclideanLin Q⁻¹ w‖ ≤ κ)
    (h0 : 0 < Q 0 0 ^ 2 + Q 0 1 ^ 2) :
    |w 0| ≤ κ * Real.sqrt (Q 0 0 ^ 2 + Q 0 1 ^ 2) ∧
      |w 1 - (Q 1 0 * Q 0 0 + Q 1 1 * Q 0 1) / (Q 0 0 ^ 2 + Q 0 1 ^ 2) * w 0| ≤
        κ * Real.sqrt (Q.det ^ 2 / (Q 0 0 ^ 2 + Q 0 1 ^ 2)) := by
  set a := Matrix.toEuclideanLin Q⁻¹ w with ha
  have hκ : 0 ≤ κ := (norm_nonneg _).trans hw
  have hw' : w = Matrix.toEuclideanLin Q a := (toEuclideanLin_inv_cancel Q hQ w).symm
  have hw0 : w 0 = Q 0 0 * a 0 + Q 0 1 * a 1 := by rw [hw', toEuclideanLin_apply_fin2]
  have hw1 : w 1 = Q 1 0 * a 0 + Q 1 1 * a 1 := by rw [hw', toEuclideanLin_apply_fin2]
  have ha2 : a 0 ^ 2 + a 1 ^ 2 ≤ κ ^ 2 := by
    rw [← norm_sq_fin2]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hdet : Q.det = Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 := by
    rw [Matrix.det_fin_two]
  set s := Q 0 0 ^ 2 + Q 0 1 ^ 2 with hs
  constructor
  · apply abs_le_of_sq _ h0.le ha2 hκ
    rw [hw0]
    nlinarith [sq_nonneg (Q 0 0 * a 1 - Q 0 1 * a 0)]
  · apply abs_le_of_sq _ (by positivity) ha2 hκ
    rw [hw0, hw1, hdet]
    have key : (Q 1 0 * a 0 + Q 1 1 * a 1 - (Q 1 0 * Q 0 0 + Q 1 1 * Q 0 1) / s *
        (Q 0 0 * a 0 + Q 0 1 * a 1)) = (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) / s *
        (Q 0 0 * a 1 - Q 0 1 * a 0) := by
      field_simp
      ring
    rw [key, mul_pow, div_pow]
    have hsq : (Q 0 0 * a 1 - Q 0 1 * a 0) ^ 2 ≤ s * (a 0 ^ 2 + a 1 ^ 2) := by
      rw [hs]; nlinarith [sq_nonneg (Q 0 0 * a 0 + Q 0 1 * a 1)]
    have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    calc (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) ^ 2 / s ^ 2 * (Q 0 0 * a 1 - Q 0 1 * a 0) ^ 2
        ≤ (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) ^ 2 / s ^ 2 * (s * (a 0 ^ 2 + a 1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) ^ 2 / s * (a 0 ^ 2 + a 1 ^ 2) := by
          field_simp

/-- Composition of chart frames (paper Prop. 4.11, composing through the parent): a frame `N`
with moving center `cN + t uN` in the normalized coordinates of a parent frame `P` with center
`c + t u` is the frame `P * N` with center `(c + P cN) + t (u + P uN)`. -/
theorem frame_comp_apply (P N : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.det ≠ 0) (hN : N.det ≠ 0)
    (y c u cN uN : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    Matrix.toEuclideanLin (P * N)⁻¹ (y - (c + Matrix.toEuclideanLin P cN) -
        t • (u + Matrix.toEuclideanLin P uN)) =
      Matrix.toEuclideanLin N⁻¹ (Matrix.toEuclideanLin P⁻¹ (y - c - t • u) - cN - t • uN) := by
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  rw [Matrix.mul_inv_rev, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  congr 1
  have hPP : Matrix.toEuclideanLin P⁻¹ (Matrix.toEuclideanLin P cN) = cN := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.nonsing_inv_mul _ hPu]
    simp
  have hPP' : Matrix.toEuclideanLin P⁻¹ (Matrix.toEuclideanLin P uN) = uN := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.nonsing_inv_mul _ hPu]
    simp
  simp only [map_sub, map_add, map_smul, hPP, hPP', smul_add]
  abel

/-- A frame given by the rows of its inverse: if both row functionals of `f` are bounded on
`w`, then so is the norm of `f w` (use with `Q = f⁻¹`, so `Q⁻¹ = f`). -/
theorem norm_le_of_rows (f : Matrix (Fin 2) (Fin 2) ℝ) (w : EuclideanSpace ℝ (Fin 2)) {a b : ℝ}
    (h0 : |f 0 0 * w 0 + f 0 1 * w 1| ≤ a) (h1 : |f 1 0 * w 0 + f 1 1 * w 1| ≤ b) :
    ‖Matrix.toEuclideanLin f w‖ ≤ a + b := by
  have ha : 0 ≤ a := (abs_nonneg _).trans h0
  have hb : 0 ≤ b := (abs_nonneg _).trans h1
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have e0 : (Matrix.toEuclideanLin f w) 0 = f 0 0 * w 0 + f 0 1 * w 1 := by
    simp [Matrix.toLpLin_apply]
  have e1 : (Matrix.toEuclideanLin f w) 1 = f 1 0 * w 0 + f 1 1 * w 1 := by
    simp [Matrix.toLpLin_apply]
  rw [e0, e1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have := abs_le.mp h0
  have := abs_le.mp h1
  nlinarith

/-- Determinant of the inverse. -/
theorem det_inv_fin2 (f : Matrix (Fin 2) (Fin 2) ℝ) : (f⁻¹).det = (f.det)⁻¹ := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-- `(f⁻¹)⁻¹ = f` for an invertible `2 × 2` matrix. -/
theorem inv_inv_of_det_ne_zero (f : Matrix (Fin 2) (Fin 2) ℝ) (hf : f.det ≠ 0) : (f⁻¹)⁻¹ = f :=
  Matrix.nonsing_inv_nonsing_inv f (isUnit_iff_ne_zero.mpr hf)

/-- The inverse of a `2 × 2` matrix through its adjugate. -/
theorem inv_entries_fin2 (f : Matrix (Fin 2) (Fin 2) ℝ) :
    f⁻¹ = (f.det)⁻¹ • !![f 1 1, -f 0 1; -f 1 0, f 0 0] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp [Ring.inverse_eq_inv']

/-- Entry sum of the inverse: `Σ|f⁻¹| = Σ|f| / |det f|`. -/
theorem sum_abs_inv_fin2 (f : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |f⁻¹ e e'|) = (∑ e : Fin 2, ∑ e' : Fin 2, |f e e'|) / |f.det| := by
  rw [inv_entries_fin2]
  simp [Fin.sum_univ_two, abs_mul, abs_inv]
  ring

/-- Entry sums are submultiplicative. -/
theorem sum_abs_mul_fin2 (P N : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |(P * N) e e'|) ≤
      (∑ e : Fin 2, ∑ e' : Fin 2, |P e e'|) * (∑ e : Fin 2, ∑ e' : Fin 2, |N e e'|) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h := fun a b c d : ℝ => abs_add_le (a * b) (c * d)
  nlinarith [h (P 0 0) (N 0 0) (P 0 1) (N 1 0), h (P 0 0) (N 0 1) (P 0 1) (N 1 1),
    h (P 1 0) (N 0 0) (P 1 1) (N 1 0), h (P 1 0) (N 0 1) (P 1 1) (N 1 1),
    abs_mul (P 0 0) (N 0 0), abs_mul (P 0 1) (N 1 0), abs_mul (P 0 0) (N 0 1),
    abs_mul (P 0 1) (N 1 1), abs_mul (P 1 0) (N 0 0), abs_mul (P 1 1) (N 1 0),
    abs_mul (P 1 0) (N 0 1), abs_mul (P 1 1) (N 1 1),
    abs_nonneg (P 0 0), abs_nonneg (P 0 1), abs_nonneg (P 1 0), abs_nonneg (P 1 1),
    abs_nonneg (N 0 0), abs_nonneg (N 0 1), abs_nonneg (N 1 0), abs_nonneg (N 1 1)]

end Submission.Obl.k4_finite_narrowness_path_improvement
