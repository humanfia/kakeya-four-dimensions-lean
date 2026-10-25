import Mathlib
import Submission.Obl.k4_tempered_grid_selection.Interface

/-!
# Polynomial format of a common-label selection

For a tempered problem `TemperedProblem n M D K ν E` and an arbitrary set `T` of common
labels, the selection `E ∩ commonLabel n H R U ⁻¹' T` is again a tempered problem, with
the enlarged exponent `M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7` and degree `max D 2` (both independent
of `n` and `T`), for every `K' ≥ K` whose inverse the selected mass dominates.

On the coefficient/time box of `E`, each of the six common-label floors takes at most
`2L+1` integer values, `L` polynomial in `n`.  The threshold atoms `ℓ ≤ φⱼ(x)` (of degree
at most two) at the `2L+2` levels determine all six floors there, so membership of the
label in `T` is a Boolean function of these atoms; they are appended to the fiber
description of `E`.
-/

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal

namespace Format

/-- A sign-condition description indexed by a finite type can be reindexed by
`Fin (Fintype.card ι)`. -/
theorem descr_reindex {d D : ℕ} {S : Set (Fin d → ℝ)} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin d) ℝ) (hp : ∀ i, (p i).totalDegree ≤ D)
    (b : (ι → Bool) → Bool)
    (hb : ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true) :
    ∃ p₀ : Fin (Fintype.card ι) → MvPolynomial (Fin d) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧
      ∃ b₀ : (Fin (Fintype.card ι) → Bool) → Bool, ∀ x₀, x₀ ∈ S ↔
        b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true := by
  let e := Fintype.equivFin ι
  refine ⟨fun i₀ => p (e.symm i₀), fun i₀ => hp _, fun bits => b (fun i => bits (e i)), ?_⟩
  intro x
  simpa only [Equiv.symm_apply_apply] using hb x

/-- The point of the incidence space with index `i` and fiber coordinates `x`
(`x 6` is the time). -/
def fiberPt (i : ℕ) (x : Fin 7 → ℝ) : Incidence :=
  ((i, fun j₁ : Fin 6 => x j₁.castSucc), x 6)

/-- The six real quantities whose floors form the common label, as polynomials in the
fiber coordinates. -/
noncomputable def labelPoly (n : ℝ) (H : ℕ) (R U : ℝ) : Fin 6 → MvPolynomial (Fin 7) ℝ :=
  ![MvPolynomial.C (n ^ H) * MvPolynomial.X 6,
    MvPolynomial.C (n ^ H) * (MvPolynomial.X 0 + MvPolynomial.X 6 * MvPolynomial.X 3),
    MvPolynomial.C (n ^ H) * (MvPolynomial.X 1 + MvPolynomial.X 6 * MvPolynomial.X 4),
    MvPolynomial.C (width n R)⁻¹ * (MvPolynomial.X 2 + MvPolynomial.X 6 * MvPolynomial.X 5),
    MvPolynomial.C (width n U)⁻¹ * MvPolynomial.X 3,
    MvPolynomial.C (width n U)⁻¹ * MvPolynomial.X 4]

theorem commonLabel_fiberPt (n : ℝ) (H : ℕ) (R U : ℝ) (i : ℕ) (x : Fin 7 → ℝ) (j : Fin 6) :
    commonLabel n H R U (fiberPt i x) j = ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ := by
  fin_cases j <;>
    simp [commonLabel, labelPoly, fiberPt, div_eq_inv_mul]

private theorem deg_C_mul_X (a : ℝ) (i : Fin 7) :
    (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp

private theorem deg_C_mul_add (a : ℝ) (i j k : Fin 7) :
    (MvPolynomial.C a * (MvPolynomial.X i + MvPolynomial.X j * MvPolynomial.X k) :
      MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem labelPoly_totalDegree (n : ℝ) (H : ℕ) (R U : ℝ) (j : Fin 6) :
    (labelPoly n H R U j).totalDegree ≤ 2 := by
  fin_cases j
  · exact deg_C_mul_X _ _
  · exact deg_C_mul_add _ _ _ _
  · exact deg_C_mul_add _ _ _ _
  · exact deg_C_mul_add _ _ _ _
  · exact deg_C_mul_X _ _
  · exact deg_C_mul_X _ _

/-- The coefficient/time box of a tempered fiber. -/
def InBox (n : ℝ) (M : ℕ) (x : Fin 7 → ℝ) : Prop :=
  x 6 ∈ Icc (0 : ℝ) 1 ∧ ∀ e : Fin 6, |x e.castSucc| ≤ n ^ M

/-- A common bound for the coefficients of the label polynomials. -/
noncomputable def labelScale (n : ℝ) (H : ℕ) (R U : ℝ) : ℝ :=
  n ^ H + (width n R)⁻¹ + (width n U)⁻¹

theorem width_pos (n r : ℝ) : 0 < width n r := by
  unfold width
  positivity

private theorem abs_mul_le_scale {a S y B : ℝ} (ha : 0 ≤ a) (haS : a ≤ S) (hy : |y| ≤ 2 * B) :
    |a * y| ≤ 2 * S * B := by
  rw [abs_mul, abs_of_nonneg ha]
  have hB : 0 ≤ B := by linarith [abs_nonneg y]
  calc a * |y| ≤ S * (2 * B) := mul_le_mul haS hy (abs_nonneg _) (ha.trans haS)
    _ = 2 * S * B := by ring

theorem abs_eval_labelPoly_le {n : ℝ} (hn : 1 ≤ n) {M H : ℕ} {R U : ℝ} {x : Fin 7 → ℝ}
    (hx : InBox n M x) (j : Fin 6) :
    |MvPolynomial.eval x (labelPoly n H R U j)| ≤ 2 * labelScale n H R U * n ^ M := by
  obtain ⟨⟨ht0, ht1⟩, hb⟩ := hx
  have hpM : 1 ≤ n ^ M := one_le_pow₀ hn
  have h0 : |x 0| ≤ n ^ M := hb 0
  have h1 : |x 1| ≤ n ^ M := hb 1
  have h2 : |x 2| ≤ n ^ M := hb 2
  have h3 : |x 3| ≤ n ^ M := hb 3
  have h4 : |x 4| ≤ n ^ M := hb 4
  have h5 : |x 5| ≤ n ^ M := hb 5
  have h6 : |x 6| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hH : 0 ≤ n ^ H := by positivity
  have hR : 0 ≤ (width n R)⁻¹ := (inv_pos.mpr (width_pos n R)).le
  have hU : 0 ≤ (width n U)⁻¹ := (inv_pos.mpr (width_pos n U)).le
  have hHS : n ^ H ≤ labelScale n H R U := by unfold labelScale; linarith
  have hRS : (width n R)⁻¹ ≤ labelScale n H R U := by unfold labelScale; linarith
  have hUS : (width n U)⁻¹ ≤ labelScale n H R U := by unfold labelScale; linarith
  have hsum : ∀ a b : Fin 7, |x a| ≤ n ^ M → |x b| ≤ n ^ M →
      |x a + x 6 * x b| ≤ 2 * n ^ M := by
    intro a b ha hb'
    calc |x a + x 6 * x b| ≤ |x a| + |x 6 * x b| := abs_add_le _ _
      _ = |x a| + |x 6| * |x b| := by rw [abs_mul]
      _ ≤ n ^ M + 1 * n ^ M := by gcongr
      _ = 2 * n ^ M := by ring
  fin_cases j <;> simp only [labelPoly, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_add,
    MvPolynomial.eval_X]
  · exact abs_mul_le_scale hH hHS (by linarith)
  · exact abs_mul_le_scale hH hHS (hsum 0 3 h0 h3)
  · exact abs_mul_le_scale hH hHS (hsum 1 4 h1 h4)
  · exact abs_mul_le_scale hR hRS (hsum 2 5 h2 h5)
  · exact abs_mul_le_scale hU hUS (by linarith)
  · exact abs_mul_le_scale hU hUS (by linarith)

/-- The number of nonnegative integer levels used on each side. -/
noncomputable def lev (n : ℝ) (M H : ℕ) (R U : ℝ) : ℕ :=
  ⌈2 * labelScale n H R U * n ^ M⌉₊

/-- The threshold atoms: `ℓ ≤ φⱼ(x)` for the levels `ℓ = w - lev`, `w < 2 lev + 2`. -/
noncomputable def atom (n : ℝ) (M H : ℕ) (R U : ℝ)
    (a : Fin 6 × Fin (2 * lev n M H R U + 2)) : MvPolynomial (Fin 7) ℝ :=
  labelPoly n H R U a.1 - MvPolynomial.C (((a.2 : ℕ) : ℝ) - (lev n M H R U : ℝ))

theorem atom_totalDegree (n : ℝ) (M H : ℕ) (R U : ℝ)
    (a : Fin 6 × Fin (2 * lev n M H R U + 2)) : (atom n M H R U a).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (labelPoly_totalDegree _ _ _ _ _) ?_)
  rw [MvPolynomial.totalDegree_C]
  exact Nat.zero_le _

theorem eval_atom_nonneg_iff (n : ℝ) (M H : ℕ) (R U : ℝ) (x : Fin 7 → ℝ)
    (a : Fin 6 × Fin (2 * lev n M H R U + 2)) :
    0 ≤ MvPolynomial.eval x (atom n M H R U a) ↔
      ((((a.2 : ℕ) : ℤ) - (lev n M H R U : ℤ) : ℤ) : ℝ) ≤
        MvPolynomial.eval x (labelPoly n H R U a.1) := by
  simp only [atom, MvPolynomial.eval_sub, MvPolynomial.eval_C, sub_nonneg]
  push_cast
  rfl

/-- On the box, membership of the common label in an arbitrary set `T` is a Boolean
function of the threshold atoms. -/
theorem label_mem_iff_atoms {n : ℝ} (hn : 1 ≤ n) (M H : ℕ) (R U : ℝ) (T : Set Label)
    (i : ℕ) :
    ∃ Φ : (Fin 6 × Fin (2 * lev n M H R U + 2) → Bool) → Bool, ∀ x, InBox n M x →
      (commonLabel n H R U (fiberPt i x) ∈ T ↔
        Φ (fun a => decide (0 ≤ MvPolynomial.eval x (atom n M H R U a))) = true) := by
  classical
  refine ⟨fun bits => decide (∃ v ∈ T, ∀ j : Fin 6, ∃ w w' : Fin (2 * lev n M H R U + 2),
    ((w : ℕ) : ℤ) - (lev n M H R U : ℤ) = v j ∧
      ((w' : ℕ) : ℤ) - (lev n M H R U : ℤ) = v j + 1 ∧
      bits (j, w) = true ∧ bits (j, w') = false), ?_⟩
  intro x hx
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro hT
    refine ⟨_, hT, fun j => ?_⟩
    have hlab : commonLabel n H R U (fiberPt i x) j =
        ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ := commonLabel_fiberPt _ _ _ _ _ _ _
    have habs := abs_eval_labelPoly_le hn hx j (H := H) (R := R) (U := U)
    have hLr : 2 * labelScale n H R U * n ^ M ≤ (lev n M H R U : ℝ) := Nat.le_ceil _
    have hlo : -(lev n M H R U : ℤ) ≤ ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith [neg_abs_le (MvPolynomial.eval x (labelPoly n H R U j))]
    have hhi : ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ ≤ (lev n M H R U : ℤ) := by
      rw [Int.floor_le_iff]
      push_cast
      linarith [le_abs_self (MvPolynomial.eval x (labelPoly n H R U j))]
    have hw : (⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ + lev n M H R U).toNat <
        2 * lev n M H R U + 2 := by omega
    have hw' : (⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ + lev n M H R U + 1).toNat <
        2 * lev n M H R U + 2 := by omega
    have e1 : (((⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ + lev n M H R U).toNat : ℕ) : ℤ)
        - (lev n M H R U : ℤ) = ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ := by omega
    have e2 : (((⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ + lev n M H R U + 1).toNat : ℕ) : ℤ)
        - (lev n M H R U : ℤ) = ⌊MvPolynomial.eval x (labelPoly n H R U j)⌋ + 1 := by omega
    refine ⟨⟨_, hw⟩, ⟨_, hw'⟩, ?_, ?_, ?_, ?_⟩
    · rw [hlab]; exact e1
    · rw [hlab]; exact e2
    · rw [eval_atom_nonneg_iff]
      simp only
      rw [e1]
      exact Int.floor_le _
    · rw [eval_atom_nonneg_iff]
      simp only
      rw [e2, not_le]
      push_cast
      exact Int.lt_floor_add_one _
  · rintro ⟨v, hv, hj⟩
    convert hv using 1
    funext j
    obtain ⟨w, w', hw, hw', h1, h2⟩ := hj j
    rw [eval_atom_nonneg_iff] at h1 h2
    rw [hw] at h1
    rw [hw', not_le] at h2
    rw [commonLabel_fiberPt, Int.floor_eq_iff]
    push_cast at h2
    exact ⟨h1, h2⟩

/-- `2^⌊r log n / log 2⌋ ≤ n^⌈|r|⌉₊` for `n ≥ 1`. -/
theorem inv_width_le {n : ℝ} (hn : 1 ≤ n) (r : ℝ) : (width n r)⁻¹ ≤ n ^ ⌈|r|⌉₊ := by
  have hn0 : 0 < n := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set m : ℤ := ⌊r * Real.log n / Real.log 2⌋ with hm
  have hw : (width n r)⁻¹ = (2 : ℝ) ^ m := by
    unfold width
    rw [zpow_neg, inv_inv]
  rw [hw, ← Real.rpow_intCast, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  have h1 : (m : ℝ) ≤ r * Real.log n / Real.log 2 := Int.floor_le _
  have h2 : (m : ℝ) * Real.log 2 ≤ r * Real.log n := (le_div_iff₀ hlog2).mp h1
  have h3 : r * Real.log n ≤ |r| * Real.log n :=
    mul_le_mul_of_nonneg_right (le_abs_self r) hlogn
  have h4 : |r| * Real.log n ≤ (⌈|r|⌉₊ : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlogn
  linarith

/-- The total number of atoms is polynomial in `n`, with an exponent independent of `n`. -/
theorem count_le {n : ℝ} (hn : 2 ≤ n) (M H : ℕ) (R U : ℝ) :
    n ^ M + ((6 * (2 * lev n M H R U + 2) : ℕ) : ℝ) ≤
      n ^ (M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7) := by
  have hn1 : 1 ≤ n := by linarith
  set Q := H + ⌈|R|⌉₊ + ⌈|U|⌉₊ with hQ
  have hpQ : ∀ e ≤ Q, n ^ e ≤ n ^ Q := fun e he => pow_le_pow_right₀ hn1 he
  have hS : labelScale n H R U ≤ 3 * n ^ Q := by
    unfold labelScale
    have a1 := hpQ H (by omega)
    have a2 := (inv_width_le hn1 R).trans (hpQ _ (by omega))
    have a3 := (inv_width_le hn1 U).trans (hpQ _ (by omega))
    linarith
  have hpM : 1 ≤ n ^ M := one_le_pow₀ hn1
  have hpQ1 : 1 ≤ n ^ Q := one_le_pow₀ hn1
  have hL : (lev n M H R U : ℝ) ≤ 2 * labelScale n H R U * n ^ M + 1 := by
    unfold lev
    have h0 : 0 ≤ 2 * labelScale n H R U * n ^ M := by
      unfold labelScale
      have := width_pos n R
      have := width_pos n U
      positivity
    exact (Nat.ceil_lt_add_one h0).le
  have h7 : (2 : ℝ) ^ 7 ≤ n ^ 7 := pow_le_pow_left₀ (by norm_num) hn 7
  have hsplit : n ^ (M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7) = n ^ M * n ^ Q * n ^ 7 := by
    rw [hQ, ← pow_add, ← pow_add]
    ring_nf
  rw [hsplit]
  push_cast
  have hMQ : n ^ M * (3 * n ^ Q) = 3 * (n ^ M * n ^ Q) := by ring
  have hprod : 1 ≤ n ^ M * n ^ Q := one_le_mul_of_one_le_of_one_le hpM hpQ1
  have hmono : labelScale n H R U * n ^ M ≤ 3 * (n ^ M * n ^ Q) := by
    rw [← hMQ, mul_comm (labelScale n H R U)]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  nlinarith

/-- The fiber description of a label selection. -/
theorem fiber_descr_select {n : ℝ} (hn : 2 ≤ n) {M D : ℕ} {E : Set Incidence} (H : ℕ)
    (R U : ℝ) (T : Set Label) (i : ℕ)
    (hbox : ∀ x, fiberPt i x ∈ E → InBox n M x)
    (hE : ∃ m₀ : ℕ, (m₀ : ℝ) ≤ (n ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ,
      (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀,
        x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E}) ↔
          b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) :
    ∃ m₀ : ℕ, (m₀ : ℝ) ≤ (n ^ (M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7)) ∧
      ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ,
      (∀ i₀, (p₀ i₀).totalDegree ≤ max D 2) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀,
        x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈
          E ∩ commonLabel n H R U ⁻¹' T}) ↔
          b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true := by
  have hn1 : 1 ≤ n := by linarith
  obtain ⟨m₀, hm₀, p₀, hp₀, b₀, hb₀⟩ := hE
  obtain ⟨Φ, hΦ⟩ := label_mem_iff_atoms hn1 M H R U T i
  let ι := Fin m₀ ⊕ (Fin 6 × Fin (2 * lev n M H R U + 2))
  let p : ι → MvPolynomial (Fin 7) ℝ := Sum.elim p₀ (atom n M H R U)
  have hp : ∀ a, (p a).totalDegree ≤ max D 2 := by
    rintro (a | a)
    · exact (hp₀ a).trans (le_max_left _ _)
    · exact (atom_totalDegree _ _ _ _ _ a).trans (le_max_right _ _)
  let b : (ι → Bool) → Bool := fun bits =>
    b₀ (fun i₀ => bits (Sum.inl i₀)) && Φ (fun a => bits (Sum.inr a))
  have hb : ∀ x, x ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈
      E ∩ commonLabel n H R U ⁻¹' T}) ↔
      b (fun a => decide (0 ≤ MvPolynomial.eval x (p a))) = true := by
    intro x
    have hb_eq : b (fun a => decide (0 ≤ MvPolynomial.eval x (p a))) =
        (b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x (p₀ i₀))) &&
          Φ (fun a => decide (0 ≤ MvPolynomial.eval x (atom n M H R U a)))) := rfl
    rw [hb_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨hE, hT⟩
      have hE' : fiberPt i x ∈ E := hE
      exact ⟨(hb₀ x).1 hE', (hΦ x (hbox x hE')).1 hT⟩
    · rintro ⟨h1, h2⟩
      have hE' : fiberPt i x ∈ E := (hb₀ x).2 h1
      exact ⟨hE', (hΦ x (hbox x hE')).2 h2⟩
  obtain ⟨p', hp', b', hb'⟩ := descr_reindex p hp b hb
  refine ⟨Fintype.card ι, ?_, p', hp', b', hb'⟩
  have hcard : Fintype.card ι = m₀ + 6 * (2 * lev n M H R U + 2) := by
    simp [ι, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [hcard]
  push_cast
  have := count_le hn M H R U
  push_cast at this
  linarith

theorem measurable_commonLabel (n : ℝ) (H : ℕ) (R U : ℝ) :
    Measurable (commonLabel n H R U) := by
  unfold commonLabel
  refine measurable_pi_iff.mpr (fun j => ?_)
  fin_cases j <;> simp <;> fun_prop

end Format

open Format in
/-- **Format preservation.** Selecting an arbitrary set of common labels keeps the tempered
format, with exponents independent of `n` and `T`, for any `K' ≥ K` whose inverse the
selected mass dominates. -/
theorem temperedProblem_select {n : ℝ} (hn : 2 ≤ n) {M D : ℕ} {K K' : ℝ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} {E : Set Incidence} (H : ℕ) (R U : ℝ) (T : Set Label)
    (hP : TemperedProblem n M D K ν E) (hKK : K ≤ K')
    (hmass : ENNReal.ofReal K'⁻¹ ≤
      incidenceMeasure ν (E ∩ commonLabel n H R U ⁻¹' T) univ) :
    TemperedProblem n (M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7) (max D 2) K' ν
      (E ∩ commonLabel n H R U ⁻¹' T) := by
  have hn1 : 1 ≤ n := by linarith
  have hpow : n ^ M ≤ n ^ (M + H + ⌈|R|⌉₊ + ⌈|U|⌉₊ + 7) :=
    pow_le_pow_right₀ hn1 (by omega)
  obtain ⟨hprob, hmix, hmeas, hsub, hbd, hfib, hK, -⟩ := hP
  refine ⟨hprob, ?_, ?_, ?_, ?_, ?_, ?_, hmass⟩
  · obtain ⟨m, hm, c, idx, A, hj, hν⟩ := hmix
    refine ⟨m, hm.trans hpow, c, idx, A, fun j => ?_, hν⟩
    obtain ⟨hc0, hc, hi, ⟨m₀, hm₀, p₀, hp₀, b₀, hb₀⟩, hA⟩ := hj j
    exact ⟨hc0, hc.trans hpow, hi.trans hpow,
      ⟨m₀, hm₀.trans hpow, p₀, fun i₀ => (hp₀ i₀).trans (le_max_left _ _), b₀, hb₀⟩,
      fun x hx b => (hA x hx b).trans hpow⟩
  · exact hmeas.inter (measurable_commonLabel n H R U T.to_countable.measurableSet)
  · exact inter_subset_left.trans hsub
  · intro p hp
    obtain ⟨h1, h2⟩ := hbd p hp.1
    exact ⟨h1.trans hpow, fun e => (h2 e).trans hpow⟩
  · intro i
    refine fiber_descr_select hn H R U T i (fun x hx => ?_) (hfib i)
    refine ⟨(mem_prod.mp (hsub hx)).2, fun e => (hbd _ hx).2 e⟩
  · filter_upwards [hK] with l hl t ht
    exact ⟨(hl t ht).1.trans hKK, (hl t ht).2.trans hKK⟩

/-- **Format preservation along the sequence.** For arbitrary label sets `T k` (`T k = univ`
keeps `E k`), the selections `E k ∩ commonLabel (N k) H R U ⁻¹' T k` satisfy the tempered
format with `K₀` in place of `K`, with exponents uniform in `k`. -/
theorem format_select (N K K₀ : ℕ → ℝ) (ν : ℕ → Measure (ℕ × (Fin 6 → ℝ)))
    (E : ℕ → Set Incidence) (H : ℕ) (R U : ℝ) (T : ℕ → Set Label) (hN : ∀ k, 2 ≤ N k)
    (hF : ∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K k) (ν k) (E k))
    (hK : ∀ k, K k ≤ K₀ k)
    (hmass : ∀ k, ENNReal.ofReal (K₀ k)⁻¹ ≤
      incidenceMeasure (ν k) (E k ∩ commonLabel (N k) H R U ⁻¹' T k) univ) :
    ∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K₀ k) (ν k)
      (E k ∩ commonLabel (N k) H R U ⁻¹' T k) := by
  obtain ⟨M, D, hP⟩ := hF
  exact ⟨_, _, fun k => temperedProblem_select (hN k) H R U (T k) (hP k) (hK k) (hmass k)⟩

end Submission.Obl.k4_tempered_grid_selection
