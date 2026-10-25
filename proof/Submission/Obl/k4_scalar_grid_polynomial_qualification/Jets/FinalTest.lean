import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.NodeStep

set_option autoImplicit false

/-!
# Testing the root polynomial at a separate time (paper, proof of `prop:higher-jets`)

At the root `u` the rows `R 0 = F u, R 1, …, R M` define the Taylor polynomial `rowPoly R M u`.
If at a time `t'` near `u` the row misses this polynomial by `θ`, then
`S(t') + (F t' - P(t')) y(t')` is determined by the root jets, hence by the scalar bin at `u`; the
scalar support at `t'` (`SS`) then determines `y(u)` up to `≈ K r^{-d}` candidates at precision
`≈ r`, and the projection estimate makes the trajectories labelled at `t'` light.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- **The tangential coordinate from a scalar cover at another time.**  If `X = S(t') + e y(t')`
is determined by the scalar bin at `u`, the scalar at `t'` has the `SS` cover at radius `|e| r`,
and `y(u)` is within `h K` of `y(t')`, then `y(u)` is determined by the scalar bin at `u`. -/
theorem ydet_of_Xdet {ν : Measure Λ} {c : Λ → Fin 5 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    {D : Set Λ} {u t' q δX e r h : ℝ} {nX : ℕ} (he : e ≠ 0) (hr : 0 < r) (hr1 : r ≤ 1)
    (hζr : ζ ≤ |e| * r) (hδX : 0 ≤ δX) (X : Λ → ℝ)
    (hX : Determined E (fun l => zS F (c l) u) D u q X δX nX)
    (hlab : ∀ l ∈ D, (l, u) ∈ E → (l, t') ∈ E)
    (hid : ∀ l ∈ D, (l, u) ∈ E → X l = zS F (c l) t' + e * zy (c l) t')
    (hyy : ∀ l ∈ D, (l, u) ∈ E → |zy (c l) u - zy (c l) t'| ≤ h * K)
    (hyb : ∀ l ∈ D, (l, u) ∈ E → |zy (c l) t'| ≤ 2 * K) :
    Determined E (fun l => zS F (c l) u) D u q (fun l => zy (c l) u)
      (δX / |e| + r + h * K) (nX * ⌊K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d⌋₊) := by
  classical
  have hK := hSN.one_le_K
  have hepos : 0 < |e| := abs_pos.mpr he
  obtain ⟨Y, hY, hmem⟩ := hX
  -- the covers at time `t'`
  have hcov : ∀ x₀ : ℝ, ∃ (m : ℕ) (z : Fin m → ℝ),
      {s | ∃ l, (l, t') ∈ E ∧ zS F (c l) t' = s} ∩
        Icc (x₀ - (2 * K * |e| + δX)) (x₀ - (2 * K * |e| + δX) + (4 * K * |e| + 2 * δX)) ⊆
        ⋃ k, Metric.closedBall (z k) (|e| * r) ∧
      (m : ℝ) ≤ K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d := by
    intro x₀
    exact hSN.support t' (|e| * r) (4 * K * |e| + 2 * δX) (x₀ - (2 * K * |e| + δX)) hζr
      (by nlinarith [mul_le_mul_of_nonneg_left hr1 hepos.le])
  choose mm zz hzz hmm using hcov
  let cand : ℝ → Finset ℝ := fun x₀ => Finset.univ.image (fun k : Fin (mm x₀) => (x₀ - zz x₀ k) / e)
  refine ⟨fun σ => (Y σ).biUnion cand, fun σ => ?_, fun l hl hlu => ?_⟩
  · calc _ ≤ ∑ x₀ ∈ Y σ, (cand x₀).card := Finset.card_biUnion_le
      _ ≤ ∑ _x₀ ∈ Y σ, ⌊K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d⌋₊ :=
          Finset.sum_le_sum fun x₀ _ => by
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            exact Nat.le_floor (hmm x₀)
      _ = (Y σ).card * ⌊K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d⌋₊ := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ nX * ⌊K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d⌋₊ :=
          Nat.mul_le_mul_right _ (hY σ)
  · obtain ⟨x₀, hx₀, hdx⟩ := hmem l hl hlu
    have hlt' := hlab l hl hlu
    have hX' := hid l hl hlu
    have hyt := hyb l hl hlu
    -- the scalar at `t'` is in the tested interval
    have hS : zS F (c l) t' ∈ Icc (x₀ - (2 * K * |e| + δX))
        (x₀ - (2 * K * |e| + δX) + (4 * K * |e| + 2 * δX)) := by
      have h1 : |e * zy (c l) t'| ≤ 2 * K * |e| := by
        rw [abs_mul]; nlinarith [abs_nonneg e]
      rw [abs_le] at hdx h1
      constructor <;> linarith
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hzz x₀ ⟨⟨l, hlt', rfl⟩, hS⟩)
    rw [Metric.mem_closedBall, Real.dist_eq] at hk
    refine ⟨(x₀ - zz x₀ k) / e, Finset.mem_biUnion.mpr ⟨x₀, hx₀, Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩⟩, ?_⟩
    have hyt' : zy (c l) t' = (X l - zS F (c l) t') / e := by
      rw [hX']; field_simp; ring
    have key : |zy (c l) t' - (x₀ - zz x₀ k) / e| ≤ δX / |e| + r := by
      rw [hyt', ← sub_div, abs_div]
      rw [div_le_iff₀ hepos]
      have : X l - zS F (c l) t' - (x₀ - zz x₀ k) = (X l - x₀) - (zS F (c l) t' - zz x₀ k) := by
        ring
      rw [this]
      calc |(X l - x₀) - (zS F (c l) t' - zz x₀ k)| ≤ |X l - x₀| + |zS F (c l) t' - zz x₀ k| :=
            abs_sub _ _
        _ ≤ δX + |e| * r := add_le_add hdx hk
        _ = (δX / |e| + r) * |e| := by field_simp
    calc |zy (c l) u - (x₀ - zz x₀ k) / e|
        ≤ |zy (c l) u - zy (c l) t'| + |zy (c l) t' - (x₀ - zz x₀ k) / e| := abs_sub_le _ _ _
      _ ≤ h * K + (δX / |e| + r) := add_le_add (hyy l hl hlu) key
      _ = δX / |e| + r + h * K := by ring

/-- The root polynomial. -/
def rowPolynomial (R : ℕ → ℝ) (M : ℕ) (u : ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i

theorem rowPolynomial_eval (R : ℕ → ℝ) (M : ℕ) (u v : ℝ) :
    (rowPolynomial R M u).eval v = rowPoly R M u v := by
  simp only [rowPolynomial, rowPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem rowPolynomial_natDegree_le (R : ℕ → ℝ) (M : ℕ) (u : ℝ) :
    (rowPolynomial R M u).natDegree ≤ M := by
  unfold rowPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : (Polynomial.X - Polynomial.C u).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_sub_C]
  calc i * (Polynomial.X - Polynomial.C u).natDegree ≤ i * 1 := Nat.mul_le_mul_left _ this
    _ ≤ M := by omega

theorem abs_coeff_X_sub_C_pow_le {u : ℝ} (hu : |u| ≤ 1) (i k : ℕ) :
    |((Polynomial.X - Polynomial.C u) ^ i).coeff k| ≤ 2 ^ i := by
  induction i generalizing k with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | succ i ih =>
    rw [pow_succ, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_C]
    cases k with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, zero_sub, abs_neg, abs_mul]
      calc |((Polynomial.X - Polynomial.C u) ^ i).coeff 0| * |u| ≤ 2 ^ i * 1 :=
            mul_le_mul (ih 0) hu (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ (i + 1) := by rw [pow_succ]; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) i]
    | succ k =>
      rw [Polynomial.coeff_mul_X]
      calc |((Polynomial.X - Polynomial.C u) ^ i).coeff k -
            ((Polynomial.X - Polynomial.C u) ^ i).coeff (k + 1) * u|
          ≤ |((Polynomial.X - Polynomial.C u) ^ i).coeff k| +
              |((Polynomial.X - Polynomial.C u) ^ i).coeff (k + 1)| * |u| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ 2 ^ i + 2 ^ i * 1 := add_le_add (ih k) (mul_le_mul (ih (k + 1)) hu (abs_nonneg _)
            (by positivity))
        _ = 2 ^ (i + 1) := by rw [pow_succ]; ring

theorem abs_coeff_rowPolynomial_le {R : ℕ → ℝ} {BR : ℝ} (hR : ∀ i, |R i| ≤ BR) (M : ℕ) {u : ℝ}
    (hu : |u| ≤ 1) (k : ℕ) : |(rowPolynomial R M u).coeff k| ≤ (M + 1) * (BR * 2 ^ M) := by
  have hBR : 0 ≤ BR := le_trans (abs_nonneg _) (hR 0)
  have hterm : ∀ i ∈ Finset.range (M + 1),
      |(Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i).coeff k| ≤
        BR * 2 ^ M := by
    intro i hi
    have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_C_mul, abs_mul, abs_div, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos i)
    have h1 : |R i| / (i.factorial : ℝ) ≤ BR := (div_le_self (abs_nonneg _) hf).trans (hR i)
    have h2 := abs_coeff_X_sub_C_pow_le hu i k
    have h3 : (2 : ℝ) ^ i ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hi'
    calc |R i| / (i.factorial : ℝ) * |((Polynomial.X - Polynomial.C u) ^ i).coeff k|
        ≤ BR * 2 ^ i := mul_le_mul h1 h2 (abs_nonneg _) hBR
      _ ≤ BR * 2 ^ M := mul_le_mul_of_nonneg_left h3 hBR
  have e : (rowPolynomial R M u).coeff k = ∑ i ∈ Finset.range (M + 1),
      (Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i).coeff k := by
    simp only [rowPolynomial, Polynomial.finsetSum_coeff]
  rw [e]
  calc |∑ i ∈ Finset.range (M + 1),
        (Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i).coeff k|
      ≤ ∑ i ∈ Finset.range (M + 1),
          |(Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i).coeff k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (M + 1), BR * 2 ^ M := Finset.sum_le_sum hterm
    _ = (M + 1) * (BR * 2 ^ M) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **The final test.**  If the row misses the root polynomial at `t'` by `θ`, the trajectories of
`D` labelled at `t'` carry little prior mass. -/
theorem final_test {ν : Measure Λ} {c : Λ → Fin 5 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) {D : Set Λ} {u t' p δ h θ r : ℝ} {M : ℕ} (hM : 2 ≤ M)
    {R : ℕ → ℝ} {BR : ℝ} {nL : ℕ} (hR0 : R 0 = F u) (hRb : ∀ i, |R i| ≤ BR)
    (hlab : ∀ l ∈ D, (l, u) ∈ E) (hL : NodeLists E F c D u R M p δ nL) (hδp : p ≤ δ)
    (hζp : ζ ≤ p) (hp1 : p ≤ 1) (htu : |t' - u| ≤ h) (hh1 : h ≤ 1)
    (hθ : θ ≤ |F t' - rowPoly R M u t'|) (hθ0 : 0 < θ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hζr : ζ ≤ θ * r) (herr : (M + 1) * δ + K * BR * h ^ (M + 1) ≤ θ * r) :
    ν {l | l ∈ D ∧ (l, t') ∈ E} ≤ ENNReal.ofReal (400 * K ^ 5 *
      ((nL ^ M * ⌊K * ((4 * K + 2) / r) ^ d⌋₊ : ℕ) : ℝ) * (2 * r + h * K + p)) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hp : 0 < p := lt_of_lt_of_le hSN.zeta_pos hζp
  have hBR : 0 ≤ BR := le_trans (abs_nonneg _) (hRb 0)
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) htu
  set e := F t' - rowPoly R M u t' with he_def
  have he : 0 < |e| := lt_of_lt_of_le hθ0 hθ
  have he0 : e ≠ 0 := abs_pos.mp he
  set D' := {l | l ∈ D ∧ (l, t') ∈ E}
  set X : Λ → ℝ := fun l => ∑ i ∈ Finset.range (M + 1),
      (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i - c l 4 * R M * (t' - u) ^ (M + 1) /
        (M.factorial : ℝ)
  -- the root jets determine `X`
  have hpow : ∀ i : ℕ, |(t' - u) ^ i / (i.factorial : ℝ)| ≤ 1 := by
    intro i
    rw [abs_div, abs_pow, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos i)
    have : |t' - u| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) (htu.trans hh1)
    calc |t' - u| ^ i / (i.factorial : ℝ) ≤ 1 / 1 := div_le_div₀ (by norm_num) this one_pos hf
      _ = 1 := by norm_num
  have hδ0 : 0 ≤ δ := le_trans hp.le hδp
  have hterms : ∀ i ∈ Finset.range (M + 1), Determined E (fun l => zS F (c l) u) D' u p
      (fun l => (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i) δ (if i = 0 then 1 else nL) := by
    intro i hi
    have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hdet : Determined E (fun l => zS F (c l) u) D' u p (fun l => jet R (c l) u i) δ
        (if i = 0 then 1 else nL) := by
      by_cases h0 : i = 0
      · subst h0
        simp only [if_true]
        refine ((Determined.self hp).mono hδp le_rfl).congr fun l _ _ => ?_
        exact (jet_zero hR0).symm
      · simp only [h0, if_false]
        exact (hL i (Nat.one_le_iff_ne_zero.mpr h0) hi').mono_set fun l hl => hl.1
    exact (hdet.const_mul _).mono (by
      calc |(t' - u) ^ i / (i.factorial : ℝ)| * δ ≤ 1 * δ :=
            mul_le_mul_of_nonneg_right (hpow i) hδ0
        _ = δ := one_mul δ) le_rfl
  have hsum := Determined.sum (Finset.range (M + 1)) _ (fun _ => δ) _ hterms
  have hprod : ∏ i ∈ Finset.range (M + 1), (if i = 0 then 1 else nL) = nL ^ M := by
    rw [Finset.prod_range_succ']
    simp only [Nat.succ_ne_zero, if_false, if_true, mul_one, Finset.prod_const, Finset.card_range]
  rw [hprod] at hsum
  have hXdet : Determined E (fun l => zS F (c l) u) D' u p X ((M + 1) * δ + K * BR * h ^ (M + 1))
      (nL ^ M) := by
    have := hsum.perturb (Ψ := X) (ε := K * BR * h ^ (M + 1)) (fun l hl hlu => ?_)
    · refine this.mono (le_of_eq ?_) le_rfl
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    · have hlt' := hl.2
      have hc : ∀ e, |c l e| ≤ K := hSN.coeff_le _ hlt'
      simp only [X]
      rw [show (∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i -
          c l 4 * R M * (t' - u) ^ (M + 1) / (M.factorial : ℝ)) -
          ∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i =
          -(c l 4 * R M * (t' - u) ^ (M + 1) / (M.factorial : ℝ)) by ring, abs_neg]
      rw [abs_div, Nat.abs_cast, abs_mul, abs_mul, abs_pow]
      have hf : (1 : ℝ) ≤ (M.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos M)
      have hpw : |t' - u| ^ (M + 1) ≤ h ^ (M + 1) := pow_le_pow_left₀ (abs_nonneg _) htu _
      calc |c l 4| * |R M| * |t' - u| ^ (M + 1) / (M.factorial : ℝ)
          ≤ |c l 4| * |R M| * |t' - u| ^ (M + 1) / 1 := by
            apply div_le_div_of_nonneg_left (by positivity) one_pos hf
        _ ≤ K * BR * h ^ (M + 1) := by
            rw [div_one]
            gcongr
            · exact hc 4
            · exact hRb M
  -- the identity
  have hid : ∀ l ∈ D', (l, u) ∈ E → X l = zS F (c l) t' + e * zy (c l) t' := by
    intro l _ _
    have := zS_eq_taylor (F := F) (R := R) (c := c l) (u := u) (v := t') hM
    simp only [X, he_def]
    have hsum_eq : ∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i =
        ∑ i ∈ Finset.range (M + 1), jet R (c l) u i * (t' - u) ^ i / (i.factorial : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [hsum_eq]
    linarith
  have hδX : 0 ≤ (M + 1) * δ + K * BR * h ^ (M + 1) := by positivity
  have hY := ydet_of_Xdet hSN (D := D') (u := u) (t' := t') (h := h) he0 hr0 hr1
    (hζr.trans (by gcongr)) hδX X hXdet (fun l hl _ => hl.2) hid
    (fun l hl hlu => by
      have hc : ∀ e, |c l e| ≤ K := hSN.coeff_le _ hlu
      simp only [zy]
      rw [show c l 3 + c l 4 * u - (c l 3 + c l 4 * t') = c l 4 * (u - t') by ring, abs_mul,
        abs_sub_comm]
      calc |c l 4| * |t' - u| ≤ K * h := mul_le_mul (hc 4) htu (abs_nonneg _) hK0
        _ = h * K := by ring)
    (fun l hl _ => abs_zy_le (hSN.coeff_le _ hl.2) (hSN.time_mem _ hl.2))
  -- precision and count
  set δX := (M + 1) * δ + K * BR * h ^ (M + 1)
  have hδXr : δX ≤ |e| * r := herr.trans (mul_le_mul_of_nonneg_right hθ hr0.le)
  have hprec : δX / |e| + r + h * K ≤ 2 * r + h * K := by
    have : δX / |e| ≤ r := by rw [div_le_iff₀ he]; linarith
    linarith
  have hcount : ⌊K * ((4 * K * |e| + 2 * δX) / (|e| * r)) ^ d⌋₊ ≤ ⌊K * ((4 * K + 2) / r) ^ d⌋₊ := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ hK0
    apply Real.rpow_le_rpow (by positivity) _ hd0
    rw [div_le_div_iff₀ (by positivity) hr0]
    have : δX ≤ |e| := hδXr.trans (by nlinarith)
    nlinarith
  have hY' := hY.mono hprec (Nat.mul_le_mul_left _ hcount)
  have hmass := Determined.mass_le hSN hd1 hζp hp1 (by positivity) hY'
  refine (measure_mono ?_).trans (hmass.trans (le_of_eq ?_))
  · intro l hl
    exact ⟨hl, hlab l hl.1⟩
  · congr 1

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
