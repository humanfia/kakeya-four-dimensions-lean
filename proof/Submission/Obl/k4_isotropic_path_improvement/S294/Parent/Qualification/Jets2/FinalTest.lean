-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.FinalTest, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/FinalTest.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/FinalTest.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/FinalTest.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.NodeStep

set_option autoImplicit false

/-!
# Testing the root polynomial at a separate time, version 2 (paper, proof of `prop:higher-jets`)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`,
`Jets/FinalTest.lean` (updated to x0801's `ec0250f0`), for rows in `(ℝ²)^*`.

At the root `u` the rows `R 0 = F u, R 1, …, R M` define the row-valued Taylor polynomial
`rowPoly R M u`.  If at a time `t'` near `u` the row misses this polynomial by `θ` (in sup norm),
then `X = S(t') + e · y(t')`, `e = F t' - P(t')`, is determined by the root jets, hence by the
scalar bin at `u`; the scalar support at `t'` (`SS`) then determines the normalized projection
`ê · y(u)` (`ê = e / e k`, `k` a largest coordinate) up to `≈ K r^{-d}` candidates at precision
`≈ r`, and the slab projection estimate makes the trajectories labelled at `t'` light.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- **The normalized tangential projection from a scalar cover at another time.** -/
theorem projdet_of_Xdet {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d)
    {D : Set Λ} {u t' q δX r h : ℝ} {nX : ℕ} {e : Fin 2 → ℝ} {k : Fin 2}
    (hek : |e k| = ‖e‖) (he : 0 < ‖e‖) (hr : 0 < r) (hr1 : r ≤ 1)
    (hζr : ζ ≤ ‖e‖ * r) (hδX : 0 ≤ δX) (X : Λ → ℝ)
    (hX : Determined E (fun l => zS F (c l) u) D u q X δX nX)
    (hlab : ∀ l ∈ D, (l, u) ∈ E → (l, t') ∈ E)
    (hid : ∀ l ∈ D, (l, u) ∈ E → X l = zS F (c l) t' + e ⬝ᵥ zy (c l) t')
    (hyy : ∀ l ∈ D, (l, u) ∈ E → ‖zy (c l) u - zy (c l) t'‖ ≤ h * K)
    (hyb : ∀ l ∈ D, (l, u) ∈ E → ‖zy (c l) t'‖ ≤ 2 * K) :
    Determined E (fun l => zS F (c l) u) D u q (fun l => ((e k)⁻¹ • e) ⬝ᵥ zy (c l) u)
      (δX / ‖e‖ + r + 2 * (h * K)) (nX * ⌊K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d⌋₊) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hek0 : e k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hek; linarith
  obtain ⟨Y, hY, hmem⟩ := hX
  -- the covers at time `t'`
  have hcov : ∀ x₀ : ℝ, ∃ (m : ℕ) (z : Fin m → ℝ),
      {s | ∃ l, (l, t') ∈ E ∧ zS F (c l) t' = s} ∩
        Icc (x₀ - (4 * K * ‖e‖ + δX)) (x₀ - (4 * K * ‖e‖ + δX) + (8 * K * ‖e‖ + 2 * δX)) ⊆
        ⋃ j, Metric.closedBall (z j) (‖e‖ * r) ∧
      (m : ℝ) ≤ K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d := by
    intro x₀
    exact hSN.support t' (‖e‖ * r) (8 * K * ‖e‖ + 2 * δX) (x₀ - (4 * K * ‖e‖ + δX)) hζr
      (by nlinarith [mul_le_mul_of_nonneg_left hr1 he.le])
  choose mm zz hzz hmm using hcov
  let cand : ℝ → Finset ℝ :=
    fun x₀ => Finset.univ.image (fun j : Fin (mm x₀) => (x₀ - zz x₀ j) / e k)
  refine ⟨fun σ => (Y σ).biUnion cand, fun σ => ?_, fun l hl hlu => ?_⟩
  · calc _ ≤ ∑ x₀ ∈ Y σ, (cand x₀).card := Finset.card_biUnion_le
      _ ≤ ∑ _x₀ ∈ Y σ, ⌊K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d⌋₊ :=
          Finset.sum_le_sum fun x₀ _ => by
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            exact Nat.le_floor (hmm x₀)
      _ = (Y σ).card * ⌊K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d⌋₊ := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ nX * ⌊K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d⌋₊ :=
          Nat.mul_le_mul_right _ (hY σ)
  · obtain ⟨x₀, hx₀, hdx⟩ := hmem l hl hlu
    have hlt' := hlab l hl hlu
    have hX' := hid l hl hlu
    have hyt := hyb l hl hlu
    have hey : |e ⬝ᵥ zy (c l) t'| ≤ 4 * K * ‖e‖ := by
      have := abs_dot_le e (zy (c l) t')
      have h2 : 2 * ‖e‖ * ‖zy (c l) t'‖ ≤ 2 * ‖e‖ * (2 * K) :=
        mul_le_mul_of_nonneg_left hyt (by positivity)
      linarith
    -- the scalar at `t'` is in the tested interval
    have hS : zS F (c l) t' ∈ Icc (x₀ - (4 * K * ‖e‖ + δX))
        (x₀ - (4 * K * ‖e‖ + δX) + (8 * K * ‖e‖ + 2 * δX)) := by
      rw [abs_le] at hdx hey
      constructor <;> linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hzz x₀ ⟨⟨l, hlt', rfl⟩, hS⟩)
    rw [Metric.mem_closedBall, Real.dist_eq] at hj
    refine ⟨(x₀ - zz x₀ j) / e k, Finset.mem_biUnion.mpr ⟨x₀, hx₀, Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, rfl⟩⟩, ?_⟩
    have hproj : ((e k)⁻¹ • e) ⬝ᵥ zy (c l) t' = (X l - zS F (c l) t') / e k := by
      rw [smul_dotProduct, smul_eq_mul, hX']; field_simp; ring
    have key : |((e k)⁻¹ • e) ⬝ᵥ zy (c l) t' - (x₀ - zz x₀ j) / e k| ≤ δX / ‖e‖ + r := by
      rw [hproj, ← sub_div, abs_div, hek, div_le_iff₀ he]
      have : X l - zS F (c l) t' - (x₀ - zz x₀ j) = (X l - x₀) - (zS F (c l) t' - zz x₀ j) := by
        ring
      rw [this]
      calc |(X l - x₀) - (zS F (c l) t' - zz x₀ j)| ≤ |X l - x₀| + |zS F (c l) t' - zz x₀ j| :=
            abs_sub _ _
        _ ≤ δX + ‖e‖ * r := add_le_add hdx hj
        _ = (δX / ‖e‖ + r) * ‖e‖ := by field_simp
    have hnorm : ‖(e k)⁻¹ • e‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, hek, inv_mul_le_iff₀ he, mul_one]
    have hmove : |((e k)⁻¹ • e) ⬝ᵥ zy (c l) u - ((e k)⁻¹ • e) ⬝ᵥ zy (c l) t'| ≤ 2 * (h * K) := by
      rw [← dotProduct_sub]
      have := abs_dot_le ((e k)⁻¹ • e) (zy (c l) u - zy (c l) t')
      have hhK : 0 ≤ h * K := le_trans (norm_nonneg _) (hyy l hl hlu)
      have h2 : 2 * ‖(e k)⁻¹ • e‖ * ‖zy (c l) u - zy (c l) t'‖ ≤ 2 * 1 * (h * K) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by norm_num)) (hyy l hl hlu)
          (norm_nonneg _) (by norm_num)
      linarith
    calc |((e k)⁻¹ • e) ⬝ᵥ zy (c l) u - (x₀ - zz x₀ j) / e k|
        ≤ |((e k)⁻¹ • e) ⬝ᵥ zy (c l) u - ((e k)⁻¹ • e) ⬝ᵥ zy (c l) t'| +
            |((e k)⁻¹ • e) ⬝ᵥ zy (c l) t' - (x₀ - zz x₀ j) / e k| := abs_sub_le _ _ _
      _ ≤ 2 * (h * K) + (δX / ‖e‖ + r) := add_le_add hmove key
      _ = δX / ‖e‖ + r + 2 * (h * K) := by ring

/-- The root polynomial of one row component (copied from x0801's `Jets/FinalTest.lean`). -/
def rowPolynomial₁ (R : ℕ → ℝ) (M : ℕ) (u : ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    Polynomial.C (R i / (i.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ i

/-- The root row polynomial, one polynomial per component. -/
def rowPolynomial (R : ℕ → Fin 2 → ℝ) (M : ℕ) (u : ℝ) : Fin 2 → Polynomial ℝ :=
  fun i => rowPolynomial₁ (fun n => R n i) M u

theorem rowPolynomial_eval (R : ℕ → Fin 2 → ℝ) (M : ℕ) (u v : ℝ) (i : Fin 2) :
    (rowPolynomial R M u i).eval v = rowPoly R M u v i := by
  simp only [rowPolynomial, rowPolynomial₁, rowPoly, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem rowPolynomial_natDegree_le (R : ℕ → Fin 2 → ℝ) (M : ℕ) (u : ℝ) (i : Fin 2) :
    (rowPolynomial R M u i).natDegree ≤ M := by
  unfold rowPolynomial rowPolynomial₁
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
  have hn' : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : (Polynomial.X - Polynomial.C u).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_sub_C]
  calc n * (Polynomial.X - Polynomial.C u).natDegree ≤ n * 1 := Nat.mul_le_mul_left _ this
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

theorem abs_coeff_rowPolynomial_le {R : ℕ → Fin 2 → ℝ} {BR : ℝ} (hR : ∀ n, ‖R n‖ ≤ BR) (M : ℕ)
    {u : ℝ} (hu : |u| ≤ 1) (i : Fin 2) (k : ℕ) :
    |(rowPolynomial R M u i).coeff k| ≤ (M + 1) * (BR * 2 ^ M) := by
  have hR' : ∀ n, |R n i| ≤ BR := fun n => (abs_le_norm (R n) i).trans (hR n)
  have hBR : 0 ≤ BR := le_trans (abs_nonneg _) (hR' 0)
  have hterm : ∀ n ∈ Finset.range (M + 1),
      |(Polynomial.C (R n i / (n.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ n).coeff k| ≤
        BR * 2 ^ M := by
    intro n hn
    have hn' : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [Polynomial.coeff_C_mul, abs_mul, abs_div, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos n)
    have h1 : |R n i| / (n.factorial : ℝ) ≤ BR := (div_le_self (abs_nonneg _) hf).trans (hR' n)
    have h2 := abs_coeff_X_sub_C_pow_le hu n k
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hn'
    calc |R n i| / (n.factorial : ℝ) * |((Polynomial.X - Polynomial.C u) ^ n).coeff k|
        ≤ BR * 2 ^ n := mul_le_mul h1 h2 (abs_nonneg _) hBR
      _ ≤ BR * 2 ^ M := mul_le_mul_of_nonneg_left h3 hBR
  have e : (rowPolynomial R M u i).coeff k = ∑ n ∈ Finset.range (M + 1),
      (Polynomial.C (R n i / (n.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ n).coeff k := by
    simp only [rowPolynomial, rowPolynomial₁, Polynomial.finsetSum_coeff]
  rw [e]
  calc |∑ n ∈ Finset.range (M + 1),
        (Polynomial.C (R n i / (n.factorial : ℝ)) * (Polynomial.X - Polynomial.C u) ^ n).coeff k|
      ≤ ∑ n ∈ Finset.range (M + 1),
          |(Polynomial.C (R n i / (n.factorial : ℝ)) *
            (Polynomial.X - Polynomial.C u) ^ n).coeff k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (M + 1), BR * 2 ^ M := Finset.sum_le_sum hterm
    _ = (M + 1) * (BR * 2 ^ M) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **The final test.**  If the row misses the root polynomial at `t'` by `θ` (sup norm), the
trajectories of `D` labelled at `t'` carry little prior mass. -/
theorem final_test {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) {D : Set Λ} {u t' p δ h θ r : ℝ} {M : ℕ} (hM : 2 ≤ M)
    {R : ℕ → Fin 2 → ℝ} {BR : ℝ} {nL : ℕ} (hR0 : R 0 = F u) (hRb : ∀ i, ‖R i‖ ≤ BR)
    (hlab : ∀ l ∈ D, (l, u) ∈ E) (hL : NodeLists E F c D u R M p δ nL) (hδp : p ≤ δ)
    (hζp : ζ ≤ p) (hp1 : p ≤ 1) (htu : |t' - u| ≤ h) (hh1 : h ≤ 1)
    (hθ : θ ≤ ‖F t' - rowPoly R M u t'‖) (hθ0 : 0 < θ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hζr : ζ ≤ θ * r) (herr : (M + 1) * δ + 2 * K * BR * h ^ (M + 1) ≤ θ * r) :
    ν {l | l ∈ D ∧ (l, t') ∈ E} ≤ ENNReal.ofReal (4000 * K ^ 6 *
      ((nL ^ M * ⌊K * ((8 * K + 2) / r) ^ d⌋₊ : ℕ) : ℝ) * (2 * r + 2 * (h * K) + p)) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hp : 0 < p := lt_of_lt_of_le hSN.zeta_pos hζp
  have hBR : 0 ≤ BR := le_trans (norm_nonneg _) (hRb 0)
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) htu
  set e := F t' - rowPoly R M u t' with he_def
  have he : 0 < ‖e‖ := lt_of_lt_of_le hθ0 hθ
  obtain ⟨k, hek, hek1, hek'⟩ := exists_normalized_row he
  set D' := {l | l ∈ D ∧ (l, t') ∈ E}
  set X : Λ → ℝ := fun l => ∑ i ∈ Finset.range (M + 1),
      (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i -
        (R M ⬝ᵥ zv (c l)) * (t' - u) ^ (M + 1) / (M.factorial : ℝ)
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
      (fun l => (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i) δ
        (if i = 0 then 1 else nL) := by
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
  have hXdet : Determined E (fun l => zS F (c l) u) D' u p X
      ((M + 1) * δ + 2 * K * BR * h ^ (M + 1)) (nL ^ M) := by
    have := hsum.perturb (Ψ := X) (ε := 2 * K * BR * h ^ (M + 1)) (fun l hl hlu => ?_)
    · refine this.mono (le_of_eq ?_) le_rfl
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    · have hlt' := hl.2
      have hc : ∀ e, |c l e| ≤ K := hSN.coeff_le _ hlt'
      have hv := norm_zv_le hc
      simp only [X]
      rw [show (∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i -
          (R M ⬝ᵥ zv (c l)) * (t' - u) ^ (M + 1) / (M.factorial : ℝ)) -
          ∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) * jet R (c l) u i =
          -((R M ⬝ᵥ zv (c l)) * (t' - u) ^ (M + 1) / (M.factorial : ℝ)) by ring, abs_neg]
      rw [abs_div, Nat.abs_cast, abs_mul, abs_pow]
      have hf : (1 : ℝ) ≤ (M.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos M)
      have hpw : |t' - u| ^ (M + 1) ≤ h ^ (M + 1) := pow_le_pow_left₀ (abs_nonneg _) htu _
      have hdot : |R M ⬝ᵥ zv (c l)| ≤ 2 * K * BR := by
        have := abs_dot_le (R M) (zv (c l))
        have h2 : 2 * ‖R M‖ * ‖zv (c l)‖ ≤ 2 * BR * K :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hRb M) (by norm_num)) hv (norm_nonneg _)
            (by positivity)
        linarith
      calc |R M ⬝ᵥ zv (c l)| * |t' - u| ^ (M + 1) / (M.factorial : ℝ)
          ≤ |R M ⬝ᵥ zv (c l)| * |t' - u| ^ (M + 1) / 1 := by
            apply div_le_div_of_nonneg_left (by positivity) one_pos hf
        _ ≤ 2 * K * BR * h ^ (M + 1) := by
            rw [div_one]
            exact mul_le_mul hdot hpw (by positivity) (by positivity)
  -- the identity
  have hid : ∀ l ∈ D', (l, u) ∈ E → X l = zS F (c l) t' + e ⬝ᵥ zy (c l) t' := by
    intro l _ _
    have := zS_eq_taylor (F := F) (R := R) (c := c l) (u := u) (v := t') hM
    simp only [X, he_def]
    have hsum_eq : ∑ i ∈ Finset.range (M + 1), (t' - u) ^ i / (i.factorial : ℝ) *
        jet R (c l) u i =
        ∑ i ∈ Finset.range (M + 1), jet R (c l) u i * (t' - u) ^ i / (i.factorial : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [hsum_eq]
    linarith
  have hδX : 0 ≤ (M + 1) * δ + 2 * K * BR * h ^ (M + 1) := by positivity
  have hY := projdet_of_Xdet hSN (D := D') (u := u) (t' := t') (h := h) (k := k) hek he hr0 hr1
    (hζr.trans (by gcongr)) hδX X hXdet (fun l hl _ => hl.2) hid
    (fun l hl hlu => by
      have hc : ∀ e, |c l e| ≤ K := hSN.coeff_le _ hlu
      have hv := norm_zv_le hc
      rw [zy_add (c l) u t', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      calc |t' - u| * ‖zv (c l)‖ ≤ h * K := mul_le_mul htu hv (norm_nonneg _) hh0)
    (fun l hl _ => norm_zy_le (hSN.coeff_le _ hl.2) (hSN.time_mem _ hl.2))
  -- precision and count
  set δX := (M + 1) * δ + 2 * K * BR * h ^ (M + 1)
  have hδXr : δX ≤ ‖e‖ * r := herr.trans (mul_le_mul_of_nonneg_right hθ hr0.le)
  have hprec : δX / ‖e‖ + r + 2 * (h * K) ≤ 2 * r + 2 * (h * K) := by
    have : δX / ‖e‖ ≤ r := by rw [div_le_iff₀ he]; linarith
    linarith
  have hcount : ⌊K * ((8 * K * ‖e‖ + 2 * δX) / (‖e‖ * r)) ^ d⌋₊ ≤
      ⌊K * ((8 * K + 2) / r) ^ d⌋₊ := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ hK0
    apply Real.rpow_le_rpow (by positivity) _ hd0
    rw [div_le_div_iff₀ (by positivity) hr0]
    have : δX ≤ ‖e‖ := hδXr.trans (by nlinarith)
    nlinarith
  have hY' := hY.mono hprec (Nat.mul_le_mul_left _ hcount)
  have hmass := Determined.mass_le hSN hd1 hζp hp1 (by positivity) hek1 hek' hY'
  refine (measure_mono ?_).trans (hmass.trans (le_of_eq ?_))
  · intro l hl
    exact ⟨hl, hlab l hl.1⟩
  · congr 1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
