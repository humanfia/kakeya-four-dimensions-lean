-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/MeshCalibration.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit abc1113588ce6b9e412a59326ea88392111ccb7e,
   Submission/Obl/k4_finite_projected_horizontal_candidates/MeshCalibration.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.RawGridCalibration
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetJets
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

/-!
# Mesh calibration of fixed-degree base polynomials

Only finite mesh caps `μ {cell = q} ≤ H δ³` are assumed, never a continuous base density.

* `mesh_calibration`: a base polynomial of degree `≤ D` bounded by `E` at the points of a
  measure of mass `≥ m` in the cube `[-K, K]³` has coefficients `≤ (K H / m)^n E`
  (accepted o242's raw kernel `exists_raw_coefficient_bound_from_original_grid`).
* `norm_cev_le`, `cev_lipschitz`: growth and variation of the complex evaluation on
  `EuclideanSpace ℂ (Fin 3)` from a coefficient bound (lib `K4PolynomialRemezThree` and
  accepted o149 `holomorphic_inner_lipschitz`).
* `slab_mass`: the thin slab `|B| ≤ b (K H)^(-c)` of an affine `B` with a coefficient of
  size `b` carries mass `≤ (K H)^(-A)` (calibration on the restricted measure).
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial

noncomputable section

theorem le_pow_of_two_le' {X : ℝ} (hX : 2 ≤ X) (n : ℕ) : (n : ℝ) ≤ X ^ n := by
  have h2n : (n : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this.le
  exact h2n.trans (pow_le_pow_left₀ (by norm_num) hX n)

theorem const_le_pow {X C : ℝ} (hX : 2 ≤ X) (hC : 0 ≤ C) : C ≤ X ^ (⌈C⌉₊) :=
  (Nat.le_ceil C).trans (le_pow_of_two_le' hX _)

/-- **Mesh calibration** of a base polynomial of fixed degree from finite mesh caps. -/
theorem mesh_calibration (D : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (K H m δ E : ℝ), 2 ≤ K → 1 ≤ H → 0 < m → m ≤ 1 → 0 < δ → 0 ≤ E →
      (K * H / m) ^ n * δ ≤ 1 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → Fin 3 → ℝ),
      ENNReal.ofReal m ≤ μ univ →
      (∀ q : Fin 3 → ℤ, μ {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
      (∀ᵐ ω ∂μ, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) P| ≤ E) →
      ∀ e, |P.coeff e| ≤ (K * H / m) ^ n * E := by
  obtain ⟨C₀, L, hC₀, hL, hcal⟩ :=
    Submission.Obl.k4_quadratic_mesh_coefficient_calibration.exists_raw_coefficient_bound_from_original_grid D
  set c₀ : ℝ := (((D + 1) ^ 3 : ℕ) : ℝ) * (2 * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
    (16384 * ((D : ℝ) + 1)) ^ (3 * D)) with hc₀
  set c₁ : ℝ := 4 * L * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ * (16384 * ((D : ℝ) + 1)) ^ (3 * D) with hc₁
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  set n : ℕ := ⌈c₀⌉₊ + ⌈c₁⌉₊ + 9 * D + 1 with hn
  refine ⟨n, by omega, ?_⟩
  intro K H m δ E hK hH hm hm1 hδ hE hmesh Ω _ μ u hmass hcap P hP hgood
  have hK1 : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hHpos : 0 < H := by linarith
  set X : ℝ := K * H / m with hXdef
  have hHm : 1 ≤ H / m := by rw [le_div_iff₀ hm]; linarith
  have hX2 : 2 ≤ X := by
    rw [hXdef, mul_div_assoc]
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ K * (H / m) := mul_le_mul hK hHm (by norm_num) (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  -- the loss of the raw kernel
  have hratio : 32 * ((D : ℝ) + 1) / (m / (H * (8 * K) ^ 3)) ≤ 16384 * ((D : ℝ) + 1) * X ^ 3 := by
    rw [div_div_eq_mul_div, div_le_iff₀ hm]
    have hK3 : K ^ 3 * H ≤ K ^ 3 * H ^ 3 / m ^ 2 := by
      have hH3 : H ≤ H ^ 3 / m ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have hmH : m ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hm.le (by linarith) 2
        nlinarith
      calc K ^ 3 * H ≤ K ^ 3 * (H ^ 3 / m ^ 2) := by gcongr
        _ = K ^ 3 * H ^ 3 / m ^ 2 := by ring
    have hX3 : X ^ 3 * m = K ^ 3 * H ^ 3 / m ^ 2 := by
      rw [hXdef]; field_simp
    calc 32 * ((D : ℝ) + 1) * (H * (8 * K) ^ 3) = 16384 * ((D : ℝ) + 1) * (K ^ 3 * H) := by ring
      _ ≤ 16384 * ((D : ℝ) + 1) * (K ^ 3 * H ^ 3 / m ^ 2) := by gcongr
      _ = 16384 * ((D : ℝ) + 1) * X ^ 3 * m := by rw [mul_assoc _ (X ^ 3), hX3]
  have hloss : (32 * ((D : ℝ) + 1) / (m / (H * (8 * K) ^ 3))) ^ (3 * D) ≤
      (16384 * ((D : ℝ) + 1)) ^ (3 * D) * X ^ (9 * D) := by
    calc _ ≤ (16384 * ((D : ℝ) + 1) * X ^ 3) ^ (3 * D) :=
          pow_le_pow_left₀ (by positivity) hratio _
      _ = (16384 * ((D : ℝ) + 1)) ^ (3 * D) * X ^ (9 * D) := by
          rw [mul_pow, ← pow_mul]; ring_nf
  have hXn9 : X ^ (9 * D) ≤ X ^ n := pow_le_pow_right₀ hX1 (by omega)
  have hc₀X : c₀ ≤ X ^ (⌈c₀⌉₊) := const_le_pow hX2 hc₀0
  have hc₁X : c₁ ≤ X ^ (⌈c₁⌉₊) := const_le_pow hX2 hc₁0
  have hδ1 : δ ≤ 1 := by
    have h1 : 1 ≤ X ^ n := one_le_pow₀ hX1
    nlinarith
  -- the smallness hypothesis of the raw kernel
  have hsmall : 2 * L * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
      (32 * ((D : ℝ) + 1) / (m / (H * (8 * K) ^ 3))) ^ (3 * D) * (δ / (8 * K)) ≤ 1 / 2 := by
    have hδK : δ / (8 * K) ≤ δ / 8 := by
      apply div_le_div_of_nonneg_left hδ.le (by norm_num); linarith
    have hA : 0 ≤ 2 * L * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ := by positivity
    calc 2 * L * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
          (32 * ((D : ℝ) + 1) / (m / (H * (8 * K) ^ 3))) ^ (3 * D) * (δ / (8 * K))
        ≤ 2 * L * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
          ((16384 * ((D : ℝ) + 1)) ^ (3 * D) * X ^ (9 * D)) * (δ / 8) := by gcongr
      _ = c₁ * X ^ (9 * D) * δ / 16 := by rw [hc₁]; ring
      _ ≤ X ^ (⌈c₁⌉₊) * X ^ (9 * D) * δ / 16 := by gcongr
      _ ≤ X ^ n * δ / 16 := by
          rw [← pow_add]
          gcongr
          omega
      _ ≤ 1 / 16 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hmb : m ≤ H * (8 * K) ^ 3 := by
    have : (1 : ℝ) ≤ (8 * K) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hcap' : ∀ q : Fin 3 → ℤ, μ {p | Submission.Lib.K4CommonLocalChoice.cell δ (u p) = q} ≤
      ENNReal.ofReal (H * δ ^ 3) := fun q => hcap q
  have hcoeff := hcal Ω μ u P hP K δ m H E hK1 hδ (hδ1.trans hK1) hm hHpos hmb hE hmass hcap'
    hgood hsmall
  intro e
  refine (hcoeff e).trans ?_
  calc (((D + 1) ^ 3 : ℕ) : ℝ) * (2 * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
        (32 * ((D : ℝ) + 1) / (m / (H * (8 * K) ^ 3))) ^ (3 * D) * E)
      ≤ (((D + 1) ^ 3 : ℕ) : ℝ) * (2 * (((D + 1) ^ 3 : ℕ) : ℝ) * C₀ *
        ((16384 * ((D : ℝ) + 1)) ^ (3 * D) * X ^ (9 * D)) * E) := by gcongr
    _ = c₀ * X ^ (9 * D) * E := by rw [hc₀]; ring
    _ ≤ X ^ (⌈c₀⌉₊) * X ^ (9 * D) * E := by gcongr
    _ ≤ X ^ n * E := by
        rw [← pow_add]
        gcongr
        omega

/-! ### Complex evaluation of base polynomials -/

/-- Complex evaluation of a real base polynomial at a point of `EuclideanSpace ℂ (Fin 3)`. -/
abbrev cev (P : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  eval₂ (algebraMap ℝ ℂ) (fun i => z i) P

theorem differentiable_cev (P : MvPolynomial (Fin 3) ℝ) : Differentiable ℂ (cev P) :=
  Submission.Obl.k4_stable_quadratic_hidden_sheets.differentiable_eval₂ P

theorem cev_emb (P : MvPolynomial (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    cev P (emb x) = ((eval (fun i => x i) P : ℝ) : ℂ) :=
  Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal P (fun i => x i)

theorem norm_cev_le (D : ℕ) (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ D)
    {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R) (hcoeff : ∀ e, |P.coeff e| ≤ E)
    (z : EuclideanSpace ℂ (Fin 3)) (hz : ‖z‖ ≤ R) :
    ‖cev P z‖ ≤ ((D + 1 : ℕ) : ℝ) ^ 3 * R ^ D * E :=
  Submission.Lib.K4PolynomialRemezThree.norm_complex_eval_le_of_coeff_bound 3 D P hP hE hR
    hcoeff (fun i => z i) (fun i => (PiLp.norm_apply_le z i).trans hz)

/-- Variation of the complex evaluation from a coefficient bound. -/
theorem cev_lipschitz (D : ℕ) (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ D)
    {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R) (hcoeff : ∀ e, |P.coeff e| ≤ E)
    (z y : EuclideanSpace ℂ (Fin 3)) (hz : ‖z‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖cev P z - cev P y‖ ≤ 4 * (((D + 1 : ℕ) : ℝ) ^ 3 * (2 * R) ^ D * E) / R * ‖z - y‖ := by
  have hR0 : 0 < R := by linarith
  set f : EuclideanSpace ℂ (Fin 3) → ℂ := fun v => cev P ((R : ℂ) • v) with hf
  have hfd : DifferentiableOn ℂ f (ball 0 4) :=
    ((differentiable_cev P).comp (differentiable_id.const_smul (R : ℂ))).differentiableOn
  have hbound : ∀ v : EuclideanSpace ℂ (Fin 3), ‖v‖ ≤ 2 →
      ‖f v‖ ≤ ((D + 1 : ℕ) : ℝ) ^ 3 * (2 * R) ^ D * E := by
    intro v hv
    refine norm_cev_le D P hP hE (by linarith) hcoeff _ ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    nlinarith
  have hx : ‖(R⁻¹ : ℂ) • y‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    rw [inv_mul_le_iff₀ hR0]; linarith
  have hz' : ‖(R⁻¹ : ℂ) • z‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    rw [inv_mul_le_iff₀ hR0]; linarith
  have h := Submission.Obl.k4_algebraic_real_jet_comparison.holomorphic_inner_lipschitz hfd
    hbound hx hz'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hfz : f ((R⁻¹ : ℂ) • z) = cev P z := by
    simp only [hf, smul_smul, mul_inv_cancel₀ hRc, one_smul]
  have hfy : f ((R⁻¹ : ℂ) • y) = cev P y := by
    simp only [hf, smul_smul, mul_inv_cancel₀ hRc, one_smul]
  rw [hfz, hfy] at h
  have hdiff : ‖(R⁻¹ : ℂ) • z - (R⁻¹ : ℂ) • y‖ = ‖z - y‖ / R := by
    rw [← smul_sub, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    field_simp
  rw [hdiff] at h
  calc ‖cev P z - cev P y‖ ≤ 4 * (((D + 1 : ℕ) : ℝ) ^ 3 * (2 * R) ^ D * E) * (‖z - y‖ / R) := h
    _ = 4 * (((D + 1 : ℕ) : ℝ) ^ 3 * (2 * R) ^ D * E) / R * ‖z - y‖ := by ring

/-! ### Thin slabs of affine functions -/

/-- **Thin slabs carry little mass.** An affine base polynomial `B` with some coefficient of
size at least `b` has `|B| ≤ b (K H)^(-c)` only on mass `≤ (K H)^(-A)` of points of the cube,
for a measure with finite mesh caps. -/
theorem slab_mass :
    ∃ n₁ : ℕ, 1 ≤ n₁ ∧ ∀ (A : ℕ) (K H δ b : ℝ), 2 ≤ K → 1 ≤ H → 0 < δ → 0 < b →
      (K * H) ^ (n₁ * (A + 1)) * δ ≤ 1 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → Fin 3 → ℝ), Measurable u →
      (∀ q : Fin 3 → ℤ, μ {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      ∀ B : MvPolynomial (Fin 3) ℝ, B.totalDegree ≤ 1 → (∃ e, b ≤ |B.coeff e|) →
      μ {ω | (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) B| ≤ b * ((K * H) ^ (n₁ * (A + 1) + 1))⁻¹} ≤
        ENNReal.ofReal (((K * H) ^ A)⁻¹) := by
  obtain ⟨n₁, hn₁, hcal⟩ := mesh_calibration 1
  refine ⟨n₁, hn₁, ?_⟩
  intro A K H δ b hK hH hδ hb hmesh Ω _ μ u hu hcap B hB ⟨e₀, he₀⟩
  set X : ℝ := K * H with hXdef
  have hX2 : 2 ≤ X := by rw [hXdef]; nlinarith
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  set S : Set Ω := {ω | (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) B| ≤ b * (X ^ (n₁ * (A + 1) + 1))⁻¹}
    with hS
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {ω | ∀ i, |u ω i| ≤ K} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le ((measurable_pi_apply i).comp hu).abs measurable_const
    have h2 : MeasurableSet {ω | |eval (u ω) B| ≤ b * (X ^ (n₁ * (A + 1) + 1))⁻¹} :=
      measurableSet_le ((MvPolynomial.continuous_eval B).measurable.comp hu).abs measurable_const
    exact h1.inter h2
  by_contra hcontra
  rw [not_le] at hcontra
  set m : ℝ := (X ^ A)⁻¹ with hmdef
  have hm : 0 < m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
  have hXm : K * H / m = X ^ (A + 1) := by
    rw [hmdef, ← hXdef, div_inv_eq_mul, pow_succ]; ring
  have hmass : ENNReal.ofReal m ≤ (μ.restrict S) univ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact hcontra.le
  have hcap' : ∀ q : Fin 3 → ℤ, (μ.restrict S) {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤
      ENNReal.ofReal (H * δ ^ 3) := fun q => (Measure.restrict_le_self _).trans (hcap q)
  have hgood : ∀ᵐ ω ∂(μ.restrict S), (∀ i, |u ω i| ≤ K) ∧
      |eval (u ω) B| ≤ b * (X ^ (n₁ * (A + 1) + 1))⁻¹ :=
    (ae_restrict_mem hSm).mono fun ω hω => hω
  have hmesh' : (K * H / m) ^ n₁ * δ ≤ 1 := by
    rw [hXm, ← pow_mul, Nat.mul_comm]; exact hmesh
  have hc := hcal K H m δ (b * (X ^ (n₁ * (A + 1) + 1))⁻¹) hK hH hm hm1 hδ
    (mul_nonneg hb.le (by positivity))
    hmesh' Ω (μ.restrict S) u hmass hcap' B hB hgood e₀
  rw [hXm, ← pow_mul] at hc
  have hlt : X ^ ((A + 1) * n₁) * (b * (X ^ (n₁ * (A + 1) + 1))⁻¹) < b := by
    have hXe : X ^ (n₁ * (A + 1) + 1) = X ^ ((A + 1) * n₁) * X := by
      rw [pow_succ, mul_comm (A + 1) n₁]
    rw [hXe]
    have hXp : 0 < X ^ ((A + 1) * n₁) := by positivity
    have hbX : 0 < b * X ^ ((A + 1) * n₁) := mul_pos hb hXp
    rw [mul_inv, ← mul_assoc, mul_comm (X ^ ((A + 1) * n₁)) b, mul_assoc,
      mul_inv_cancel_left₀ hXp.ne']
    rw [mul_inv_lt_iff₀ hXpos]
    nlinarith
  linarith

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
