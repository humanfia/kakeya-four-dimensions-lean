import Submission.Obl.k4_scalar_candidate_original_return.Core.QuadBounds
import Submission.Obl.k4_eligibility_sign_description.Families

/-!
# Affine normalization of two-variable quadratics
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.Normalize

open MeasureTheory Set MvPolynomial

/-- An affine form in the two variables has total degree at most one. -/
private theorem affine_form_totalDegree_le (a₀ a₁ c : ℝ) :
    (C a₀ * X 0 + C a₁ * X 1 + C c : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
  have h1 : (C a₀ * X 0 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simp [totalDegree_C, totalDegree_X]
  have h2 : (C a₁ * X 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simp [totalDegree_C, totalDegree_X]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_add _ _).trans (max_le h1 h2)
  · simp [totalDegree_C]

/-- Explicit affine substitution `z ↦ A z + b` into a two-variable polynomial. -/
noncomputable def affSubst (P : MvPolynomial (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ)
    (b : Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval (fun i => C (A i 0) * X 0 + C (A i 1) * X 1 + C (b i)) P

theorem affSubst_totalDegree_le (P : MvPolynomial (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ)
    (b : Fin 2 → ℝ) : (affSubst P A b).totalDegree ≤ P.totalDegree :=
  Submission.Obl.k4_eligibility_sign_description.degree_aeval_le P _
    (fun i => affine_form_totalDegree_le (A i 0) (A i 1) (b i))

theorem eval_affSubst (P : MvPolynomial (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ)
    (b : Fin 2 → ℝ) (z : Fin 2 → ℝ) :
    eval z (affSubst P A b) = eval (fun i => A i 0 * z 0 + A i 1 * z 1 + b i) P := by
  unfold affSubst
  rw [Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
  have hfun : (fun i => eval z (C (A i 0) * X 0 + C (A i 1) * X 1 + C (b i))) =
      (fun i => A i 0 * z 0 + A i 1 * z 1 + b i) := by
    funext i
    simp
  rw [hfun]

/-- Affine substitution keeps a two-variable polynomial of the same total degree. -/
theorem affine_subst (P : MvPolynomial (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ P.totalDegree ∧
      ∀ z : Fin 2 → ℝ, eval z Q = eval (fun i => A i 0 * z 0 + A i 1 * z 1 + b i) P := by
  refine ⟨MvPolynomial.aeval (fun i => C (A i 0) * X 0 + C (A i 1) * X 1 + C (b i)) P, ?_, ?_⟩
  · exact Submission.Obl.k4_eligibility_sign_description.degree_aeval_le P _
      (fun i => affine_form_totalDegree_le (A i 0) (A i 1) (b i))
  · intro z
    rw [Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
    have hfun : (fun i => eval z (C (A i 0) * X 0 + C (A i 1) * X 1 + C (b i))) =
        (fun i => A i 0 * z 0 + A i 1 * z 1 + b i) := by
      funext i
      simp
    rw [hfun]

set_option linter.unusedVariables false in
/-- One-dimensional extrapolation from an interval of length `ℓ ≤ 1` inside `[0,1]`. -/
theorem quad1d_extrap {a b c B α ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hα : 0 ≤ α)
    (hαℓ : α + ℓ ≤ 1)
    (hB : ∀ t ∈ Set.Icc α (α + ℓ), |a + b * t + c * t ^ 2| ≤ B) :
    ∀ t ∈ Set.Icc (-4 : ℝ) 5, |a + b * t + c * t ^ 2| ≤ 1000 / ℓ ^ 2 * B := by
  intro t ht
  have h0 := hB α ⟨le_rfl, by linarith⟩
  have h1 := hB (α + ℓ / 2) ⟨by linarith, by linarith⟩
  have h2 := hB (α + ℓ) ⟨by linarith, le_rfl⟩
  have hBnn : 0 ≤ B := (abs_nonneg _).trans h0
  have key : ℓ ^ 2 * (a + b * t + c * t ^ 2) =
      2 * (a + b * α + c * α ^ 2) * (t - (α + ℓ / 2)) * (t - (α + ℓ)) +
      (-(4 * (a + b * (α + ℓ / 2) + c * (α + ℓ / 2) ^ 2) * (t - α) * (t - (α + ℓ)))) +
      2 * (a + b * (α + ℓ) + c * (α + ℓ) ^ 2) * (t - α) * (t - (α + ℓ / 2)) := by
    ring
  have e0 : |t - α| ≤ 5 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have e1 : |t - (α + ℓ / 2)| ≤ 5 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have e2 : |t - (α + ℓ)| ≤ 5 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have t1 : |2 * (a + b * α + c * α ^ 2) * (t - (α + ℓ / 2)) * (t - (α + ℓ))| ≤
      2 * B * 5 * 5 := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have t2 : |-(4 * (a + b * (α + ℓ / 2) + c * (α + ℓ / 2) ^ 2) * (t - α) * (t - (α + ℓ)))| ≤
      4 * B * 5 * 5 := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
  have t3 : |2 * (a + b * (α + ℓ) + c * (α + ℓ) ^ 2) * (t - α) * (t - (α + ℓ / 2))| ≤
      2 * B * 5 * 5 := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have hbound : |ℓ ^ 2 * (a + b * t + c * t ^ 2)| ≤ 200 * B := by
    rw [key]
    calc _ ≤ |2 * (a + b * α + c * α ^ 2) * (t - (α + ℓ / 2)) * (t - (α + ℓ)) +
          (-(4 * (a + b * (α + ℓ / 2) + c * (α + ℓ / 2) ^ 2) * (t - α) * (t - (α + ℓ))))| +
          |2 * (a + b * (α + ℓ) + c * (α + ℓ) ^ 2) * (t - α) * (t - (α + ℓ / 2))| :=
          abs_add_le _ _
      _ ≤ (|2 * (a + b * α + c * α ^ 2) * (t - (α + ℓ / 2)) * (t - (α + ℓ))| +
          |-(4 * (a + b * (α + ℓ / 2) + c * (α + ℓ / 2) ^ 2) * (t - α) * (t - (α + ℓ)))|) +
          |2 * (a + b * (α + ℓ) + c * (α + ℓ) ^ 2) * (t - α) * (t - (α + ℓ / 2))| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ 2 * B * 5 * 5 + 4 * B * 5 * 5 + 2 * B * 5 * 5 := by linarith
      _ = 200 * B := by ring
  have hl2 : 0 < ℓ ^ 2 := by positivity
  rw [abs_mul, abs_of_pos hl2] at hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  nlinarith [abs_nonneg (a + b * t + c * t ^ 2)]

/-- Two-dimensional extrapolation from a sub-box of the unit square to `[-4,5]²`. -/
theorem quad2d_extrap (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    {B α₀ α₁ ℓ₀ ℓ₁ : ℝ} (hℓ₀ : 0 < ℓ₀) (hℓ₁ : 0 < ℓ₁) (hα₀ : 0 ≤ α₀) (hα₁ : 0 ≤ α₁)
    (h₀ : α₀ + ℓ₀ ≤ 1) (h₁ : α₁ + ℓ₁ ≤ 1)
    (hB : ∀ z : Fin 2 → ℝ, z 0 ∈ Set.Icc α₀ (α₀ + ℓ₀) → z 1 ∈ Set.Icc α₁ (α₁ + ℓ₁) →
      |eval z P| ≤ B) :
    ∀ z : Fin 2 → ℝ, (∀ i, z i ∈ Set.Icc (-4 : ℝ) 5) →
      |eval z P| ≤ 10 ^ 6 / (ℓ₀ ^ 2 * ℓ₁ ^ 2) * B := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := QuadBounds.quad_normal_form P hP
  have hℓ₀1 : ℓ₀ ≤ 1 := by linarith
  have hℓ₁1 : ℓ₁ ≤ 1 := by linarith
  -- the box hypothesis in normal form
  have hbox : ∀ u ∈ Set.Icc α₀ (α₀ + ℓ₀), ∀ v ∈ Set.Icc α₁ (α₁ + ℓ₁),
      |a + b * u + c * v + d * u ^ 2 + e * u * v + f * v ^ 2| ≤ B := by
    intro u hu v hv
    have h := hB ![u, v] (by simpa using hu) (by simpa using hv)
    rw [hnf] at h
    simpa using h
  -- step 1: extrapolate in the first variable on the second variable's interval
  have hstep1 : ∀ v ∈ Set.Icc α₁ (α₁ + ℓ₁), ∀ u ∈ Set.Icc (-4 : ℝ) 5,
      |a + b * u + c * v + d * u ^ 2 + e * u * v + f * v ^ 2| ≤ 1000 / ℓ₀ ^ 2 * B := by
    intro v hv u hu
    have h := quad1d_extrap (a := a + c * v + f * v ^ 2) (b := b + e * v) (c := d) (B := B)
      hℓ₀ hℓ₀1 hα₀ h₀ (fun s hs => by
        have := hbox s hs v hv
        have heq : a + c * v + f * v ^ 2 + (b + e * v) * s + d * s ^ 2 =
            a + b * s + c * v + d * s ^ 2 + e * s * v + f * v ^ 2 := by ring
        rw [heq]; exact this) u hu
    have heq : a + c * v + f * v ^ 2 + (b + e * v) * u + d * u ^ 2 =
        a + b * u + c * v + d * u ^ 2 + e * u * v + f * v ^ 2 := by ring
    rw [heq] at h
    exact h
  -- step 2: extrapolate in the second variable
  intro z hz
  rw [hnf]
  have h := quad1d_extrap (a := a + b * z 0 + d * z 0 ^ 2) (b := c + e * z 0) (c := f)
    (B := 1000 / ℓ₀ ^ 2 * B) hℓ₁ hℓ₁1 hα₁ h₁ (fun s hs => by
      have := hstep1 s hs (z 0) (hz 0)
      have heq : a + b * z 0 + d * z 0 ^ 2 + (c + e * z 0) * s + f * s ^ 2 =
          a + b * z 0 + c * s + d * z 0 ^ 2 + e * z 0 * s + f * s ^ 2 := by ring
      rw [heq]; exact this) (z 1) (hz 1)
  have heq : a + b * z 0 + d * z 0 ^ 2 + (c + e * z 0) * z 1 + f * z 1 ^ 2 =
      a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2 := by ring
  rw [heq] at h
  have hconst : 1000 / ℓ₁ ^ 2 * (1000 / ℓ₀ ^ 2 * B) = 10 ^ 6 / (ℓ₀ ^ 2 * ℓ₁ ^ 2) * B := by
    field_simp
    ring
  rw [hconst] at h
  exact h

/-- A quadratic bounded on `[-4,5]²` is Lipschitz on `[-3,4]²`. -/
theorem quad_lipschitz_of_bound (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ z : Fin 2 → ℝ, (∀ i, z i ∈ Set.Icc (-4 : ℝ) 5) → |eval z P| ≤ B) :
    ∀ z z' : Fin 2 → ℝ, (∀ i, z i ∈ Set.Icc (-3 : ℝ) 4) → (∀ i, z' i ∈ Set.Icc (-3 : ℝ) 4) →
      |eval z P - eval z' P| ≤ 1000 * B * (|z 0 - z' 0| + |z 1 - z' 1|) := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := QuadBounds.quad_normal_form P hP
  have hval : ∀ u v : ℝ, u ∈ Set.Icc (-4 : ℝ) 5 → v ∈ Set.Icc (-4 : ℝ) 5 →
      |a + b * u + c * v + d * u ^ 2 + e * u * v + f * v ^ 2| ≤ B := by
    intro u v hu hv
    have h := hB ![u, v] (by
      intro i
      fin_cases i
      · simpa using hu
      · simpa using hv)
    rw [hnf] at h
    simpa using h
  have hm : (0 : ℝ) ∈ Set.Icc (-4 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Set.Icc (-4 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have hn1 : (-1 : ℝ) ∈ Set.Icc (-4 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have v00 := hval 0 0 hm hm
  have v10 := hval 1 0 hp1 hm
  have vm0 := hval (-1) 0 hn1 hm
  have v01 := hval 0 1 hm hp1
  have v0m := hval 0 (-1) hm hn1
  have v11 := hval 1 1 hp1 hp1
  norm_num at v00 v10 vm0 v01 v0m v11
  rw [abs_le] at v00 v10 vm0 v01 v0m v11
  have hBnn : 0 ≤ B := by linarith [v00.1, v00.2]
  have hb : |b| ≤ B := by rw [abs_le]; constructor <;> linarith
  have hc : |c| ≤ B := by rw [abs_le]; constructor <;> linarith
  have hd : |d| ≤ 2 * B := by rw [abs_le]; constructor <;> linarith
  have hf : |f| ≤ 2 * B := by rw [abs_le]; constructor <;> linarith
  have he : |e| ≤ 4 * B := by rw [abs_le]; constructor <;> linarith
  intro z z' hz hz'
  have hz0 : |z 0| ≤ 4 := by rw [abs_le]; constructor <;> linarith [(hz 0).1, (hz 0).2]
  have hz1 : |z 1| ≤ 4 := by rw [abs_le]; constructor <;> linarith [(hz 1).1, (hz 1).2]
  have hz0' : |z' 0| ≤ 4 := by rw [abs_le]; constructor <;> linarith [(hz' 0).1, (hz' 0).2]
  have hz1' : |z' 1| ≤ 4 := by rw [abs_le]; constructor <;> linarith [(hz' 1).1, (hz' 1).2]
  have hs0 : |z 0 + z' 0| ≤ 8 := (abs_add_le _ _).trans (by linarith)
  have hs1 : |z 1 + z' 1| ≤ 8 := (abs_add_le _ _).trans (by linarith)
  set Δ0 := z 0 - z' 0 with hΔ0
  set Δ1 := z 1 - z' 1 with hΔ1
  have key : eval z P - eval z' P =
      b * Δ0 + c * Δ1 + d * (Δ0 * (z 0 + z' 0)) + e * (Δ0 * z 1 + z' 0 * Δ1) +
        f * (Δ1 * (z 1 + z' 1)) := by
    rw [hnf z, hnf z', hΔ0, hΔ1]
    ring
  have tb : |b * Δ0| ≤ B * |Δ0| := by rw [abs_mul]; gcongr
  have tc : |c * Δ1| ≤ B * |Δ1| := by rw [abs_mul]; gcongr
  have td : |d * (Δ0 * (z 0 + z' 0))| ≤ 2 * B * (|Δ0| * 8) := by
    rw [abs_mul, abs_mul]; gcongr
  have te : |e * (Δ0 * z 1 + z' 0 * Δ1)| ≤ 4 * B * (|Δ0| * 4 + 4 * |Δ1|) := by
    rw [abs_mul]
    gcongr
    calc |Δ0 * z 1 + z' 0 * Δ1| ≤ |Δ0 * z 1| + |z' 0 * Δ1| := abs_add_le _ _
      _ = |Δ0| * |z 1| + |z' 0| * |Δ1| := by rw [abs_mul, abs_mul]
      _ ≤ |Δ0| * 4 + 4 * |Δ1| := by gcongr
  have tf : |f * (Δ1 * (z 1 + z' 1))| ≤ 2 * B * (|Δ1| * 8) := by
    rw [abs_mul, abs_mul]; gcongr
  rw [key]
  have hsum : |b * Δ0 + c * Δ1 + d * (Δ0 * (z 0 + z' 0)) + e * (Δ0 * z 1 + z' 0 * Δ1) +
        f * (Δ1 * (z 1 + z' 1))| ≤
      |b * Δ0| + |c * Δ1| + |d * (Δ0 * (z 0 + z' 0))| + |e * (Δ0 * z 1 + z' 0 * Δ1)| +
        |f * (Δ1 * (z 1 + z' 1))| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    refine (abs_add_le _ _).trans ?_
    gcongr
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  have hΔ0nn : 0 ≤ |Δ0| := abs_nonneg _
  have hΔ1nn : 0 ≤ |Δ1| := abs_nonneg _
  nlinarith

end Submission.Obl.k4_scalar_candidate_original_return.Normalize
