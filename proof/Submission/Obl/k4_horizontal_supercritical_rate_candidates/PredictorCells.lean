import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Geometry

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates

noncomputable section

/-- The collapsed affine predictor has two scalar cell coordinates. -/
theorem parameterValue_cell_difference (L : Fin 4 → ℝ)
    (pc qc v D t τ R R₀ : ℝ) :
    parameterValue L pc qc v D t 0 R - parameterValue L pc qc v D τ 0 R₀ =
      (t - τ) * (L 1 + v * L 2 - pc * L 3) + D * (R - R₀) * L 3 := by
  unfold parameterValue affineValue
  ring

/-- Each true label supplies a bounded number of hidden terminal bins in one
fine scalar base cell, once this oscillation is below terminal thickness. -/
theorem parameterValue_cell_oscillation (L : Fin 4 → ℝ)
    {pc qc v D t τ R R₀ H σ : ℝ} (hD : 0 ≤ D)
    (h₁ : |L 1| ≤ H) (h₂ : |L 2| ≤ H) (h₃ : |L 3| ≤ H)
    (ht : |t - τ| ≤ σ) (hR : |R - R₀| ≤ σ) :
    |parameterValue L pc qc v D t 0 R - parameterValue L pc qc v D τ 0 R₀| ≤
      H * σ * (1 + |v| + |pc| + D) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans h₁
  have hσ : 0 ≤ σ := (abs_nonneg _).trans ht
  have hA : |L 1 + v * L 2 - pc * L 3| ≤ H * (1 + |v| + |pc|) := by
    calc
      _ ≤ |L 1| + |v * L 2| + |pc * L 3| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ H + |v| * H + |pc| * H := by
        simp only [abs_mul]
        gcongr
      _ = _ := by ring
  rw [parameterValue_cell_difference]
  calc
    _ ≤ |(t - τ) * (L 1 + v * L 2 - pc * L 3)| + |D * (R - R₀) * L 3| :=
      abs_add_le _ _
    _ ≤ σ * (H * (1 + |v| + |pc|)) + D * σ * H := by
      simp only [abs_mul, abs_of_nonneg hD]
      gcongr
    _ = _ := by ring

/-- The frozen horizontal slope hypotheses bound the three nonconstant
coefficients needed for scalar-cell oscillation. -/
theorem horizontal_affine_coeff_bounds (L : Fin 4 → ℝ)
    {K a q Z t : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a) (hq : 0 < q) (hq₁ : q ≤ 1)
    (hZ : |Z| ≤ K) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h₃ : |L 3| ≤ K * (1 + a / q ^ 2))
    (hs : |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ K * (1 + a / q)) :
    |L 1| ≤ 2 * K ^ 2 * (1 + a / q ^ 2) ∧
      |L 2| ≤ 2 * K ^ 2 * (1 + a / q ^ 2) ∧
      |L 3| ≤ 2 * K ^ 2 * (1 + a / q ^ 2) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKsq : K ≤ K ^ 2 := by nlinarith only [hK]
  have hC : 0 ≤ 1 + a / q ^ 2 := by positivity
  have hq₂ : q ^ 2 ≤ q := by nlinarith only [hq, hq₁]
  have hratio : a / q ≤ a / q ^ 2 :=
    div_le_div_of_nonneg_left ha (pow_pos hq 2) hq₂
  have hs' : |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ K * (1 + a / q ^ 2) :=
    hs.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hratio) hK₀)
  have hs₁ : |L 1 - Z * L 3| ≤ K * (1 + a / q ^ 2) :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans hs'
  have hs₂ : |L 2 + t * L 3| ≤ K * (1 + a / q ^ 2) :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hs'
  have ht₁ : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h₁ : |L 1| ≤ K * (1 + a / q ^ 2) + K ^ 2 * (1 + a / q ^ 2) := by
    calc
      _ = |(L 1 - Z * L 3) + Z * L 3| := by congr 1; ring
      _ ≤ |L 1 - Z * L 3| + |Z * L 3| := abs_add_le _ _
      _ ≤ K * (1 + a / q ^ 2) + K * (K * (1 + a / q ^ 2)) := by
        rw [abs_mul]
        exact add_le_add hs₁ (mul_le_mul hZ h₃ (abs_nonneg _) hK₀)
      _ = _ := by ring
  have h₂ : |L 2| ≤ 2 * K * (1 + a / q ^ 2) := by
    calc
      _ = |(L 2 + t * L 3) - t * L 3| := by congr 1; ring
      _ ≤ |L 2 + t * L 3| + |t * L 3| := abs_sub _ _
      _ ≤ K * (1 + a / q ^ 2) + 1 * (K * (1 + a / q ^ 2)) := by
        rw [abs_mul]
        exact add_le_add hs₂ (mul_le_mul ht₁ h₃ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      _ = _ := by ring
  have hKK := mul_le_mul_of_nonneg_right hKsq hC
  exact ⟨by nlinarith only [h₁, hKK], by nlinarith only [h₂, hKK],
    by nlinarith only [h₃, hKK, mul_nonneg hK₀ hC]⟩

/-- Every true label meeting a scalar base cell lies in a fixed bounded
number of hidden terminal bins there. The centre is its collapsed predictor. -/
theorem scalar_cell_fit_bound_of_budget (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    {pc qc v D t τ R₀ K a q H χ ζ σ : ℝ}
    (hD : 0 < D) (hK : 0 ≤ K)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hp : |(b 0 - pc) / D| ≤ 1) (hv : |b 3 - v| ≤ χ)
    (he : |b 4 + b 0| ≤ ζ)
    (h₁ : |L 1| ≤ H) (h₂ : |L 2| ≤ H) (h₃ : |L 3| ≤ H)
    (hslope : |L 2 + t * L 3| ≤ K * (1 + a / q))
    (hbudget : D * K * (1 + a / q) ≤ 2 * K * a)
    (htτ : |t - τ| ≤ σ)
    (hR : |scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - R₀| ≤ σ)
    (hcontact : H * (χ + ζ) ≤ K * a)
    (hcell : H * σ * (1 + |v| + |pc| + D) ≤ K * a)
    (hfit : |b 2 + t * b 5 - affineValue L t (b 0 + t * b 3) (b 1 + t * b 4)| ≤ K * a) :
    |b 2 + t * b 5 - parameterValue L pc qc v D τ 0 R₀| ≤ 5 * K * a := by
  let p := (b 0 - pc) / D
  let r := (b 1 - qc) / D
  have hfull : |b 2 + t * b 5 - parameterValue L pc qc v D t p r| ≤
      K * a + H * (χ + ζ) := by
    rw [parameterValue_reconstruction L b pc qc v D t hD.ne']
    exact (abs_sub_le _ (affineValue L t (b 0 + t * b 3) (b 1 + t * b 4)) _).trans
      (add_le_add hfit (affineValue_contact_bound L b v t χ ζ H ht hv he h₂ h₃))
  have hcollapse : |parameterValue L pc qc v D t p r -
      parameterValue L pc qc v D t 0 (scalarParameter t p r)| ≤ 2 * K * a := by
    have h := parameterValue_fiber_bound L pc qc v D t p r K a q 1 hD.le hK hp hslope
    refine le_trans (b := D * K * (1 + a / q)) ?_ hbudget
    simpa only [mul_one, mul_assoc] using h
  have hosc : |parameterValue L pc qc v D t 0 (scalarParameter t p r) -
      parameterValue L pc qc v D τ 0 R₀| ≤ H * σ * (1 + |v| + |pc| + D) :=
    parameterValue_cell_oscillation L hD.le h₁ h₂ h₃ htτ hR
  have htri := abs_sub_le (b 2 + t * b 5)
    (parameterValue L pc qc v D t p r) (parameterValue L pc qc v D τ 0 R₀)
  have htri' := abs_sub_le (parameterValue L pc qc v D t p r)
    (parameterValue L pc qc v D t 0 (scalarParameter t p r))
    (parameterValue L pc qc v D τ 0 R₀)
  linarith only [hfull, hcollapse, hosc, htri, htri', hcontact, hcell]

/-- Every true label meeting a scalar base cell lies in a fixed bounded
number of hidden terminal bins there. The centre is its collapsed predictor. -/
theorem scalar_cell_fit_bound (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    {pc qc v D t τ R₀ K a q H χ ζ σ : ℝ}
    (hD : 0 < D) (hK : 0 ≤ K) (hDa : D ≤ a) (hq : 0 < q) (haq : a ≤ q)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hp : |(b 0 - pc) / D| ≤ 1) (hv : |b 3 - v| ≤ χ)
    (he : |b 4 + b 0| ≤ ζ)
    (h₁ : |L 1| ≤ H) (h₂ : |L 2| ≤ H) (h₃ : |L 3| ≤ H)
    (hslope : |L 2 + t * L 3| ≤ K * (1 + a / q))
    (htτ : |t - τ| ≤ σ)
    (hR : |scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - R₀| ≤ σ)
    (hcontact : H * (χ + ζ) ≤ K * a)
    (hcell : H * σ * (1 + |v| + |pc| + D) ≤ K * a)
    (hfit : |b 2 + t * b 5 - affineValue L t (b 0 + t * b 3) (b 1 + t * b 4)| ≤ K * a) :
    |b 2 + t * b 5 - parameterValue L pc qc v D τ 0 R₀| ≤ 5 * K * a := by
  have ha : 0 ≤ a := hD.le.trans hDa
  have hratio : a / q ≤ 1 := (div_le_one hq).mpr haq
  have hbudget : D * K * (1 + a / q) ≤ 2 * K * a := by
    calc
      _ ≤ a * K * 2 := by gcongr; linarith only [hratio]
      _ = _ := by ring
  exact scalar_cell_fit_bound_of_budget L b hD hK ht hp hv he h₁ h₂ h₃ hslope hbudget
    htτ hR hcontact hcell hfit

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates
