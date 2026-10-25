/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingApply.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/MatchingApply.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Interface

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set

/-- The sheet hypotheses of the matching statement for one list, with degree two,
measured against a common reference `f₀` at scale `A` on the real unit ball. -/
def MatchSheets {n : ℕ} (f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ)
    (P : Fin n → MvPolynomial (Fin 4) ℂ) (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (A : ℝ) : Prop :=
  ∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) (Metric.ball 0 4) ∧
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f i z)) (P i) = 0) ∧
    ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f i (emb x)).im = 0 ∧ ‖f i (emb x) - f₀ x‖ ≤ A

/-- The discrepancy events of the matching statement. -/
def MatchEvents {n₁ n₂ : ℕ} (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (near far : ℝ) :
    Set ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) :=
  {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ near ∧
    ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧ far ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}

/-- The conclusion of the matching hypothesis in unnormalized form, for fixed `d₀, ε₀, R₀`:
a finite measure carried by discrepancy events, with per-index base densities at most `ρ`,
has total mass at most `ρ * max n₁ n₂ * R ^ (-ε)`. -/
def MatchBound (d₀ ε₀ R₀ : ℝ) : Prop :=
  ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
    ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ) (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ)
      (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (ρ : ℝ)
      (μ : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))) [IsFiniteMeasure μ],
      (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) →
      MatchSheets f₁ P₁ f₀ (M * R ^ ε) → MatchSheets f₂ P₂ f₀ (M * R ^ ε) → 0 ≤ ρ →
      (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal ρ * volume U) →
      (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal ρ * volume U) →
      μ (MatchEvents f₁ f₂ (M * R ^ (-1 + ε)) (M * R ^ (-ε)))ᶜ = 0 →
      μ univ ≤ ENNReal.ofReal (ρ * (max n₁ n₂ : ℕ) * R ^ (-ε))

/-- The matching hypothesis, specialized to degree two, in unnormalized form. -/
theorem matching_unnormalized (hM : Matching) (d₀ : ℝ) (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ MatchBound d₀ ε₀ R₀ := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmain⟩ := hM 2 d₀ hd0 hd1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hMpos hε hεε₀ n₁ n₂ f₁ f₂ P₁ P₂ f₀ ρ μ _ hn₁ hn₂ hs₁ hs₂ hρ hm₁ hm₂ hev
  by_contra hcon
  push Not at hcon
  set m : ENNReal := μ univ with hm_def
  have hmfin : m ≠ ⊤ := measure_ne_top μ univ
  have hmpos : 0 < m := lt_of_le_of_lt (zero_le) hcon
  have hmne : m ≠ 0 := hmpos.ne'
  -- nonemptiness of the index types
  have hne : Nonempty ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : μ univ = 0 := by simp [Set.univ_eq_empty_iff.mpr h]
    exact hmne this
  obtain ⟨⟨⟨i₁, i₂⟩, _⟩⟩ := hne
  have hn₁pos : 0 < n₁ := Fin.pos i₁
  have hn₂pos : 0 < n₂ := Fin.pos i₂
  have hRpos : 0 < R := by linarith
  -- the normalized measure
  set μ' : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) := m⁻¹ • μ with hμ'
  have hμ'univ : μ' univ = 1 := by
    simp only [hμ', Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmne hmfin
  -- the real mass
  set mr : ℝ := m.toReal with hmr
  have hmr_pos : 0 < mr := ENNReal.toReal_pos hmne hmfin
  have hm_eq : m = ENNReal.ofReal mr := (ENNReal.ofReal_toReal hmfin).symm
  have hcon' : ρ * (max n₁ n₂ : ℕ) * R ^ (-ε) < mr := by
    have := hcon
    rw [hm_eq] at this
    exact (ENNReal.ofReal_lt_ofReal_iff hmr_pos).mp this
  have hRε : 0 < R ^ ε := Real.rpow_pos_of_pos hRpos ε
  have key : ∀ n : ℕ, 0 < n → n ≤ max n₁ n₂ → ∀ (a : ENNReal), a ≤ ENNReal.ofReal ρ →
      m⁻¹ * a ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) := by
    intro n hn hnle a ha
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : ρ * n * R ^ (-ε) ≤ ρ * (max n₁ n₂ : ℕ) * R ^ (-ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRpos.le _)
      apply mul_le_mul_of_nonneg_left _ hρ
      exact_mod_cast hnle
    have h2 : ρ ≤ mr * (R ^ ε * (1 / (n : ℝ))) := by
      have h3 : ρ * n * R ^ (-ε) < mr := lt_of_le_of_lt h1 hcon'
      rw [Real.rpow_neg hRpos.le] at h3
      have h4 : ρ = ρ * n * (R ^ ε)⁻¹ * (R ^ ε * (1 / (n : ℝ))) := by
        field_simp
      rw [h4]
      exact mul_le_mul_of_nonneg_right h3.le (by positivity)
    calc m⁻¹ * a ≤ m⁻¹ * ENNReal.ofReal ρ := mul_le_mul_right ha _
      _ ≤ m⁻¹ * ENNReal.ofReal (mr * (R ^ ε * (1 / (n : ℝ)))) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal h2) _
      _ = m⁻¹ * (m * ENNReal.ofReal (R ^ ε * (1 / (n : ℝ)))) := by
          rw [ENNReal.ofReal_mul hmr_pos.le, ← hm_eq]
      _ = ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hmne hmfin, one_mul]
  have happ := hmain R M ε hR hMpos hε hεε₀ n₁ n₂ f₁ f₂ P₁ P₂ f₀
    (fun _ => 1 / (n₁ : ℝ)) (fun _ => 1 / (n₂ : ℝ)) μ'
  simp only at happ
  apply happ hn₁ hn₂
  · intro i
    obtain ⟨a, b, c, d, e⟩ := hs₁ i
    exact ⟨a, b, c, d, e⟩
  · intro i
    obtain ⟨a, b, c, d, e⟩ := hs₂ i
    exact ⟨a, b, c, d, e⟩
  · intro i; positivity
  · intro i; positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [hμ'univ]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  · rw [hμ'univ]
  · intro i U hU
    simp only [hμ', Measure.smul_apply, smul_eq_mul]
    calc m⁻¹ * μ {p | p.1.1 = i ∧ p.2 ∈ U}
        ≤ m⁻¹ * (ENNReal.ofReal ρ * volume U) := mul_le_mul_right (hm₁ i U hU) _
      _ = (m⁻¹ * ENNReal.ofReal ρ) * volume U := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (R ^ ε * (1 / (n₁ : ℝ))) * volume U :=
          mul_le_mul_left (key n₁ hn₁pos (le_max_left _ _) _ le_rfl) _
  · intro i U hU
    simp only [hμ', Measure.smul_apply, smul_eq_mul]
    calc m⁻¹ * μ {p | p.1.2 = i ∧ p.2 ∈ U}
        ≤ m⁻¹ * (ENNReal.ofReal ρ * volume U) := mul_le_mul_right (hm₂ i U hU) _
      _ = (m⁻¹ * ENNReal.ofReal ρ) * volume U := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (R ^ ε * (1 / (n₂ : ℝ))) * volume U :=
          mul_le_mul_left (key n₂ hn₂pos (le_max_right _ _) _ le_rfl) _
  · have : μ' (MatchEvents f₁ f₂ (M * R ^ (-1 + ε)) (M * R ^ (-ε)))ᶜ = 0 := by
      simp only [hμ', Measure.smul_apply, smul_eq_mul, hev, mul_zero]
    exact this

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
