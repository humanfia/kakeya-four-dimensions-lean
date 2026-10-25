import Mathlib
import ChallengeDeps
import Submission.Obl.k4_plank_estimate.SetEstimateFinset
import Submission.Obl.k4_weighted_convex_tubes
import Submission.Obl.k4_plank_tube_realization
set_option linter.unusedVariables false

/-!
# `Submission.k4_plank_estimate`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_plank_estimate`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_plank_estimate/`
belong to this obligation.
-/

private theorem plank_mass_from_normalized {d W C K A P E : ℝ}
    (hd : 0 < d) (h : W / d ^ 2 ≤ C * (K * A) * P * (K * E / d ^ 3)) :
    W * d ≤ (C * K * K) * A * P * E := by
  have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ d ^ 3 by positivity)
  have hdne : d ≠ 0 := ne_of_gt hd
  field_simp at h'
  nlinarith only [h']

theorem Submission.k4_plank_estimate : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ) (A : ℝ) (J : Fin n → Finset (Fin D)), (∀ i : Fin n, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n), (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧ |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) → ∑ i ∈ S, ω i ≤ A * a * β) → (∀ i : Fin n, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) → ∑ i : Fin n, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p => ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ) := by
  obtain ⟨c, K, hc, hK, hrealize⟩ := Submission.k4_plank_tube_realization
  intro ε hε
  obtain ⟨η, hη, Cw, hCw, hweighted⟩ :=
    Submission.k4_weighted_convex_tubes Submission.Obl.k4_plank_estimate.unweighted_set_estimate_finset ε hε c hc
  refine ⟨η, hη, Cw * K * K, mul_pos (mul_pos hCw hK) hK, ?_⟩
  intro D hD n b u ω A J hbu hω hA hplank hJ
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  obtain ⟨x, v, Y, hv, hball, hmeas, hsub, hdens, hcluster, hunion⟩ :=
    hrealize D hD n b u ω A J hbu hω hA hplank
  have hdens' : ∀ i : Fin n,
      c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 ≤
        (MeasureTheory.volume (Y i)).toReal := by
    intro i
    have hpow : (D : ℝ) ^ (1 - η) = (D : ℝ) * (D : ℝ) ^ (-η) := by
      rw [sub_eq_add_neg, Real.rpow_add hDpos, Real.rpow_one]
    calc
      c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 =
          c * (D : ℝ) ^ (1 - η) / (D : ℝ) ^ 3 := by
        rw [hpow]
        field_simp
      _ ≤ c * ((J i).card : ℝ) / (D : ℝ) ^ 3 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hJ i) hc.le) (by positivity)
      _ ≤ (MeasureTheory.volume (Y i)).toReal := hdens i
  have hw := hweighted D hD n x v Y ω (K * A) hv hball hmeas hsub hω
    (mul_pos hK hA) hdens' hcluster
  have hcoefficient : 0 ≤ Cw * (K * A) * (D : ℝ) ^ ε := by positivity
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hunion hcoefficient)
  have hmass : (∑ i : Fin n, ω i) * (D : ℝ) ≤
      (Cw * K * K) * A * (D : ℝ) ^ ε *
        ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p =>
          ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) *
            (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ) :=
    plank_mass_from_normalized hDpos hw'
  calc
    (∑ i : Fin n, ω i * ((J i).card : ℝ)) ≤
        ∑ i : Fin n, ω i * (D : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hω i).le
      have hcard : (J i).card ≤ D := by
        simpa only [Finset.card_fin] using
          (Finset.card_le_card (Finset.subset_univ (J i)))
      exact_mod_cast hcard
    _ = (∑ i : Fin n, ω i) * (D : ℝ) := (Finset.sum_mul ..).symm
    _ ≤ _ := hmass
