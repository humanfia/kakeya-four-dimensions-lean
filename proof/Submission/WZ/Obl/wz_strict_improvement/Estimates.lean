-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.Estimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

abbrev Slab (u : Space) (t r : ℝ) : Set Space :=
  Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}

abbrev Dense {n : ℕ} (δ η : ℝ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

abbrev KatzTao {n : ℕ} (δ m : ℝ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (({i : Fin n | Tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal m * volume W

abbrev FrostmanSlab {n : ℕ} (δ l : ℝ) (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i : Fin n | Tube δ (x i) (v i) ⊆ Slab u t r}.ncard : ℝ) ≤
      ENNReal.ofReal (l * (n : ℝ)) * volume (Slab u t r)

abbrev DLower (σ ω a ε δ : ℝ) (n : ℕ) : ℝ :=
  a * δ ^ (ω + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ)

abbrev ELower (σ ω a ε δ m l : ℝ) (n : ℕ) : ℝ :=
  a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-σ)

/-- The small-error estimate, with precisely the quantifiers of the obligation. -/
abbrev D (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n →
      (∀ i : Fin n, ‖v i‖ = 1) →
      (∀ i : Fin n, Tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) →
      (∀ i j : Fin n, i ≠ j →
        volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      (∀ i : Fin n, MeasurableSet (Y i)) →
      (∀ i : Fin n, Y i ⊆ Tube δ (x i) (v i)) →
      Dense δ η Y → KatzTao δ (δ ^ (-η)) x v →
      FrostmanSlab δ (δ ^ (-η)) x v →
      ENNReal.ofReal (DLower σ ω a ε δ n) ≤ volume (⋃ i, Y i)

/-- The arbitrary-error estimate from the hypothesis of the obligation. -/
abbrev E (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n →
      (∀ i : Fin n, ‖v i‖ = 1) →
      (∀ i : Fin n, Tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) →
      (∀ i j : Fin n, i ≠ j →
        volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      (∀ i : Fin n, MeasurableSet (Y i)) →
      (∀ i : Fin n, Y i ⊆ Tube δ (x i) (v i)) →
      Dense δ η Y → KatzTao δ m x v → FrostmanSlab δ l x v →
      ENNReal.ofReal (ELower σ ω a ε δ m l n) ≤ volume (⋃ i, Y i)

theorem dense_mono {n : ℕ} {δ η₁ η₂ : ℝ} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η₁ ≤ η₂) (h : Dense δ η₁ Y) :
    Dense δ η₂ Y := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hη)
      (Nat.cast_nonneg n)) (sq_nonneg δ)

theorem katzTao_mono {n : ℕ} {δ m₁ m₂ : ℝ} {x v : Fin n → Space}
    (hm : m₁ ≤ m₂) (h : KatzTao δ m₁ x v) : KatzTao δ m₂ x v := by
  intro W hW
  exact (h W hW).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hm) _)

theorem frostmanSlab_mono {n : ℕ} {δ l₁ l₂ : ℝ} {x v : Fin n → Space}
    (hl : l₁ ≤ l₂) (h : FrostmanSlab δ l₁ x v) : FrostmanSlab δ l₂ x v := by
  intro u t r hu hr
  exact (h u t r hu hr).trans (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg n))) _)

/-- Specializing the two error constants gives an exact loss in the scale exponent. -/
theorem eLower_specialize (σ ω a ε η δ : ℝ) (n : ℕ) (hδ : 0 < δ) :
    ELower σ ω a ε δ (δ ^ (-η)) (δ ^ (-η)) n =
      DLower σ ω a (ε + η * (1 - σ / 2)) δ n := by
  have hδ₀ : 0 ≤ δ := hδ.le
  have hpow : (δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) = δ ^ (η / 2) := by
    rw [← Real.rpow_mul hδ₀, ← Real.rpow_add hδ]
    congr 1
    ring
  unfold ELower DLower
  rw [hpow, Real.mul_rpow (Real.rpow_nonneg hδ₀ _) (by positivity),
    ← Real.rpow_mul hδ₀, ← Real.rpow_neg_one, ← Real.rpow_mul hδ₀]
  have hexp : ω + ε + -η * (-1) + η / 2 * -σ = ω + (ε + η * (1 - σ / 2)) := by
    ring
  calc
    a * δ ^ (ω + ε) * δ ^ (-η * (-1)) * ((n : ℝ) * δ ^ 2) *
        (δ ^ (η / 2 * -σ) * ((n : ℝ) * δ) ^ (-σ)) =
      a * (δ ^ (ω + ε) * δ ^ (-η * (-1)) * δ ^ (η / 2 * -σ)) *
        ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ) := by ring
    _ = _ := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, hexp]

theorem dLower_mono_exponent {σ ω₁ ω₂ a ε₁ ε₂ δ : ℝ} (n : ℕ)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hω : ω₁ + ε₁ ≤ ω₂ + ε₂) :
    DLower σ ω₂ a ε₂ δ n ≤ DLower σ ω₁ a ε₁ δ n := by
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hω) ha

theorem specialization_loss_pos {σ η : ℝ} (hσ : σ ≤ (1 / 2 : ℝ)) (hη : 0 < η) :
    0 < η * (1 - σ / 2) :=
  mul_pos hη (by linarith)

theorem dLower_mono_coefficient {σ ω a₁ a₂ ε δ : ℝ} (n : ℕ)
    (hδ : 0 ≤ δ) (ha : a₁ ≤ a₂) :
    DLower σ ω a₁ ε δ n ≤ DLower σ ω a₂ ε δ n := by
  unfold DLower
  gcongr

/-- The direct specialization proves the estimate at the unchanged exponent. -/
theorem e_implies_d {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : E σ ω) : D σ ω := by
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, h⟩ := hE (ε / 2) (by positivity)
  let η := min η₀ (ε / 2)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub hdense hK hF
  have hδ₁ : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hm : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hδ hδ₁ (neg_nonpos.mpr hη.le)
  have hbound := h δ hδ hδmax (δ ^ (-η)) (δ ^ (-η)) hm hm n x v Y hn hv
    hball hdistinct hmeas hsub (dense_mono hδ hδ₁ (min_le_left _ _) hdense) hK hF
  rw [eLower_specialize σ ω a (ε / 2) η δ n hδ] at hbound
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
  apply dLower_mono_exponent n ha.le hδ hδ₁
  have hηε : η ≤ ε / 2 := min_le_right _ _
  have hση : 0 ≤ η * σ := mul_nonneg hη.le hσ
  nlinarith

theorem d_mono_omega {σ ω₁ ω₂ : ℝ} (hω : ω₁ ≤ ω₂) (h : D σ ω₁) : D σ ω₂ := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := h ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub hdense hK hF
  apply le_trans (ENNReal.ofReal_le_ofReal ?_)
    (h δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub hdense hK hF)
  exact dLower_mono_exponent n ha.le hδ (le_trans hδmax (by norm_num))
    (add_le_add_left hω ε)

/-- Any strict gain can be clipped to keep the improved exponent nonnegative. -/
theorem clip_improvement {σ ω g : ℝ} (hω : 0 < ω) (hg : 0 < g)
    (h : D σ (ω - g)) : ∃ g' : ℝ, 0 < g' ∧ g' ≤ ω ∧ D σ (ω - g') := by
  refine ⟨min g ω, lt_min hg hω, min_le_right _ _, ?_⟩
  exact d_mono_omega (sub_le_sub_left (min_le_left g ω) ω) h

end

end WangZahlLot.Obl.wz_strict_improvement
