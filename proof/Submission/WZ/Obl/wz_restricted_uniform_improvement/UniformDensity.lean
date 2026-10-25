-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.UniformDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.CompactScale
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Powers

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- The restricted estimate with a density lower bound on each shading. -/
def IndividuallyRestricted (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η x v Y →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

/-- Uniform density on each tube suffices for the original averaged-density estimate. -/
theorem restricted_of_individually {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 2 / 3) (hω : 0 ≤ ω)
    (h : IndividuallyRestricted σ ω) : Restricted σ ω := by
  apply restricted_of_asymptotic hσ hσ1 hω
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, hbound⟩ := h (ε / 2) (by positivity)
  let η := min (η₀ / 4) (ε / 8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη₀' : 4 * η ≤ η₀ := by have := min_le_left (η₀ / 4) (ε / 8); dsimp [η]; linarith
  have hηε : 8 * η ≤ ε := by have := min_le_right (η₀ / 4) (ε / 8); dsimp [η]; linarith
  let δ₀ := (1 / 768 : ℝ) ^ η⁻¹
  refine ⟨a, ha, η, hη, δ₀, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro δ hδ hδ100 hδsmall m hm n x v Y hA hK hF
  have hδ1 : δ ≤ 1 := by linarith
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hsmall : δ ^ η ≤ 1 / 768 := by
    calc
      _ ≤ ((1 / 768 : ℝ) ^ η⁻¹) ^ η := Real.rpow_le_rpow hδ.le hδsmall hη.le
      _ = _ := Real.rpow_inv_rpow (by norm_num) hη.ne'
  obtain ⟨k, hk, f, hcard, hshade⟩ := extract_uniform_density_fin hδ hδ1 hA
  have hcard' : (n : ℝ) * δ ^ (2 * η) ≤ (k : ℝ) := by
    calc
      _ = ((n : ℝ) * δ ^ η) * δ ^ η := by
        rw [show 2 * η = η + η by ring, Real.rpow_add hδ]
        ring
      _ ≤ (768 * (k : ℝ)) * δ ^ η :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hδ.le _)
      _ ≤ (k : ℝ) := by
        have hh : 768 * δ ^ η ≤ 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg k)]
  have hdenpow : δ ^ η₀ ≤ δ ^ η / 2 := by
    calc
      _ ≤ δ ^ (2 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ η * δ ^ η := by rw [show 2 * η = η + η by ring, Real.rpow_add hδ]
      _ ≤ δ ^ η * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hδ.le _)
      _ = _ := by ring
  have hden : ∀ j, ENNReal.ofReal (δ ^ η₀ * δ ^ 2) ≤ volume (Y (f j)) := by
    intro j
    apply le_trans (ENNReal.ofReal_le_ofReal _) (hshade j)
    calc
      _ ≤ (δ ^ η / 2) * δ ^ 2 := mul_le_mul_of_nonneg_right hdenpow (sq_nonneg δ)
      _ = _ := by ring
  have hFcard : δ ^ (-η) * (n : ℝ) ≤ δ ^ (-η₀) * (k : ℝ) := by
    calc
      _ ≤ δ ^ (-η₀ + 2 * η) * (n : ℝ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg n)
      _ = δ ^ (-η₀) * ((n : ℝ) * δ ^ (2 * η)) := by rw [Real.rpow_add hδ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard' (Real.rpow_nonneg hδ.le _)
  have hA' : Admissible δ η₀ (x ∘ f) (v ∘ f) (Y ∘ f) :=
    admissible_subfamily f hk hA (dense_of_individual hδ.le hden)
  have hv := hbound δ hδ hδ100 m hm k (x ∘ f) (v ∘ f) (Y ∘ f) hA' hden
    (katz_subfamily f hK) (frostman_subfamily f hFcard hF)
  have hcoef : δ ^ (ε / 2) * restrictedCoefficient σ δ m (n : ℝ) ≤
      restrictedCoefficient σ δ m (k : ℝ) :=
    restrictedCoefficient_subfamily (β := 2 * η) (ε := ε / 2) (by linarith) hδ hδ1 hm0
      (Nat.cast_pos.mpr hA.1) (Nat.cast_pos.mpr hk)
      (by simpa only [mul_comm] using hcard') (by nlinarith only [hηε, mul_nonneg hη.le hσ, hη.le])
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hv.trans (measure_mono (subfamily_union_subset f Y)))
  calc
    _ = (a * δ ^ (ω + ε / 2)) * (δ ^ (ε / 2) * restrictedCoefficient σ δ m (n : ℝ)) := by
      rw [show ω + ε = (ω + ε / 2) + ε / 2 by ring, Real.rpow_add hδ]
      unfold restrictedCoefficient
      ring
    _ ≤ (a * δ ^ (ω + ε / 2)) * restrictedCoefficient σ δ m (k : ℝ) :=
      mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = _ := by unfold restrictedCoefficient; ring

theorem Restricted.individually {σ ω : ℝ} (h : Restricted σ ω) :
    IndividuallyRestricted σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, hbound⟩ := h ε hε
  exact ⟨a, ha, η, hη, fun δ hδ hδ100 m hm n x v Y hA _ hK hF =>
    hbound δ hδ hδ100 m hm n x v Y hA hK hF⟩

theorem restricted_iff_individually {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 2 / 3) (hω : 0 ≤ ω) :
    Restricted σ ω ↔ IndividuallyRestricted σ ω :=
  ⟨Restricted.individually, restricted_of_individually hσ hσ1 hω⟩

end WangZahlLot.Obl.wz_restricted_uniform_improvement
