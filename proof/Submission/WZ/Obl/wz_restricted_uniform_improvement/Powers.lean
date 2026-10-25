-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Powers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Estimates

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

/-- The coefficient naturally produced by a Frostman-controlled subfamily. -/
noncomputable def frostmanCoefficient (σ δ N : ℝ) : ℝ :=
  N ^ (σ / 2) * δ ^ (2 * σ)

theorem frostmanCoefficient_nonneg {σ δ N : ℝ} (hδ : 0 ≤ δ) (hN : 0 ≤ N) :
    0 ≤ frostmanCoefficient σ δ N := by
  unfold frostmanCoefficient
  positivity

/-- Counts and transverse scales telescope through a balanced three-level cover. -/
theorem frostmanCoefficient_telescope {σ δ τ ρ N Nτ Nρ : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hN : 0 < N) (hNτ : 0 < Nτ) (hNρ : 0 < Nρ) :
    frostmanCoefficient σ ρ Nρ * frostmanCoefficient σ (τ / ρ) (Nτ / Nρ) *
      frostmanCoefficient σ (δ / τ) (N / Nτ) = frostmanCoefficient σ δ N := by
  unfold frostmanCoefficient
  rw [Real.div_rpow hNτ.le hNρ.le, Real.div_rpow hτ.le hρ.le,
    Real.div_rpow hN.le hNτ.le, Real.div_rpow hδ.le hτ.le]
  have h₁ := (Real.rpow_pos_of_pos hNρ (σ / 2)).ne'
  have h₂ := (Real.rpow_pos_of_pos hNτ (σ / 2)).ne'
  have h₃ := (Real.rpow_pos_of_pos hρ (2 * σ)).ne'
  have h₄ := (Real.rpow_pos_of_pos hτ (2 * σ)).ne'
  field_simp

/-- Applying the better exponent at an intermediate ratio saves a scale power. -/
theorem intermediate_exponent_identity {δ τ ρ u w : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ) :
    ρ ^ u * (τ / ρ) ^ w * (δ / τ) ^ u = δ ^ u * (τ / ρ) ^ (w - u) := by
  rw [Real.div_rpow hτ.le hρ.le, Real.div_rpow hδ.le hτ.le,
    Real.div_rpow hτ.le hρ.le, Real.rpow_sub hτ, Real.rpow_sub hρ]
  have h₁ := (Real.rpow_pos_of_pos hρ u).ne'
  have h₂ := (Real.rpow_pos_of_pos hρ w).ne'
  have h₃ := (Real.rpow_pos_of_pos hτ u).ne'
  field_simp

/-- A single loss budget covers the separated-scale and aspect-ratio gains. -/
theorem gain_of_small_ratio {δ q c u w loss α : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hqc : q ≤ δ ^ c) (hwu : w ≤ u)
    (hbudget : loss + α ≤ c * (u - w)) :
    δ ^ (u - α) ≤ δ ^ (u + loss) * q ^ (w - u) := by
  calc
    _ ≤ δ ^ ((u + loss) + c * (w - u)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    _ = δ ^ (u + loss) * (δ ^ c) ^ (w - u) := by
      rw [Real.rpow_add hδ, Real.rpow_mul hδ.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hq hqc (sub_nonpos.mpr hwu))
      (Real.rpow_nonneg hδ.le _)

/-- Exact numerical form of the three-scale estimate in the paper's (6.4)--(6.8). -/
theorem three_scale_identity {σ δ τ ρ N Nτ Nρ u w ε : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hN : 0 < N) (hNτ : 0 < Nτ) (hNρ : 0 < Nρ) :
    (δ ^ ε * ρ ^ u * frostmanCoefficient σ ρ Nρ) *
      (δ ^ ε * (τ / ρ) ^ w * frostmanCoefficient σ (τ / ρ) (Nτ / Nρ)) *
      (δ ^ ε * (δ / τ) ^ u * frostmanCoefficient σ (δ / τ) (N / Nτ)) =
      δ ^ (u + 3 * ε) * (τ / ρ) ^ (w - u) * frostmanCoefficient σ δ N := by
  have he : δ ^ ε * δ ^ ε * δ ^ ε = δ ^ (3 * ε) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = (δ ^ ε * δ ^ ε * δ ^ ε) * (ρ ^ u * (τ / ρ) ^ w * (δ / τ) ^ u) *
        (frostmanCoefficient σ ρ Nρ * frostmanCoefficient σ (τ / ρ) (Nτ / Nρ) *
          frostmanCoefficient σ (δ / τ) (N / Nτ)) := by ring
    _ = δ ^ (3 * ε) * (δ ^ u * (τ / ρ) ^ (w - u)) * frostmanCoefficient σ δ N := by
      rw [he, intermediate_exponent_identity hδ hτ hρ,
        frostmanCoefficient_telescope hδ hτ hρ hN hNτ hNρ]
    _ = _ := by rw [Real.rpow_add hδ]; ring

/-- The gap between the input exponents produces a positive power gain. -/
theorem three_scale_gain {σ δ τ ρ N Nτ Nρ u w ε c α : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hN : 0 < N) (hNτ : 0 < Nτ) (hNρ : 0 < Nρ)
    (hsep : τ / ρ ≤ δ ^ c) (hwu : w ≤ u)
    (hbudget : 3 * ε + α ≤ c * (u - w)) :
    δ ^ (u - α) * frostmanCoefficient σ δ N ≤
      (δ ^ ε * ρ ^ u * frostmanCoefficient σ ρ Nρ) *
      (δ ^ ε * (τ / ρ) ^ w * frostmanCoefficient σ (τ / ρ) (Nτ / Nρ)) *
      (δ ^ ε * (δ / τ) ^ u * frostmanCoefficient σ (δ / τ) (N / Nτ)) := by
  rw [three_scale_identity hδ hτ hρ hN hNτ hNρ]
  exact mul_le_mul_of_nonneg_right
    (gain_of_small_ratio hδ hδ1 (div_pos hτ hρ) hsep hwu hbudget)
    (frostmanCoefficient_nonneg hδ.le hN.le)

theorem restrictedCoefficient_monomial {σ δ m N : ℝ}
    (hδ : 0 < δ) (hm : 0 < m) (hN : 0 < N) :
    restrictedCoefficient σ δ m N =
      N ^ (1 - σ) * δ ^ (2 - σ) * m ^ (3 * σ / 2 - 1) := by
  have hNpow : N * N ^ (-σ) = N ^ (1 - σ) := by
    rw [Real.rpow_sub hN, Real.rpow_one, Real.rpow_neg hN.le, div_eq_mul_inv]
  have hδpow : δ ^ 2 * δ ^ (-σ) = δ ^ (2 - σ) := by
    rw [Real.rpow_sub hδ, Real.rpow_two, Real.rpow_neg hδ.le, div_eq_mul_inv]
  rw [restrictedCoefficient_eq hm hN.le hδ.le, Real.mul_rpow hN.le hδ.le]
  calc
    _ = (N * N ^ (-σ)) * (δ ^ 2 * δ ^ (-σ)) * m ^ (3 * σ / 2 - 1) := by ring
    _ = _ := by rw [hNpow, hδpow]

theorem restrictedCoefficient_mono_count {σ δ m N N' : ℝ}
    (hσ : σ ≤ 1) (hδ : 0 < δ) (hm : 0 < m) (hN : 0 < N) (hNN : N ≤ N') :
    restrictedCoefficient σ δ m N ≤ restrictedCoefficient σ δ m N' := by
  rw [restrictedCoefficient_monomial hδ hm hN,
    restrictedCoefficient_monomial hδ hm (hN.trans_le hNN)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hN.le hNN (sub_nonneg.mpr hσ)) (Real.rpow_nonneg hδ.le _))
    (Real.rpow_nonneg hm.le _)

theorem restrictedCoefficient_rescale_count {σ δ m N θ : ℝ}
    (hδ : 0 < δ) (hm : 0 < m) (hN : 0 < N) (hθ : 0 < θ) :
    restrictedCoefficient σ δ m (θ * N) = θ ^ (1 - σ) * restrictedCoefficient σ δ m N := by
  rw [restrictedCoefficient_monomial hδ hm (mul_pos hθ hN),
    restrictedCoefficient_monomial hδ hm hN, Real.mul_rpow hθ.le hN.le]
  ring

/-- A power loss in the retained cardinality is paid for by a power loss
in the coefficient. This makes dense-shading refinements compatible with R. -/
theorem restrictedCoefficient_subfamily {σ δ m N k β ε : ℝ}
    (hσ : σ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 < m)
    (hN : 0 < N) (_hk : 0 < k) (hcount : δ ^ β * N ≤ k)
    (hbudget : β * (1 - σ) ≤ ε) :
    δ ^ ε * restrictedCoefficient σ δ m N ≤ restrictedCoefficient σ δ m k := by
  calc
    _ ≤ δ ^ (β * (1 - σ)) * restrictedCoefficient σ δ m N :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget)
        (restrictedCoefficient_nonneg hm.le hN.le hδ.le)
    _ = restrictedCoefficient σ δ m (δ ^ β * N) := by
      rw [restrictedCoefficient_rescale_count hδ hm hN (Real.rpow_pos_of_pos hδ _),
        Real.rpow_mul hδ.le]
    _ ≤ _ := restrictedCoefficient_mono_count hσ hδ hm
      (mul_pos (Real.rpow_pos_of_pos hδ _) hN) hcount

end WangZahlLot.Obl.wz_restricted_uniform_improvement
