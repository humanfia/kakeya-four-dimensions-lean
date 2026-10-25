-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FineScaleArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiberMultiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

/-- The full local Katz--Tao/Frostman expression at equal power errors. -/
theorem normalized_local_multiplicity_factor {δ u : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (η σ : ℝ) :
    δ ^ (-η) * ((δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * u) ^ σ =
      δ ^ (η * (σ / 2 - 1)) * u ^ σ := by
  have he : (δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * u = δ ^ (η / 2) * u := by
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    congr 2
    ring
  rw [he, Real.mul_rpow (Real.rpow_nonneg hδ.le _) hu, ← mul_assoc,
    ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  congr 2
  ring

/-- Equal power errors cost at most one copy of their exponent when sigma is nonnegative. -/
theorem normalized_local_multiplicity_factor_le {δ u η σ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu : 0 ≤ u) (hη : 0 ≤ η) (hσ : 0 ≤ σ) :
    δ ^ (-η) * ((δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * u) ^ σ ≤
      δ ^ (-η) * u ^ σ := by
  rw [normalized_local_multiplicity_factor hδ hu]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu _)
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)

/-- A rich intermediate-scale cover converts the fine-fiber count into the factor
that cancels with the middle and coarse estimates in Section 9. -/
theorem fine_count_of_rich_coarse_cover {δ ρ θ n N J k a ζ h : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hθ : 0 < θ) (hJ : 0 < J) (hk0 : 0 ≤ k)
    (hbalance : k * N ≤ δ ^ (-h) * n)
    (hrich : δ ^ (a - ζ) * (θ / ρ) ^ 2 * J ≤ N) :
    k * δ / ρ ≤ δ ^ (ζ - a - h) * (n / J * δ * ρ / θ ^ 2) := by
  have h1 := mul_le_mul_of_nonneg_left hrich hk0
  have h2 : k * (δ ^ (a - ζ) * (θ / ρ) ^ 2 * J) ≤ δ ^ (-h) * n := by
    exact h1.trans hbalance
  have hdense : 0 < δ ^ (a - ζ) * (θ / ρ) ^ 2 * J := by positivity
  have h3 := (le_div_iff₀ hdense).mpr h2
  have h4 := mul_le_mul_of_nonneg_right h3 (div_nonneg hδ.le hρ.le)
  calc
    k * δ / ρ = k * (δ / ρ) := by ring
    _ ≤ (δ ^ (-h) * n / (δ ^ (a - ζ) * (θ / ρ) ^ 2 * J)) * (δ / ρ) := h4
    _ = δ ^ (ζ - a - h) * (n / J * δ * ρ / θ ^ 2) := by
      have hp : δ ^ (-h) / δ ^ (a - ζ) = δ ^ (ζ - a - h) := by
        rw [← Real.rpow_sub hδ]
        congr 1
        ring
      calc
        _ = (δ ^ (-h) / δ ^ (a - ζ)) * (n / J * δ * ρ / θ ^ 2) := by field_simp
        _ = _ := by rw [hp]


/-- Raising the rich-cover count bound to the nonnegative Kakeya exponent
produces the strict factor `δ^(ζ * σ)` in the fine-scale multiplicity estimate. -/
theorem fine_multiplicity_of_rich_coarse_cover {δ ρ θ n N J k a ζ h σ ε C M ω : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hθ : 0 < θ) (hJ : 0 < J)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hbalance : k * N ≤ δ ^ (-h) * n)
    (hrich : δ ^ (a - ζ) * (θ / ρ) ^ 2 * J ≤ N)
    (hmult : M ≤ C * δ ^ (-ε) * (δ / ρ) ^ (-ω) * (k * δ / ρ) ^ σ) :
    M ≤ C * δ ^ (σ * ζ - ε - σ * (a + h)) * (δ / ρ) ^ (-ω) *
      (n / J * δ * ρ / θ ^ 2) ^ σ := by
  have hc := fine_count_of_rich_coarse_cover hδ hρ hθ hJ hk hbalance hrich
  have hcσ := Real.rpow_le_rpow (by positivity : 0 ≤ k * δ / ρ) hc hσ
  rw [Real.mul_rpow (Real.rpow_nonneg hδ.le _) (by positivity),
    ← Real.rpow_mul hδ.le] at hcσ
  have hp := mul_le_mul_of_nonneg_left hcσ
    (by positivity : 0 ≤ C * δ ^ (-ε) * (δ / ρ) ^ (-ω))
  apply hmult.trans (hp.trans_eq _)
  have he : δ ^ (-ε) * δ ^ ((ζ - a - h) * σ) =
      δ ^ (σ * ζ - ε - σ * (a + h)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = C * (δ ^ (-ε) * δ ^ ((ζ - a - h) * σ)) * (δ / ρ) ^ (-ω) *
        (n / J * δ * ρ / θ ^ 2) ^ σ := by ring
    _ = _ := by rw [he]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
