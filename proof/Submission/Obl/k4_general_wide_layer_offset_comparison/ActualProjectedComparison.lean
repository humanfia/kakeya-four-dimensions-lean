import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonBuild
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonAsymptotic
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedCoefficients
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedLongDomain

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ActualProjectedComparison.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Actual simultaneous projected layers have a long-domain comparison,
with a fixed primitive mesh exponent and power-small ORIGINAL bad mass.
All source atlases and all numerical comparison inputs are constructed. -/
theorem actual_projected_comparison (hp : p.Valid)
    (hM : Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Matching)
    {sc sf m u : ℝ} (hsc : 0 < sc) (hsf : sc ≤ sf) (hsfU : sf ≤ p.U)
    (hm : 0 < m) (hu : 0 < u) (hgap : sf - sc ≤ u)
    (H : ℕ → ℝ) (σ : ℕ → Measure (α × ℝ)) (A₀ A₁ : ℕ → ProjectedLayer α)
    (hH : ∀ k, 1 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    (hσ : ∀ k, σ k ≤ p.ρ k)
    (hvalid₀ : ∀ k, (A₀ k).Valid p k sc m (H k))
    (hvalid₁ : ∀ k, (A₁ k).Valid p k sf m (H k))
    (hcover₀ : ∀ k, (A₀ k).Covers (σ k)) (hcover₁ : ∀ k, (A₁ k).Covers (σ k)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ k in atTop,
      ∃ f : ProjectedComparisonFrame p k sc sf m (H k)
        (longTime (A₀ k).β (A₁ k).β) (longSlope (A₀ k).β (A₁ k).β)
        (longWidth (A₀ k).β (A₁ k).β) (σ k),
        f.coarse = A₀ k ∧ f.fine = A₁ k ∧ f.r = 80 * C ∧
        σ k (f.bad (4 * H k * p.N k ^ (-sc) * p.N k ^ (10 / (1 - p.d) * u))) ≤
          ENNReal.ofReal (p.N k ^ (-c)) := by
  have hsf0 : 0 < sf := hsc.trans_le hsf
  have hL : 0 ≤ p.ℓ * sf := mul_nonneg hp.transverse_pos.le hsf0.le
  let C := 3 + m + sf + 5 * (p.ℓ * sf)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hmC : m ≤ C := by dsimp [C]; linarith
  have hsfC : sf ≤ C := by dsimp [C]; linarith
  have hCL : p.ℓ * sf + 2 ≤ C := by dsimp [C]; linarith
  have hCcoeff : 1 + 5 * (p.ℓ * sf) ≤ C := by dsimp [C]; linarith
  have hrp : 0 < 80 * C := by linarith
  have hscinv : 0 < sc⁻¹ := inv_pos.mpr hsc
  have hminv : 0 < m⁻¹ := inv_pos.mpr hm
  have hrinv : 0 < (80 * C)⁻¹ := inv_pos.mpr hrp
  let R := 2 + 80 * C + sf + m + sc⁻¹ + m⁻¹ + (80 * C)⁻¹
  have hR : 1 < R := by dsimp [R]; linarith
  have hrR : 80 * C ≤ R := by dsimp [R]; linarith
  have hsfR : sf ≤ R := by dsimp [R]; linarith
  have hmR : m ≤ R := by dsimp [R]; linarith
  have hRsc : R⁻¹ ≤ sc := by
    have hh := inv_anti₀ hscinv (show sc⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  have hRm : R⁻¹ ≤ m := by
    have hh := inv_anti₀ hminv (show m⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  have hRr : R⁻¹ ≤ 80 * C := by
    have hh := inv_anti₀ hrinv (show (80 * C)⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  obtain ⟨c, hc, hbad⟩ := p.eventually_wide_comparison_bad_small hp hM hu hgap H hH hKH hsub
  have hcoeff := eventually_projected_coefficients hp.scale hp.scale_limit hH hsub hL
  refine ⟨c, hc, C, hC, ?_⟩
  filter_upwards [hbad, hsub 1 (by norm_num), hcoeff, hp.prepared R hR, hp.caps R hR]
    with k hbadk hHk hcoeffk hprepk hcapsk
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hHp : 0 < H k := zero_lt_one.trans_le (hH k)
  have hK0 : 0 ≤ p.K k := zero_le_one.trans (hp.subpower.1 k)
  have hv₀ := hvalid₀ k
  have hv₁ := hvalid₁ k
  have hpow : p.N k ^ (-(p.ℓ * sf)) ≤ p.N k ^ (-(p.ℓ * sc)) :=
    Real.rpow_le_rpow_of_exponent_le hN1
      (neg_le_neg (mul_le_mul_of_nonneg_left hsf hp.transverse_pos.le))
  have hlo₀ : p.N k ^ (-(p.ℓ * sf)) / H k ≤ (A₀ k).β := by
    have hb₀ : p.N k ^ (-(p.ℓ * sc)) / H k ≤ (A₀ k).β := by
      simpa only [neg_mul] using hv₀.2.1
    exact (div_le_div_of_nonneg_right hpow hHp.le).trans hb₀
  have hlo₁ : p.N k ^ (-(p.ℓ * sf)) / H k ≤ (A₁ k).β := by
    simpa only [neg_mul] using hv₁.2.1
  have hhi₀ : (A₀ k).β ≤ H k := by
    calc
      _ ≤ H k * p.N k ^ (-p.ℓ * sc) := hv₀.2.2.1
      _ ≤ H k * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN1
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.transverse_pos.le) hsc.le)) hHp.le
      _ = _ := mul_one _
  have hhi₁ : (A₁ k).β ≤ H k := by
    calc
      _ ≤ H k * p.N k ^ (-p.ℓ * sf) := hv₁.2.2.1
      _ ≤ H k * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN1
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.transverse_pos.le) hsf0.le)) hHp.le
      _ = _ := mul_one _
  have hHN : H k ≤ p.N k := by simpa only [Real.rpow_one] using hHk
  have hdom := long_domain_power_bounds hN1 (hH k) hHN hL hCL hv₀.1 hv₁.1 hlo₀ hlo₁ hhi₀ hhi₁
  have hHX : H k ≤ p.N k ^ C := by
    calc
      _ ≤ p.N k := by simpa only [Real.rpow_one] using hHk
      _ = p.N k ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hC
  have hc₀ : ∀ i e, |((A₀ k).G i).coeff e| ≤ p.N k ^ C := by
    intro i e
    have hi := hv₀.2.2.2.2.2.1 i
    exact (hcoeffk _ _ _ _ hi.2.1 hi.1 hv₀.1 hlo₀ hi.2.2.1 e).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hCcoeff)
  have hc₁ : ∀ i e, |((A₁ k).G i).coeff e| ≤ p.N k ^ C := by
    intro i e
    have hi := hv₁.2.2.2.2.2.1 i
    exact (hcoeffk _ _ _ _ hi.2.1 hi.1 hv₁.1 hlo₁ hi.2.2.1 e).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hCcoeff)
  have hat := hprepk sc hRsc (hsf.trans hsfU)
  obtain ⟨a₀⟩ := (A₀ k).exists_sourceAtlas p hp.basic hv₀ (hH k)
    hdom.time_pos hdom.time_le_one hdom.width_pos hdom.width_coarse hdom.coarse_slope
    hat hK0 hRm hmR (σ k) (hσ k) (hcover₀ k)
  obtain ⟨a₁⟩ := (A₁ k).exists_sourceAtlas p hp.basic hv₁ (hH k)
    hdom.time_pos hdom.time_le_one hdom.width_pos hdom.width_fine hdom.fine_slope
    hat hK0 hRm hmR (σ k) (hσ k) (hcover₁ k)
  have hnative : ∀ s : ℝ, 0 ≤ s → s ≤ sf → ∀ (q : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) (80 * C) ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / p.N k ^ (-s)⌋ = j ∧
        ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = v₁} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * (80 * C) - p.d * s)) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = v₁} := by
    intro s hs hss q j v₁
    exact (hcapsk (80 * C) s m hRr hrR hs (hss.trans hsfR) hRm hmR).2.2 true q j v₁
  let f := ProjectedComparisonFrame.of_power_bounds hp hC hsc.le hsf hsfC hm.le hmC
    (hH k) (hKH k) hHX hdom.time_pos hdom.slope_pos hdom.width_pos hdom.motion
    hdom.time_lower hdom.time_upper hdom.slope_upper hdom.width_lower hdom.width_upper
    a₀ a₁ ((hσ k).trans (hp.basic k).2.2.2.2.1) hc₀ hc₁ hnative
  exact ⟨f, rfl, rfl, rfl, hbadk _ _ _ _ f⟩

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
