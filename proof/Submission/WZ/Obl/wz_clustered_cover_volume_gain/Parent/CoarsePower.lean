-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarsePower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.NeighborhoodMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseClose

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Normalized E with explicit coefficient bounds supplies the coarse power
estimate. The favorable negative power of the convex coefficient is discarded. -/
theorem coarse_estimate_power {δ b c κ M l N Cm Cl u v σ ω ε : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hc : 0 < c) (hκ : 0 ≤ κ)
    (hM : 1 ≤ M) (hl : 0 < l) (hN : 0 < N) (hCm : 0 < Cm) (hCl : 0 < Cl)
    (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hδb : δ ≤ b)
    (hMu : M ≤ Cm * δ ^ (-u)) (hlv : l ≤ Cl * δ ^ (-v)) :
    (κ * c ^ (ω + ε + 2 - σ) * Cm ^ (-2 : ℝ) * Cl ^ (-σ)) *
        δ ^ (2 * u + σ * v + ε) * b ^ ω * (N * b) ^ (-σ) * (N * b ^ 2) ≤
      κ * (c * b) ^ (ω + ε) * (M⁻¹) ^ 2 * (N * (c * b) ^ 2) *
        (M ^ (-(3 / 2 : ℝ)) * l * (N * (c * b))) ^ (-σ) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMp : M ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM (by norm_num)
  have hdrop : (l * (N * (c * b))) ^ (-σ) ≤
      (M ^ (-(3 / 2 : ℝ)) * l * (N * (c * b))) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hσ)
    calc
      _ ≤ 1 * l * (N * (c * b)) := by gcongr
      _ = _ := by ring
  have hMinv : Cm ^ (-2 : ℝ) * δ ^ (2 * u) ≤ (M⁻¹) ^ 2 := by
    have hh := Real.rpow_le_rpow_of_nonpos hM0 hMu (by norm_num : (-2 : ℝ) ≤ 0)
    rw [Real.mul_rpow hCm.le (by positivity), ← Real.rpow_mul hδ.le,
      show -u * (-2) = 2 * u by ring] at hh
    simpa only [Real.rpow_neg hM0.le, Real.rpow_two, inv_pow] using hh
  have hlinv : Cl ^ (-σ) * δ ^ (σ * v) ≤ l ^ (-σ) := by
    have hh := Real.rpow_le_rpow_of_nonpos hl hlv (neg_nonpos.mpr hσ)
    rw [Real.mul_rpow hCl.le (by positivity), ← Real.rpow_mul hδ.le,
      show -v * -σ = σ * v by ring] at hh
    exact hh
  have hbε : δ ^ ε ≤ b ^ ε := Real.rpow_le_rpow hδ.le hδb hε
  have hnum : (κ * c ^ (ω + ε + 2 - σ) * Cm ^ (-2 : ℝ) * Cl ^ (-σ)) *
      δ ^ (2 * u + σ * v + ε) * b ^ ω * (N * b) ^ (-σ) * (N * b ^ 2) =
      κ * c ^ (ω + ε) * c ^ (-σ) * c ^ 2 * b ^ ω *
        (Cm ^ (-2 : ℝ) * δ ^ (2 * u)) * (Cl ^ (-σ) * δ ^ (σ * v)) * δ ^ ε *
        (N * b) ^ (-σ) * (N * b ^ 2) := by
    rw [show ω + ε + 2 - σ = (ω + ε) + -σ + 2 by ring,
      Real.rpow_add hc, Real.rpow_add hc, Real.rpow_two,
      Real.rpow_add hδ, Real.rpow_add hδ]
    ring
  rw [hnum]
  calc
    _ ≤ κ * c ^ (ω + ε) * c ^ (-σ) * c ^ 2 * b ^ ω *
        (M⁻¹) ^ 2 * l ^ (-σ) * b ^ ε * (N * b) ^ (-σ) * (N * b ^ 2) := by gcongr
    _ = κ * (c * b) ^ (ω + ε) * (M⁻¹) ^ 2 * (N * (c * b) ^ 2) *
        (l * (N * (c * b))) ^ (-σ) := by
      rw [Real.mul_rpow hc.le hb.le, Real.rpow_add hb,
        show N * (c * b) = c * (N * b) by ring,
        Real.mul_rpow hl.le (by positivity), Real.mul_rpow hc.le (by positivity)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdrop (by positivity)

/-- The linear occupied count can differ from the count in the slab factor. -/
theorem coarse_estimate_power_selected {δ b c κ M l N P Cm Cl u v σ ω ε : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hc : 0 < c) (hκ : 0 ≤ κ)
    (hM : 1 ≤ M) (hl : 0 < l) (hN : 0 < N) (hP : 0 ≤ P)
    (hCm : 0 < Cm) (hCl : 0 < Cl) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hδb : δ ≤ b)
    (hMu : M ≤ Cm * δ ^ (-u)) (hlv : l ≤ Cl * δ ^ (-v)) :
    (κ * c ^ (ω + ε + 2 - σ) * Cm ^ (-2 : ℝ) * Cl ^ (-σ)) *
        δ ^ (2 * u + σ * v + ε) * b ^ ω * (N * b) ^ (-σ) * (P * b ^ 2) ≤
      κ * (c * b) ^ (ω + ε) * (M⁻¹) ^ 2 * (P * (c * b) ^ 2) *
        (M ^ (-(3 / 2 : ℝ)) * l * (N * (c * b))) ^ (-σ) := by
  have hh := mul_le_mul_of_nonneg_right
    (coarse_estimate_power (ω := ω) hδ hb hc hκ hM hl hN hCm hCl hσ hε hδb hMu hlv)
    (div_nonneg hP hN.le)
  convert hh using 1 <;> field_simp

/-- The coarse estimate controls a uniform multiplicity level on packet unions,
with every loss recorded as a power of the original scale. -/
theorem coarse_multiplicity_power {δ b c κ K l Cm Cl u v σ ω ε A : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb3 : b ≤ 1 / 3) (hc : 0 < c) (hκ : 0 < κ)
    (hK : 1 ≤ K) (hl : 0 < l) (hCm : 0 < Cm) (hCl : 0 < Cl)
    (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hδb : δ ≤ b) (hA : 0 ≤ A)
    (hKu : K ≤ Cm * δ ^ (-u)) (hlv : l ≤ Cl * δ ^ (-v))
    {N : ℕ} (hN : 0 < N) (Q : Fin N → Set Space)
    (z : Fin N → Space) (e : Fin N → Space ≃ₗᵢ[ℝ] Space)
    (hsub : ∀ j, thickening b (Q j) ⊆ factoringCarrier b (z j) (e j))
    (hmult : ∀ p ∈ ⋃ j, Q j, ENNReal.ofReal A ≤ multiplicity Q p)
    (hvol : ENNReal.ofReal (κ * (c * b) ^ (ω + ε) * (K⁻¹) ^ 2 *
        (N * (c * b) ^ 2) * (K ^ (-(3 / 2 : ℝ)) * l * (N * (c * b))) ^ (-σ)) ≤
      volume (⋃ j, thickening b (Q j))) :
    A ≤ (360 / (κ * c ^ (ω + ε + 2 - σ) * Cm ^ (-2 : ℝ) * Cl ^ (-σ))) *
      δ ^ (-(2 * u + σ * v + ε)) * (b ^ (-ω) * (N * b) ^ σ) := by
  let C := κ * c ^ (ω + ε + 2 - σ) * Cm ^ (-2 : ℝ) * Cl ^ (-σ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hNb : 0 < (N : ℝ) * b := by positivity
  have hcoef : 0 < C * δ ^ (2 * u + σ * v + ε) * b ^ ω * (N * b) ^ (-σ) := by positivity
  have hbound := coarse_multiplicity_bound_of_union_lower hb hb3 hcoef hA hN Q z e hsub hmult
    ((ENNReal.ofReal_le_ofReal (coarse_estimate_power hδ hb hc hκ.le hK hl
      (Nat.cast_pos.mpr hN) hCm hCl hσ hε hδb hKu hlv)).trans hvol)
  refine hbound.trans_eq ?_
  change 360 / (C * δ ^ (2 * u + σ * v + ε) * b ^ ω * (N * b) ^ (-σ)) = _
  rw [Real.rpow_neg hδ.le, Real.rpow_neg hb.le, Real.rpow_neg hNb.le]
  dsimp only [C]
  field_simp

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
