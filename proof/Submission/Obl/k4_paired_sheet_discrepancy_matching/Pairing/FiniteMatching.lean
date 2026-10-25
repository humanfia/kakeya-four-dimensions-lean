/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/FiniteMatching.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.LightThresholds
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.PowerGeometry
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleBand

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

def DiscSetup.discrepancyEvent {ι Λ Ω : Type*} [MeasurableSpace Ω]
    (S : DiscSetup ι Λ Ω) (M₀ : ℝ) : Set Ω :=
  {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
    M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖}

noncomputable def matchingBadConstant {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData) : ℝ :=
  4 * (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
    (1 - p.decay) * 5324

namespace NormalizationStep.TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

noncomputable def matchingRadius (_s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε) : ℝ :=
  (Nk ^ a) ^ (-3 : ℝ)

noncomputable def matchingThreshold {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀) : ℝ :=
  2 * s.sheetError * (Nk ^ a) ^ p.size

theorem matching_grid_pos (hcv : cv) (hNk : 1 ≤ Nk) (ha : 0 < a)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a) :
    ∀ p : s.Active,
      DiscPosOn (s.P (s.src p))
        (gridCenter (s.matchingRadius / 2) (gridLabel (s.matchingRadius / 2) (s.sourceBase p)))
          s.matchingRadius ∧
      DiscPosOn (s.P (s.wit p))
        (gridCenter (s.matchingRadius / 2) (gridLabel (s.matchingRadius / 2) (s.sourceBase p)))
          s.matchingRadius := by
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hXpos : 0 < Nk ^ a := Real.rpow_pos_of_pos hNkpos _
  have hr : 0 < s.matchingRadius := Real.rpow_pos_of_pos hXpos _
  apply s.grid_discriminants_pos hcv hNkpos (mesh := s.matchingRadius / 2)
    (r := s.matchingRadius) (by positivity : 0 < s.matchingRadius / 2)
    (by linarith) (MatchingScales.grid_radius_small (by linarith : 4 ≤ Nk ^ a))
  rw [Real.rpow_neg hNkpos.le]
  simpa only [matchingRadius, Real.rpow_neg_one] using
    MatchingScales.grid_positive_margin hXpos hgrid

noncomputable def matchingTests (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 1 ≤ Nk) (ha : 0 < a)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a) :
    PairTests (Fin s.m) (Fin s.J) s.Active :=
  s.toPairTests hω (zero_lt_one.trans_le hNk)
    (by have := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNk) a) (-3);
        change 0 < (Nk ^ a) ^ (-3 : ℝ) / 2; positivity)
    (by have := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNk) a) (-3);
        change (Nk ^ a) ^ (-3 : ℝ) / 2 ≤ (Nk ^ a) ^ (-3 : ℝ); linarith)
    (s.matching_grid_pos hcv hNk ha hX hgrid)

/-- Uniform finite-sample matching. All lower thresholds depend on the fixed
matching exponents and jet data, not on the tested polynomial format. -/
theorem matching_bad_mass {d₀ ε₀ R₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ) (hωsum : ∑ γ, ωk γ = 1)
    (hNk : 1 ≤ Nk) (ha : 0 < a) (hdc : 0 ≤ dc) (hdd : dc ≤ d₀)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a)
    (hXR : R₀ ≤ Nk ^ a) (hXJ : 3 * J.C₂ ≤ Nk ^ a)
    (hXV : matchingVolumeConstant ≤ Nk ^ a) (hXB : matchingBadConstant p J ≤ Nk ^ a) :
    s.pairMeasure ((s.matchingTests hcv hω hNk ha hX hgrid).toDiscSetup.discrepancyEvent
      (s.matchingThreshold p)) ≤ ENNReal.ofReal ((Nk ^ a) ^ (-5 : ℝ)) := by
  let X := Nk ^ a
  let r := s.matchingRadius
  let T := s.matchingTests hcv hω hNk ha hX hgrid
  let S := T.toDiscSetup
  let M₀ := s.matchingThreshold p
  let ζ := Nk ^ (-(M : ℝ))
  let θ := lightThreshold s.sourceCeiling ζ r X
  let Y := 2 * M₀ / δ Nk L
  let G := fun l : Fin s.J × (Fin 3 → ℤ) => matchingVolumeConstant * S.ρ l * Y ^ dc
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hXpos : 0 < X := Real.rpow_pos_of_pos hNkpos _
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hXfour : 4 ≤ X := by dsimp [X]; linarith
  have hr : 0 < r := Real.rpow_pos_of_pos hXpos _
  have hr1 : r ≤ 1 := (MatchingScales.grid_radius_small hXfour).trans (by norm_num)
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hNkpos _
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  have hΔ : 0 < s.sheetError := s.sheetError_pos hNkpos
  have hM₀ : 0 < M₀ := by dsimp [M₀, matchingThreshold]; positivity
  have hR : M₀ / (2 * S.Δ) = X ^ p.size := by
    change (2 * s.sheetError * X ^ p.size) / (2 * s.sheetError) = X ^ p.size
    field_simp
  have hYeq : Y = 8 * X ^ 2 * X ^ p.size := by
    dsimp [Y, M₀, matchingThreshold]
    rw [s.sheetError_eq hNkpos]
    change 2 * (2 * (2 * δ Nk L * X ^ 2) * X ^ p.size) / δ Nk L = _
    field_simp
    ring
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYbound : Y ≤ X ^ (p.size + 3) := by
    rw [hYeq]
    exact p.band_amplitude hX
  have hθ : ∀ l, 0 < θ l := lightThreshold_pos (s.sourceCeiling_nonneg hω hNkpos.le) hζ hr hXpos
  have hG : ∀ l, 0 ≤ G l := fun l => mul_nonneg
    (mul_nonneg matchingVolumeConstant_pos.le (S.ρ_nonneg l)) (Real.rpow_nonneg hY.le _)
  have hmatchR : R₀ * (2 * S.Δ) ≤ M₀ := by
    have hh : X ≤ X ^ p.size := by
      have hh := Real.rpow_le_rpow_of_exponent_le hXone p.size_one
      simpa only [Real.rpow_one] using hh
    have hh' := mul_le_mul_of_nonneg_right (hXR.trans hh) (show 0 ≤ 2 * S.Δ by positivity)
    change R₀ * (2 * s.sheetError) ≤ X ^ p.size * (2 * s.sheetError) at hh'
    change R₀ * (2 * s.sheetError) ≤ 2 * s.sheetError * X ^ p.size
    convert hh' using 1 <;> ring
  have hmatchC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ p.slack := by
    rw [hR, ← Real.rpow_mul hXpos.le]
    refine hXJ.trans ?_
    have hh := Real.rpow_le_rpow_of_exponent_le hXone (by have := p.density_gap; linarith :
      (1 : ℝ) ≤ p.size * p.slack)
    simpa only [Real.rpow_one] using hh
  have hρ : ∀ l, S.ρ l * (M₀ / (2 * S.Δ)) ^ (-p.slack) ≤ θ l / 2 := by
    intro l
    rw [hR]
    have hh := p.density_base hXfour (S.ρ_nonneg l)
      (mul_pos hζ (pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr) 3))
    convert hh using 1
    dsimp [θ, lightThreshold, S, T, matchingTests, PairTests.toDiscSetup, toPairTests, ζ, r, X]
    ring
  have hΓ : ∀ l, G l / θ l ≤ (M₀ / (2 * S.Δ)) ^ (p.middle + p.slack) := by
    intro l
    rw [hR]
    have hh := p.band_base hXfour (S.ρ_nonneg l)
      (mul_pos hζ (pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr) 3)) matchingVolumeConstant_pos.le
      hXV hY.le hYbound hdc hdd
    convert hh using 1
    congr 1
    dsimp [θ, lightThreshold, S, T, matchingTests, PairTests.toDiscSetup, toPairTests, ζ, r, X]
    ring
  have hδM : δ Nk L ≤ 2 * M₀ := by
    have hsize : 1 ≤ X ^ p.size := Real.one_le_rpow hXone (zero_le_one.trans p.size_one)
    have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hXone
    have hh := mul_le_mul hXsq hsize (by positivity) (by positivity : 0 ≤ X ^ 2)
    change δ Nk L ≤ 2 * M₀
    dsimp [M₀, matchingThreshold]
    rw [s.sheetError_eq hNkpos]
    change δ Nk L ≤ 2 * (2 * (2 * δ Nk L * X ^ 2) * X ^ p.size)
    nlinarith [mul_le_mul_of_nonneg_left hh hδ.le]
  have hband (i : Fin s.m × ↥(gridBox (r / 2) (1 / 8)) × Bool) (k : ℕ) :
      S.Pm {v | S.lab (S.src v) = S.lab i ∧
        ‖S.φ i (emb (S.x v)) - (S.w v : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
          ENNReal.ofReal (G (S.lab i) * ((2 : ℝ) ^ dc) ^ k) :=
    s.matching_band_pow_bound hω hNkpos hr hM₀ hδM
      (s.matching_grid_pos hcv hNk ha hX hgrid) i k
  have hb := discrepancy_mass_le_from_base J S M₀ θ G hmb hR₀ p.slack_pos p.slack_le hM₀
    p.decay_pos p.decay_lt_one hθ hG hmatchR hmatchC hρ p.density_growth hΓ
      (p.band_growth hdd) hband
  have ht := s.light_threshold_budget hω hωsum hNk ha hr hr1
  have ht' : (∑ i, θ (S.lab i)) ≤ 5324 * X ^ (-6 : ℝ) := ht
  have hconst : 0 ≤ 4 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) / (1 - p.decay) := by
    apply div_nonneg (by positivity) (sub_nonneg.mpr p.decay_lt_one.le)
  calc _ ≤ ENNReal.ofReal (4 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
          (1 - p.decay) * ∑ i, θ (S.lab i)) := hb
    _ ≤ ENNReal.ofReal (matchingBadConstant p J * X ^ (-6 : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left ht' hconst
      refine hh.trans_eq ?_
      dsimp [matchingBadConstant]
      ring
    _ ≤ ENNReal.ofReal (X * X ^ (-6 : ℝ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXB (Real.rpow_nonneg hXpos.le _))
    _ = _ := by
      congr 1
      change X * X ^ (-6 : ℝ) = X ^ (-5 : ℝ)
      calc X * X ^ (-6 : ℝ) = X ^ (1 : ℝ) * X ^ (-6 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hXpos]; norm_num

end NormalizationStep.TestedSample

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
