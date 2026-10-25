/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/UniformSample.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.FiniteMatching
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleAssembly

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample

open MeasureTheory Set Metric

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

theorem goodSource_of_no_discrepancy {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀)
    (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 1 ≤ Nk) (ha : 0 < a)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a) (v : s.Active)
    (hgood : v ∉ (s.matchingTests hcv hω hNk ha hX hgrid).toDiscSetup.discrepancyEvent
      (s.matchingThreshold p)) : s.goodSource (p.output * a) (s.src v) (s.point v) := by
  let X := Nk ^ a
  let r := s.matchingRadius
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hXpos : 0 < X := Real.rpow_pos_of_pos hNkpos _
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hXfour : 4 ≤ X := by dsimp [X]; linarith
  have hr : 0 < r := Real.rpow_pos_of_pos hXpos _
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  have hneg : Nk ^ (-(p.output * a)) = X ^ (-p.output) := by
    dsimp [X]
    rw [← Real.rpow_mul hNkpos.le]
    congr 1
    ring
  have hpos : Nk ^ (p.output * a) = X ^ p.output := by
    dsimp [X]
    rw [← Real.rpow_mul hNkpos.le]
    congr 1
    ring
  have hinv : Nk ^ (-a) = X ^ (-1 : ℝ) := by
    dsimp [X]
    rw [Real.rpow_neg hNkpos.le, Real.rpow_neg_one]
  have hrad : 2 * Nk ^ (-(p.output * a)) ≤ r / 2 := by
    rw [hneg]
    exact p.output_radius hXfour
  have hfloor : Nk ^ (-(p.output * a)) ≤ Nk ^ (-a) := by
    rw [hneg, hinv]
    exact p.output_floor hXone
  have herror : 4 * (δ Nk L * Nk ^ a) / Nk ^ (-a) ≤ δ Nk L * Nk ^ (p.output * a) := by
    rw [Real.rpow_neg hNkpos.le, div_inv_eq_mul, hpos]
    convert mul_le_mul_of_nonneg_left (p.output_error hXfour) hδ.le using 1 <;> ring
  have hslope : 2 * Nk ^ a * (Nk ^ (-(p.output * a)) / 100) ≤ Nk ^ (-a) / 2 := by
    rw [hneg, hinv]
    exact p.output_slope hXone
  have hMbound : s.matchingThreshold p ≤ δ Nk L * Nk ^ (p.output * a) := by
    rw [matchingThreshold, s.sheetError_eq hNkpos, hpos]
    convert p.threshold_output hX hδ.le using 1 <;> ring
  have hpair := s.localPair_of_matching_agreement hcv hω hNkpos
    (by positivity : 0 < r / 2) (le_refl (r / 2))
    (s.matching_grid_pos hcv hNk ha hX hgrid) hrad hfloor herror hslope hMbound v (by
      intro y hy
      apply lt_of_not_ge
      intro hle
      exact hgood ⟨y, hy, hle⟩)
  have hH := (s.hH _ _).2 _ (s.witness_mem v)
  exact ⟨s.wit v, hH.2.2.2.1, hH.2.2.2.2.1, hpair⟩

theorem badActive_subset_discrepancy {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀)
    (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 1 ≤ Nk) (ha : 0 < a)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a) :
    s.badActive (p.output * a) ⊆
      (s.matchingTests hcv hω hNk ha hX hgrid).toDiscSetup.discrepancyEvent
        (s.matchingThreshold p) := by
  intro v hv
  by_contra hgood
  exact hv (s.goodSource_of_no_discrepancy p hcv hω hNk ha hX hgrid v hgood)

/-- One exact tested sample yields a paired sample with the same format
exponents, source events, frames and terminal lists. -/
theorem uniform_pairedAt {d₀ ε₀ R₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hcv : cv) (hlam : 2 ≤ lam) (hω : ∀ γ, 0 ≤ ωk γ) (hωsum : ∑ γ, ωk γ = 1)
    (hNk : 1 ≤ Nk) (ha : 0 < a) (hdc : 0 ≤ dc) (hdd : dc ≤ d₀)
    (hX : 8 ≤ Nk ^ a) (hgrid : 9 * gridConstant < Nk ^ a)
    (hXR : R₀ ≤ Nk ^ a) (hXJ : 3 * J.C₂ ≤ Nk ^ a)
    (hXV : matchingVolumeConstant ≤ Nk ^ a) (hXB : matchingBadConstant p J ≤ Nk ^ a)
    (hκX : s.κ ≤ Nk ^ a) {εout : ℝ} (hεout : ε ≤ εout) :
    PairedAt Nk Wk ωk νk Ek Bk L (p.output * a) h M D εout := by
  let X := Nk ^ a
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hκpos : 0 < s.κ := zero_lt_one.trans_le s.κ_one
  have hbad : s.pairMeasure (s.badActive (p.output * a)) ≤ ENNReal.ofReal (X ^ (-5 : ℝ)) :=
    (measure_mono (s.badActive_subset_discrepancy p hcv hω hNk ha hX hgrid)).trans
      (s.matching_bad_mass p J hmb hR₀ hcv hω hωsum hNk ha hdc hdd hX hgrid hXR hXJ hXV hXB)
  have hsmall : ENNReal.ofReal (X ^ (-5 : ℝ)) ≤ ENNReal.ofReal s.κ⁻¹ := by
    apply ENNReal.ofReal_le_ofReal
    calc _ ≤ X ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
      _ = X⁻¹ := Real.rpow_neg_one _
      _ ≤ _ := inv_anti₀ hκpos hκX
  have hcov : ENNReal.ofReal (2 * s.κ⁻¹) ≤ s.pairMeasure univ := by
    have hh := s.hcoverage
    have hrow (i : Fin s.m) : {v | ∃ j, v ∈ s.H i j} = FinitePairLaw.row s.H i := by
      ext v
      simp only [mem_setOf_eq, FinitePairLaw.row, mem_iUnion]
    simp_rw [hrow] at hh
    rw [← s.pairMeasure_univ_eq hω] at hh
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlam (by positivity))).trans hh
  have hcover : ENNReal.ofReal s.κ⁻¹ + ENNReal.ofReal (X ^ (-5 : ℝ)) ≤ s.pairMeasure univ := by
    calc _ ≤ ENNReal.ofReal s.κ⁻¹ + ENNReal.ofReal s.κ⁻¹ := add_le_add le_rfl hsmall
      _ = ENNReal.ofReal (2 * s.κ⁻¹) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := hcov
  apply s.pairedAt_of_bad_bound hcv hω hωsum hNk ha hεout
    (by have := p.size_one; dsimp [MatchingScales.output]; nlinarith)
    (by have := p.size_one; dsimp [MatchingScales.output]; nlinarith)
    (ENNReal.ofReal (X ^ (-5 : ℝ))) ENNReal.ofReal_ne_top hbad hcover

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample
