import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonBands
import Submission.Obl.k4_general_wide_layer_offset_comparison.AEComparisonDecay
import Submission.Lib.K4ScalarCoreTools.Finalization.CartesianOriginalMass

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonDecay.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

def bad (M₀ : ℝ) : Set (α × ℝ) :=
  {ω | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
    M₀ ≤ ‖f.coarseAtlas.sheet (f.coarseAtlas.selector ω) (emb y) -
      f.fineAtlas.sheet (f.fineAtlas.selector ω) (emb y)‖}

theorem bad_measurable (M₀ : ℝ) : MeasurableSet (f.bad M₀) := by
  let obs := fun ω : α × ℝ => (f.coarseAtlas.selector ω, f.fineAtlas.selector ω)
  have hobs (ij : f.coarseAtlas.Index × f.fineAtlas.Index) : MeasurableSet {ω | obs ω = ij} := by
    convert (f.coarseAtlas.atom_measurable ij.1).inter (f.fineAtlas.atom_measurable ij.2) using 1
    ext ω
    simp only [obs, Prod.ext_iff, mem_inter_iff, mem_ofPred_eq]
  exact Submission.Lib.K4ScalarCoreTools.Finalization.measurableSet_finite_observation_predicate
    obs hobs (fun ij => ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖f.coarseAtlas.sheet ij.1 (emb y) - f.fineAtlas.sheet ij.2 (emb y)‖)

/-- Discrepancy depends only on the two original finite selectors, so it
returns through the common jitter with its exact original mass. -/
theorem bad_law_eq (hp : p.Valid) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q) (M₀ : ℝ) :
    let S := f.matching hp Q hcover
    S.law {z | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ₁ (S.src z) (emb y) - S.φ₂ (S.wit z) (emb y)‖} = σ (f.bad M₀) := by
  letI := f.finite_source hp
  change matchingMeshCoupling σ (p.normalizedDomainBase k h g b) f.δ Q
    (Prod.fst ⁻¹' f.bad M₀) = σ (f.bad M₀)
  rw [← Measure.map_apply measurable_fst (f.bad_measurable M₀),
    matchingMeshCoupling_fst σ (p.normalizedDomainBase k h g b)
      (p.measurable_normalizedDomainBase hp.basic k h g b) f.mesh_pos Q hcover]

/-- Quantitative raw projected comparison. Separate original layer priors
and whole original-code band caps give power decay of bad ORIGINAL-source
mass, with no current pair-mass floors or discrepancy-scale logarithm. -/
theorem bad_mass_le (hp : p.Valid) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (J : JetData) {M₀ R d₀ ε₀ R₀ ε : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hmin : H * p.N k ^ (-sf) ≤ M₀)
    (hReq : R = M₀ / (4 * H * p.N k ^ (-sc))) (hR : R₀ ≤ R)
    (hC : 3 * J.C₂ ≤ R ^ ε)
    (hAR : (M₀ / p.N k ^ (-sf)) ^ p.d ≤ 2 * R ^ d₀) (hdd : p.d ≤ d₀) :
    σ (f.bad M₀) ≤ ENNReal.ofReal (8 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - (2 : ℝ) ^ (-ε / 2)) * p.projectedComparisonDensity k H * R ^ (-ε) *
        (3 * (1 + 240 * H ^ 3))) := by
  classical
  let S := f.matching hp Q hcover
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hRp : 0 < R := by linarith
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have haf : 0 < p.N k ^ (-sf) := Real.rpow_pos_of_pos hN _
  obtain ⟨r, hr, hc⟩ := p.comparisonPrior_copy_count hN1 hp.dimension_nonneg
    (sub_nonneg.mpr f.coarse_le_fine) sc m h b
  have hweights : ∀ c, S.weight₁ c ≤ (r : ℝ) * S.weight₂ c := by
    intro c
    change p.comparisonPrior k sc m h b c ≤ (r : ℝ) * p.comparisonPrior k sf m h b c
    simpa only [show sc + (sf - sc) = sf by ring] using (hc c).1
  have hround : ∀ c, (r : ℝ) * S.weight₂ c ≤ 2 * S.weight₁ c := by
    intro c
    change (r : ℝ) * p.comparisonPrior k sf m h b c ≤ 2 * p.comparisonPrior k sc m h b c
    simpa only [show sc + (sf - sc) = sf by ring] using (hc c).2
  have hSK : 0 < S.K := by
    change 0 < 34406400 * p.K k ^ 2 * H ^ p.d
    have hK := hp.subpower.1 k
    have hH := f.loss_one
    positivity
  have hw : ∀ c, 0 < S.weight₂ c := fun c => p.comparisonPrior_pos hN c
  have hReqS : R = M₀ / (2 * S.error) := by
    change R = M₀ / (2 * (2 * H * p.N k ^ (-sc)))
    simpa only [show 2 * (2 * H * p.N k ^ (-sc)) = 4 * H * p.N k ^ (-sc) by ring] using hReq
  have hband : ∀ i : f.coarseAtlas.Index ⊕ f.fineAtlas.Index, ∀ n : ℕ,
      S.law {z | S.lab₁ (S.src z) = Sum.elim S.lab₁ S.lab₂ i ∧
        ‖Sum.elim S.φ₁ S.φ₂ i (emb (S.point z)) - (S.value z : ℂ)‖ ≤ 2 * (M₀ * 2 ^ n)} ≤
        ENNReal.ofReal (S.K * S.weight₂ (Sum.elim S.lab₁ S.lab₂ i) *
          (M₀ / p.N k ^ (-sf)) ^ p.d * ((2 : ℝ) ^ p.d) ^ n) := by
    intro i n
    cases i with
    | inl i => exact f.band_ceiling hp f.coarseAtlas f.coarse_coeff hM₀ hmin Q hcover i n
    | inr i => exact f.band_ceiling hp f.fineAtlas f.fine_coeff hM₀ hmin Q hcover i n
  have hb := S.decay_against_original_weights_ae r hr hweights hround hSK hw J hmb hR₀
    hε hεε₀ hM₀ hReqS hR hC (Real.rpow_nonneg (div_nonneg hM₀.le haf.le) _)
    hAR hdd hband
  rw [f.bad_law_eq hp Q hcover M₀] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hb₀ := f.coarseAtlas.prior_budget hp.basic hN1 f.coarse_nonneg hp.dimension_nonneg
    f.time_pos f.width_pos
  have hb₁ := f.fineAtlas.prior_budget hp.basic hN1 f.fine_nonneg hp.dimension_nonneg
    f.time_pos f.width_pos
  have hsum : 2 * (∑ i, S.weight₁ (S.lab₁ i)) + ∑ j, S.weight₂ (S.lab₂ j) ≤
      3 * (1 + 240 * H ^ 3) := by
    change 2 * (∑ i : f.coarseAtlas.Index, p.comparisonPrior k sc m h b (f.coarseAtlas.key i)) +
      (∑ j : f.fineAtlas.Index, p.comparisonPrior k sf m h b (f.fineAtlas.key j)) ≤ _
    linarith
  have hχ : (2 : ℝ) ^ (-ε / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hfactor : 0 ≤ 8 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - (2 : ℝ) ^ (-ε / 2)) * S.K * R ^ (-ε) := by
    have hSK0 := S.K_nonneg
    positivity
  exact mul_le_mul_of_nonneg_left hsum hfactor

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
