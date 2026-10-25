import Submission.Obl.k4_horizontal_strict_parameter_step.CandidateFloors
import Submission.Obl.k4_horizontal_strict_parameter_step.ReturnNumerics

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RawChartAssembly.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

noncomputable section

/-- A raw chart collection is sufficient for the complete single-depth output.
The input loss is chosen before the collection; every later choice keeps its original
trajectory priors and current-law normalization. -/
theorem raw_charts_to_layer (hjet : RawFirstJetCover) (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ (N : ℕ → ℝ) (k : ℕ), N₀ ≤ N k →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (ρ : Measure (α × ℝ))
        (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (e₀ D a : ℝ),
      Measurable (b k) → 0 < D → 0 < a → a ≤ 1 →
      Nonempty (RawChartFamily α ν ρ (π k) (b k) d (N k) ξ (N k ^ (-e₀)) D a
        ((N k ^ (-c)) ^ (1000 / (1 - d)))) →
      ∃ (σ : Measure (α × ℝ)) (n : ℕ) (A : Fin n → Set α)
        (q : Fin n → Fin 3 → ℤ) (h : Fin n → Fin 6 → ℝ),
        σ ≤ ρ ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ σ univ ∧
          LayerAt N d e₀ π b k ε σ D (a * N k ^ (-c)) n A q h := by
  let δ := ε / 100
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδgap : 5 * δ < ε := by dsimp [δ]; linarith
  obtain ⟨η, hη, Nj, hNj, hjet⟩ := hjet d hd hd1 c hc δ hδ
  obtain ⟨Nn, hnum⟩ := eventually_atTop.mp (eventually_raw_return_numerics hδ hδgap)
  let ξ := min η δ
  have hξ : 0 < ξ := lt_min hη hδ
  have hξη : ξ ≤ η := min_le_left _ _
  have hξδ : ξ ≤ δ := min_le_right _ _
  let N₀ := max Nj (max 2 Nn)
  have hN₀ : 2 ≤ N₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨ξ, hξ, N₀, hN₀, ?_⟩
  intro N k hNk α _ ν ρ π b e₀ D a hb hD ha ha1 hraw
  obtain ⟨H⟩ := hraw
  have hNk2 : 2 ≤ N k := hN₀.trans hNk
  have hNk1 : 1 ≤ N k := by linarith
  have hNkp : 0 < N k := by linarith
  have hNkjet : Nj ≤ N k := (le_max_left _ _).trans hNk
  have hNkn : Nn ≤ N k := ((le_max_right _ _).trans (le_max_right _ _)).trans hNk
  let w := N k ^ (-c)
  have hw : 0 < w := Real.rpow_pos_of_pos hNkp _
  have hw1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk1 (by linarith)
  have hNξη : N k ^ ξ ≤ N k ^ η := Real.rpow_le_rpow_of_exponent_le hNk1 hξη
  have hcover (i : Fin H.n) : FirstJet.Cover ((H.chart i).prior ν)
      ((H.chart i).y (b k) a D) ((H.chart i).β (b k) a D) ((H.chart i).γ (b k) a D)
        (H.chart i).E (H.chart i).F d (N k) δ w := by
    apply hjet (N k) hNkjet α ((H.chart i).prior ν) (H.valid i).probability
    exact (H.valid i).data.mono_bound (Real.rpow_pos_of_pos hNkp _) hNξη
      (Real.rpow_nonneg hw.le _)
  obtain ⟨C⟩ := candidateLayer_of_raw_charts H hb hNkp ha hD hw hcover
  obtain ⟨-, htwo, hnum⟩ := hnum (N k) hNkn
  obtain ⟨hnorm, hreserve⟩ := hnum ξ a w hξδ ha.le ha1 hw.le hw1
  exact C.restore_floors hNkp (mul_nonneg ha.le hw.le) (Real.rpow_nonneg hNkp.le _)
    (Real.rpow_pos_of_pos hNkp _) hnorm htwo hreserve

end

end Submission.Obl.k4_horizontal_strict_parameter_step
