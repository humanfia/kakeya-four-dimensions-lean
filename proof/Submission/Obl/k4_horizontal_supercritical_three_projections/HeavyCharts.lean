import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartSelection
import Submission.Obl.k4_horizontal_supercritical_three_projections.FamilyMass
import Submission.Obl.k4_horizontal_supercritical_three_projections.Conditioning

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- One whole-chart cutoff supplies both a dense normalized scalar law and
bounds for its unchanged prior/reference ratio. Zero-prior charts have zero
incidence mass and disappear without a further loss. -/
theorem select_dense_charts {α : Type} {ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (ζ μ : Measure (α × ℝ)) [IsFiniteMeasure ζ]
    (G : ι → Set α) (hG : ∀ i, MeasurableSet (G i))
    (hdisj : Pairwise (fun i j => Disjoint (G i) (G j)))
    (W : ι → ℝ) (hW : ∀ i, 0 ≤ W i) {K H δ B : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hδ : 0 < δ)
    (hbudget : ∑ i, W i ≤ B)
    (hζμ : ζ ≤ μ)
    (hdom : ζ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcap : ∀ i, μ (G i ×ˢ univ) ≤ ENNReal.ofReal (H * W i)) :
    ∃ S : Finset ι,
      (∀ i ∈ S, ν (G i) ≠ 0 ∧ 0 < W i ∧
        ENNReal.ofReal δ * ν (G i) ≤ ζ (G i ×ˢ univ) ∧
        ENNReal.ofReal (δ * W i) ≤ ζ (G i ×ˢ univ) ∧
        δ / H ≤ W i / (ν (G i)).toReal ∧ W i / (ν (G i)).toReal ≤ K / δ ∧
        ENNReal.ofReal δ ≤ chartLaw ν ζ (G i) univ) ∧
      ζ {p | ∃ i, p.1 ∈ G i} ≤
        ζ {p | ∃ i ∈ S, p.1 ∈ G i} + ENNReal.ofReal (δ * (1 + B)) := by
  classical
  have hassign (i) : ζ (G i ×ˢ univ) ≤ ENNReal.ofReal K * ν (G i) := by
    have heq : G i ×ˢ (univ : Set ℝ) = {p : α × ℝ | p.1 ∈ G i} := by
      ext p
      simp
    rw [heq]
    exact incidence_assignment_bound ν ζ (G i) (ENNReal.ofReal K) hdom hsupp
  obtain ⟨S, hheavy, hmass⟩ := select_heavy_assignments ζ G hG
    (fun i => ENNReal.ofReal δ * (ν (G i) + ENNReal.ofReal (W i)))
  let S' := S.filter (fun i => ν (G i) ≠ 0)
  have hzero (i : ι) : ∀ᵐ p ∂ζ, ν (G i) = 0 → p.1 ∉ G i := by
    by_cases hi : ν (G i) = 0
    · have hz : ζ {p | p.1 ∈ G i} = 0 := by
        apply le_antisymm _ zero_le
        simpa only [hi, mul_zero] using
          incidence_assignment_bound ν ζ (G i) (ENNReal.ofReal K) hdom hsupp
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with p hp _
      exact hp
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hsame : ζ {p | ∃ i ∈ S, p.1 ∈ G i} = ζ {p | ∃ i ∈ S', p.1 ∈ G i} := by
    apply measure_congr
    filter_upwards [ae_all_iff.mpr hzero] with p hp
    apply propext
    constructor
    · rintro ⟨i, hi, hpi⟩
      refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hpi⟩
      exact fun h => hp i h hpi
    · rintro ⟨i, hi, hpi⟩
      exact ⟨i, (Finset.mem_filter.mp hi).1, hpi⟩
  have hνsum : (∑ i, ν (G i)) ≤ 1 := by
    have heq : ν (⋃ i, G i) = ∑ i, ν (G i) := by
      rw [measure_iUnion hdisj hG, tsum_fintype]
    rw [← heq]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : ν univ = 1)
  have hB : 0 ≤ B := (Finset.sum_nonneg (fun i _ => hW i)).trans hbudget
  have hthreshold :
      (∑ i, ENNReal.ofReal δ * (ν (G i) + ENNReal.ofReal (W i))) ≤
        ENNReal.ofReal (δ * (1 + B)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hW i)]
    calc
      _ ≤ ENNReal.ofReal δ * (1 + ENNReal.ofReal B) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hB,
          ← ENNReal.ofReal_mul hδ.le]
  refine ⟨S', ?_, ?_⟩
  · intro i hi
    obtain ⟨hiS, hi₀⟩ := Finset.mem_filter.mp hi
    have hνpos : 0 < (ν (G i)).toReal :=
      ENNReal.toReal_pos hi₀ (measure_ne_top ν _)
    have h₁ : ENNReal.ofReal δ * ν (G i) ≤ ζ (G i ×ˢ univ) := by
      apply le_trans _ (hheavy i hiS)
      gcongr
      exact le_add_right le_rfl
    have h₂ : ENNReal.ofReal (δ * W i) ≤ ζ (G i ×ˢ univ) := by
      rw [ENNReal.ofReal_mul hδ.le]
      apply le_trans _ (hheavy i hiS)
      gcongr
      exact le_add_left le_rfl
    have hlo : δ * (ν (G i)).toReal ≤ H * W i := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hH.le (hW i))).mp
      calc
        _ = ENNReal.ofReal δ * ν (G i) := by
          rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal (measure_ne_top ν _)]
        _ ≤ _ := h₁.trans ((hζμ _).trans (hcap i))
    have hup : δ * W i ≤ K * (ν (G i)).toReal := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK.le hνpos.le)).mp
      calc
        _ ≤ ENNReal.ofReal K * ν (G i) := h₂.trans (hassign i)
        _ = _ := by
          rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_toReal (measure_ne_top ν _)]
    obtain ⟨hc₁, hc₂⟩ := chart_density_ratio_bounds hνpos hδ hH hlo hup
    have hWi : 0 < W i := by nlinarith [mul_pos hδ hνpos]
    exact ⟨hi₀, hWi, h₁, h₂, hc₁, hc₂, chartLaw_mass_lower ν ζ (G i) hi₀ _ h₁⟩
  · calc
      _ ≤ ζ {p | ∃ i ∈ S, p.1 ∈ G i} + ENNReal.ofReal (δ * (1 + B)) :=
        hmass.trans (add_le_add le_rfl hthreshold)
      _ = _ := by rw [hsame]

end Submission.Obl.k4_horizontal_supercritical_three_projections
