-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.MiddleCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.MiddleEstimate
import Submission.WZ.Obl.wz_separated_scales_gain.TubeCells

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- `D` yields cellwise lower density between the two separated parent scales. -/
theorem middle_cells {σ ω : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : EstimateD σ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ b δ lam θ m : ℝ, 0 < δ → δ ≤ b → b ≤ 1 →
      0 < lam → lam ≤ 1 → 0 < θ → 0 ≤ m →
      ∀ K : ℕ, 0 < K → 288 * θ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2 →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / (64 * K) →
      16 * m / fineContraction ≤ (fineRadius δ b) ^ (-η) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (a u : Space),
      0 < n →
      m / (δ ^ 2 * (fineContraction ^ 3 * b⁻¹ ^ 2) *
        (retainedFraction * (lam / (224 * K) * n))) ≤ (fineRadius δ b) ^ (-η) →
      ‖u‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ tube b a u) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, Y i ⊆ ball (0 : Space) 5) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → ConvexCount δ m x v →
      ∃ s : Finset (Fin 3 → ℤ),
        (∀ z ∈ s, (tube b a u ∩ gridCell b z).Nonempty) ∧
        ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
        ∀ z ∈ s, ENNReal.ofReal (A * lam * θ / K * (δ / b) ^ (ω + ε) *
          ((n : ℝ) * (δ / b) ^ 2) * ((n : ℝ) * (δ / b)) ^ (-σ)) * volume (gridCell b z) ≤
            volume ((⋃ i, Y i) ∩ gridCell b z) := by
  obtain ⟨A, η, hA, hη, H⟩ := middle_estimate hσ0 hσ1 hD hε
  refine ⟨A / 64512, η, by positivity, hη, ?_⟩
  intro b δ lam θ m hδ hδb hb1 hlam hlam1 hθ hm K hK hcut hden hconvbound
    n x v Y a u hn hslabbound hu hv hTP hover hYm hYT hYB hind hconv
  have hb : 0 < b := hδ.trans_le hδb
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  let f := lam / (224 * K)
  have hf : 0 < f := by dsimp [f]; positivity
  have hf1 : f ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 224 * (K : ℝ))).mpr
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  let F := A * f * (δ / b) ^ (ω + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * (δ / b)) ^ (-σ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨e, he⟩ := tube_in_square_prism hb1 a u hu
  have hlocal : ∀ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) →
      (∀ i, Z i ⊆ Y i) → lam * n * δ ^ 2 / (2 * K) ≤ ∑ i, volume.real (Z i) →
        ENNReal.ofReal F ≤ volume (⋃ i, Z i) := by
    intro Z hZm hZY hmass
    let t := lam / (4 * K) * δ ^ 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hZtube (i : Fin n) : Z i ⊆ tube δ (x i) (v i) := (hZY i).trans (hYT i)
    have hupper (i : Fin n) : volume.real (Z i) ≤ 56 * δ ^ 2 := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      rw [measureReal_def, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono (hZtube i)).trans (tube_volume_upper hδ.le (hδb.trans hb1) (x i) (v i) (hv i))))]
      exact (measure_mono (hZtube i)).trans (tube_volume_upper hδ.le (hδb.trans hb1) (x i) (v i) (hv i))
    have hmass' : 2 * n * t ≤ ∑ i, volume.real (Z i) := by
      convert hmass using 1
      dsimp [t]
      field_simp
      ring
    obtain ⟨k, g, hk, hg, hsize, hInd⟩ := dense_index_subfamily hn (fun i => volume.real (Z i)) ht
      (by positivity : 0 < 56 * δ ^ 2) hupper hmass'
    have hsize' : f * (n : ℝ) ≤ k := by
      convert hsize using 1
      dsimp [f, t]
      field_simp
      ring
    have hden' : (fineRadius δ b) ^ η ≤ fineContraction * (lam / (4 * K)) / 16 := by
      convert hden using 1 <;> ring
    have hslab' : m / (δ ^ 2 * (fineContraction ^ 3 * b⁻¹ ^ 2) * (retainedFraction * k)) ≤
        (fineRadius δ b) ^ (-η) := by
      apply le_trans _ hslabbound
      apply div_le_div_of_nonneg_left hm
      · have := retainedFraction_pos
        positivity
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsize' retainedFraction_pos.le) (by positivity)
    have hInd' (i : Fin k) : ENNReal.ofReal (lam / (4 * K) * δ ^ 2) ≤ volume (Z (g i)) := by
      have hfin : volume (Z (g i)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono (hZtube (g i))).trans (tube_volume_upper hδ.le (hδb.trans hb1) _ _ (hv (g i))))
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mpr (hInd i)
    have hbound := H b δ (lam / (4 * K)) m hδ hδb hb1 (by positivity) hm hden' hconvbound
      e k (fun i => x (g i)) (fun i => v (g i)) (fun i => Z (g i)) hk hslab'
      (fun i => hv (g i)) (fun i => (hTP (g i)).trans he)
      (fun i j hij => hover (g i) (g j) (hg.ne hij)) (fun i => hZm (g i))
      (fun i => hZtube (g i)) hInd' (convexCount_subfamily g hg hconv)
    apply le_trans (b := volume (⋃ i, Z (g i))) _ (subfamily_union_volume Z g)
    apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
    have hw := count_power_fraction (div_pos hδ hb) (Nat.cast_pos.mpr hn) hf hf1 hsize' hσ0 hσ1
    have hp : 0 ≤ A * (δ / b) ^ (ω + ε) * δ ^ 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hw hp
    dsimp [F]
    convert hh using 1 <;> ring
  obtain ⟨s, hmeet, hmass, hgrid⟩ := tube_cells_of_estimate hb hb1 hδ hlam hθ hF hK hcut
    hn x v Y a u hu hv hYm hYT hYB (fun i => (hYT i).trans (hTP i)) hind hlocal
  refine ⟨s, hmeet, hmass, ?_⟩
  intro z hz
  convert hgrid z hz using 2
  dsimp [F, f]
  congr 1
  field_simp
  ring

end WangZahlLot.Obl.wz_separated_scales_gain
