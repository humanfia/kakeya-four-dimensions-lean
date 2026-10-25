-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AverageLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineBody

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- Average density gives an upper multiplicity level with its explicit inverse loss. -/
theorem convex_body_multiplicity_average {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m D : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < D →
      768 * δ ^ η ≤ D → BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ∀ M : ℝ, 0 ≤ M → (∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) →
      M ≤ C * δ ^ (-ε) * D⁻¹ * B ^ (-ω) * m ^ (1 + σ / 2) * w ^ (-σ / 2) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    convex_body_estimate_average hσ hσhalf hω hE ε hε
  refine ⟨384 / A, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m D hn hcount hδB hw hm hD htD hG hball hYm hYU hden hK M hM hlevel
  have hB : 0 < B := hδ.trans_le hδB
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  let c := A * δ ^ ε * B ^ ω * m ^ (-1 - σ / 2) * D * w ^ (σ / 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv := H δ hδ hδd n U Y x B w m D hn hcount hδB hw hm hD htD hG hball hYm hYU hden hK
  have hv' : ENNReal.ofReal (c * (n * w)) ≤ volume (⋃ i, Y i) := by
    convert hv using 1
    congr 1
    dsimp [c]
    rw [Real.rpow_add hw, Real.rpow_one]
    ring
  have hh := body_level_bound_of_union_lower hn hw hc hM hYm hYU
    (fun i => (hG.volume_bounds i).2) hlevel hv'
  apply hh.trans_eq
  dsimp only [c]
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_inv]
  ring

/-- The average-density multiplicity estimate after an affine change of coordinates. -/
theorem affine_body_multiplicity_average {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m J D : ℝ) (f : Space ≃ᵃ[ℝ] Space),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < J → 0 < D →
      768 * δ ^ η ≤ D → (∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q) →
      BodyGeometry (fun i => f '' U i) x δ B (J * w) →
      (∀ i, f '' U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ∀ M : ℝ, 0 ≤ M → (∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) →
      M ≤ C * δ ^ (-ε) * D⁻¹ * B ^ (-ω) * m ^ (1 + σ / 2) * (J * w) ^ (-σ / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    convex_body_multiplicity_average hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m J D f hn hcount hδB hw hm hJ hD htD hvol hG hball hYm hYU hden hK M hM hlevel
  apply H δ hδ hδd n (fun i => f '' U i) (fun i => f '' Y i) x B (J * w) m D
    hn hcount hδB (mul_pos hJ hw) hm hD htD hG hball
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono (hYU i)) ?_ (hK.affine_image hw.le hJ f hvol) M hM ?_
  · calc
      _ = ENNReal.ofReal J * ENNReal.ofReal (D * n * w) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal J * ∑ i, volume (Y i) := mul_le_mul' le_rfl hden
      _ = _ := by simp only [Finset.mul_sum, hvol]
  · intro q hq
    obtain ⟨p, rfl⟩ := f.surjective q
    have hp : p ∈ ⋃ i, Y i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨i, f.injective.mem_set_image.mp hi⟩
    simpa only [body_ncard_image Y f f.injective p] using hlevel p hp

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
