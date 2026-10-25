-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AffineBody.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyLevel
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumScalar

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- Pointwise finite multiplicity is unchanged by an injective map. -/
theorem body_ncard_image {n : ℕ} (Y : Fin n → Set Space)
    (f : Space → Space) (hf : Function.Injective f) (p : Space) :
    {i : Fin n | f p ∈ f '' Y i}.ncard = {i : Fin n | p ∈ Y i}.ncard := by
  congr 1
  ext i
  exact hf.mem_set_image

/-- The body multiplicity bound is invariant under the affine normalization.
Only the volume weight acquires the Jacobian. -/
theorem affine_body_multiplicity {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m J : ℝ) (f : Space ≃ᵃ[ℝ] Space),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < J →
      (∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q) →
      BodyGeometry (fun i => f '' U i) x δ B (J * w) →
      (∀ i, f '' U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
      BodyConvexCount U w m → ∀ M : ℝ, 0 ≤ M →
      (∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) →
      M ≤ C * δ ^ (-ε) * B ^ (-ω) * m ^ (1 + σ / 2) * (J * w) ^ (-σ / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    convex_body_multiplicity hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m J f hn hcount hδB hw hm hJ hvol hG hball hYm hYU hden hK M hM hlevel
  apply H δ hδ hδd n (fun i => f '' U i) (fun i => f '' Y i) x B (J * w) m
    hn hcount hδB (mul_pos hJ hw) hm hG hball
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono (hYU i)) ?_ (hK.affine_image hw.le hJ f hvol) M hM ?_
  · intro i
    rw [hvol, hvol, ← mul_assoc, mul_comm (ENNReal.ofReal (δ ^ η)), mul_assoc]
    exact mul_le_mul_right (hden i) _
  · intro q hq
    obtain ⟨p, rfl⟩ := f.surjective q
    have hp : p ∈ ⋃ i, Y i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨i, f.injective.mem_set_image.mp hi⟩
    simpa only [body_ncard_image Y f f.injective p] using hlevel p hp

/-- Quantitative middle-scale form after an affine normalization of the grains.
The hypotheses expose the three geometric losses needed by the final exponent budget. -/
theorem affine_medium_multiplicity {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m J r b v h : ℝ) (f : Space ≃ᵃ[ℝ] Space),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < J → 0 < r →
      (∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q) →
      BodyGeometry (fun i => f '' U i) x δ B (J * w) →
      (∀ i, f '' U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
      BodyConvexCount U w m → δ ^ b * r ≤ B → δ ^ v * r ^ 2 ≤ J * w → m ≤ δ ^ (-h) →
      ∀ M : ℝ, 0 ≤ M → (∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) →
      M ≤ C * δ ^ (-(ε + b * ω + h * (1 + σ / 2) + v * σ / 2)) * r ^ (-ω - σ) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    affine_body_multiplicity hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m J r b v h f hn hcount hδB hw hm hJ hr hvol hG hball hYm hYU hden hK hwidth hweight hmUpper M hM hlevel
  exact (H δ hδ hδd n U Y x B w m J f hn hcount hδB hw hm hJ
    hvol hG hball hYm hYU hden hK M hM hlevel).trans
    (medium_body_factor_bound hδ hr hC (zero_le_one.trans hm) hσ hω.le hwidth hweight hmUpper)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
