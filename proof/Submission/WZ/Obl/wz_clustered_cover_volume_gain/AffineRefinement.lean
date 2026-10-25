-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AffineRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineBody

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- Pulling back a measurable refinement by an affine equivalence preserves
its mass fraction and all pointwise multiplicity bounds. -/
theorem pullback_body_refinement {n : ℕ} (Y Z' : Fin n → Set Space)
    (f : Space ≃ᵃ[ℝ] Space) {J t K : ℝ} (hJ : 0 < J)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (hZ : ∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ f '' Y i)
    (hmass : ENNReal.ofReal t * ∑ i, volume (f '' Y i) ≤ ∑ i, volume (Z' i))
    (hcount : ∀ p, bodyCount Z' p ≤ K) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      ENNReal.ofReal t * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ K := by
  let Z := fun i => f ⁻¹' Z' i
  have himage : ∀ i, f '' Z i = Z' i := fun i => f.surjective.image_preimage (Z' i)
  have hmeas : ∀ i, MeasurableSet (Z i) := fun i =>
    (hZ i).1.preimage f.toContinuousAffineEquiv.continuous.measurable
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hmeas i, ?_⟩
    intro p hp
    exact f.injective.mem_set_image.mp ((hZ i).2 hp)
  · have hm := hmass
    simp only [← himage, hvol, ← Finset.mul_sum] at hm
    rw [← mul_assoc, mul_comm (ENNReal.ofReal t), mul_assoc] at hm
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal J)⁻¹) hm
    have hJ0 : ENNReal.ofReal J ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hJ)
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hJ0 ENNReal.ofReal_ne_top, one_mul] using hh
  · intro p
    have hc := hcount (f p)
    have he : bodyCount Z p = bodyCount Z' (f p) := rfl
    rwa [he]

/-- The volume-only refinement theorem in the original coordinates. Only the
weight acquires the Jacobian of the common affine normalization. -/
theorem affine_body_refinement_of_volume {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (w m J D : ℝ) (f : Space ≃ᵃ[ℝ] Space),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 256 * δ ^ 2 ≤ J * w → 0 < w →
      1 ≤ m → 0 < J → 0 < D → 1536 * δ ^ η ≤ D →
      (∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q) →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, f '' U i ⊆ ball (0 : Space) 1) →
      (∀ i, ball (x i) δ ⊆ f '' U i) →
      (∀ i, ∃ p ∈ f '' U i, ∃ q ∈ f '' U i, (1 / 16 : ℝ) ≤ dist p q) →
      (∀ i, ENNReal.ofReal w ≤ volume (U i) ∧ volume (U i) ≤ ENNReal.ofReal (384 * w)) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ C * δ ^ (-ε) * D⁻¹ * m ^ (1 + σ / 2) * (J * w) ^ (-(ω + σ) / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    convex_body_refinement_of_volume hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x w m J D f hn hcount hscale hw hm hJ hD htD hvol hcompact
    hconvex hball hint hdiam hbounds hYm hYU hden hK
  have hden' : ENNReal.ofReal (D * n * (J * w)) ≤ ∑ i, volume (f '' Y i) := by
    calc
      _ = ENNReal.ofReal J * ENNReal.ofReal (D * n * w) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal J * ∑ i, volume (Y i) := mul_le_mul' le_rfl hden
      _ = _ := by simp only [Finset.mul_sum, hvol]
  have hbounds' : ∀ i, ENNReal.ofReal (J * w) ≤ volume (f '' U i) ∧
      volume (f '' U i) ≤ ENNReal.ofReal (384 * (J * w)) := by
    intro i
    rw [hvol, ENNReal.ofReal_mul hJ.le]
    constructor
    · exact mul_le_mul' le_rfl (hbounds i).1
    · calc
        _ ≤ ENNReal.ofReal J * ENNReal.ofReal (384 * w) := mul_le_mul' le_rfl (hbounds i).2
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le]; congr 1; ring
  obtain ⟨Z', hZ', hmass, hmult⟩ := H δ hδ hδd n (fun i => f '' U i)
    (fun i => f '' Y i) x (J * w) m D hn hcount hscale hm hD htD
    (fun i => (hcompact i).image f.toContinuousAffineEquiv.continuous)
    (fun i => (hconvex i).affine_image f.toAffineMap) hball hint hdiam hbounds'
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono (hYU i)) hden' (hK.affine_image hw.le hJ f hvol)
  obtain ⟨Z, hZY, hmass', hmult'⟩ := pullback_body_refinement Y Z' f (t := 1 / 2) hJ hvol hZ'
    (by simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] using hmass) hmult
  exact ⟨Z, hZY, by simpa using hmass', hmult'⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
