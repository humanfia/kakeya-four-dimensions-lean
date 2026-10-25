-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NormalizedGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TransverseDichotomy

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (prism)

/-- The density forced by a transverse pair depends on the grain aspect
ratio, but not on the affine normalization scale. -/
def confinementDensity (a ρ c D s : ℝ) : ℝ :=
  transverseDensity 1 (2 * ρ * c / a) (D / 400000 / 2) (D / 400000 / 16000) s

/-- Dense original grains, after one common coarse normalization, either
force a large physical ball density or have a quarter-mass narrow refinement. -/
theorem coarse_grains_transverse_or_narrow {n : ℕ} {θ ρ a c s R D lam : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρθ : ρ ≤ θ)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * ρ * c)
    (hR : 0 < R) (hRs : R ≤ (s / 2) * ρ * c) (hD : 0 < D) (hlam : 0 ≤ lam)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (Y : Fin n → Set V) (Z U : Set V)
    (haxis : ∀ i, ‖coarseLinear θ (boxAxis (e i) 2)‖ ≤ 43)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ P a (ρ * c) c (z i) (e i))
    (hYZ : ∀ i, Y i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hdense : ∀ i, O D * volume (P a (ρ * c) c (z i) (e i)) ≤ volume (Y i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p R) ≤ O (lam * R ^ 3)) :
    confinementDensity a ρ c D s ≤ 46080 * lam ∨
    ∃ W : Fin n → Set V,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i ∧
        (1 / 4 : ℝ≥0∞) * volume (Y i) ≤ volume (W i)) ∧
      ∀ i j p, p ∈ W i → p ∈ W j →
        pd (unit (dualLinear θ (boxAxis (e i) 0)))
          (unit (dualLinear θ (boxAxis (e j) 0))) ≤ s := by
  let r : ℝ := 1 / (100000000 * c)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrc : r * c = 1 / 100000000 := by dsimp [r]; field_simp
  let g := coarseAffine hθ hr
  let J : ℝ := r ^ 3 / θ ^ 2
  have hJ : 0 < J := by dsimp [J]; positivity
  have hvol (Q : Set V) : volume (g '' Q) = O J * volume Q := coarseAffine_volume hθ hr Q
  let α := r * a / (2 * θ)
  let β := r * ρ * c / θ
  obtain ⟨hα, hαβ, hβ⟩ := coarse_prism_sizes hθ hρ hρθ ha hac hc hr hrc
  choose u hu0 hbox using fun i => coarse_grain_prism hθ hθ1 hρ hρθ ha hac hc hr hrc
    (z i) (e i) (haxis i)
  let H := fun i => g '' Y i
  have hHm (i : Fin n) : MeasurableSet (H i) :=
    g.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i)
  have hHU (i : Fin n) : H i ⊆ prism α β (g (z i)) (u i) := (Set.image_mono (hYU i)).trans (hbox i)
  have hden (i : Fin n) : O (D / 400000) * volume (prism α β (g (z i)) (u i)) ≤ volume (H i) := by
    have hp := coarse_prism_volume_ratio hθ hρ ha hc hr hrc (z i) (e i) (u i)
    change volume (prism α β (g (z i)) (u i)) = _ at hp
    rw [hp, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ D / 400000)]
    rw [show D / 400000 * 400000 = D by ring, hvol, hvol]
    rw [mul_comm (O D), mul_assoc]
    exact mul_le_mul' le_rfl (by simpa only [mul_comm] using hdense i)
  have hHZ (i : Fin n) : g.symm '' H i ⊆ Z := by
    simpa only [H, Set.image_image, g.symm_apply_apply, Set.image_id'] using hYZ i
  have hLip (p q : V) : dist (g.symm.symm p) (g.symm.symm q) ≤ (r / θ) * dist p q :=
    coarseAffine_dist_upper hθ hθ1 hr p q
  have hfit : (r / θ) * R ≤ (s / 2) * β := coarse_radius_fits hθ hr hRs
  have hαs : α ≤ s * β := coarse_prism_threshold hθ hr has ha.le
  rcases prism_transverse_or_narrow hα hαβ hβ (by positivity : 0 < D / 400000)
      hs hs1 hαs hR (by positivity : 0 ≤ r / θ) hfit (inv_pos.mpr hJ) hlam
      g.symm (fun i => g (z i)) u H Z U (inverse_affine_volume hJ g hvol) hLip
      hHm hHU hHZ hZU hUball hden hupper with hden | href
  · left
    simpa only [confinementDensity, transverseDensity, α, β,
      coarse_prism_ratio hθ.ne' hr.ne' ha.ne', div_one] using hden
  · obtain ⟨G, hG, hnarrow⟩ := href
    let W := fun i => g ⁻¹' G i
    have himage (i : Fin n) : g '' W i = G i := g.surjective.image_preimage (G i)
    right
    refine ⟨W, ?_, ?_⟩
    · intro i
      refine ⟨(hG i).1.preimage g.toContinuousAffineEquiv.continuous.measurable, ?_, ?_⟩
      · intro p hp
        exact g.injective.mem_set_image.mp ((hG i).2.1 hp)
      · have hh := (hG i).2.2
        rw [← himage i, hvol, hvol, ← mul_assoc, mul_comm (1 / 4 : ℝ≥0∞), mul_assoc] at hh
        exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp hh
    · intro i j p hi hj
      have hh := hnarrow i j (g p) hi hj
      rwa [hu0 i, hu0 j] at hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
