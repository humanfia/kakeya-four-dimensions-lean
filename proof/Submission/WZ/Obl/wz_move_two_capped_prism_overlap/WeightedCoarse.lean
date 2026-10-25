-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedCoarse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedTransverse
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedCoarse.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (prism)

/-- The incidence-preserving dichotomy in the coordinates of the frozen
grains. Its density is measured against the cap on each incidence measure. -/
theorem weighted_coarse_grains_transverse_or_narrow {n : ℕ} {θ ρ a c s R D q : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρθ : ρ ≤ θ)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * ρ * c)
    (hR : 0 < R) (hRs : R ≤ (s / 2) * ρ * c) (hD : 0 < D) (hq : 0 ≤ q)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (H : Fin n → Set V) (Z U : Set V)
    (ν : Fin n → Measure V) (m : Fin n → ℝ) (hm : ∀ i, 0 < m i)
    (haxis : ∀ i, ‖coarseLinear θ (boxAxis (e i) 2)‖ ≤ 43)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ P a (ρ * c) c (z i) (e i))
    (hHZ : ∀ i, H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ O (m i) * volume A)
    (hdense : ∀ i, O (D * m i) * volume (P a (ρ * c) c (z i) (e i)) ≤ ν i (H i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p R) ≤ O (q * R ^ 3)) :
    confinementDensity a ρ c D s ≤ 46080 * q ∨
    ∃ C : Fin n → Set V,
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ H i ∧
        (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (C i) ∧
        O (D / 4) * volume (P a (ρ * c) c (z i) (e i)) ≤ volume (C i)) ∧
      ∀ i j p, p ∈ C i → p ∈ C j →
        pd (unit (dualLinear θ (boxAxis (e i) 0)))
          (unit (dualLinear θ (boxAxis (e j) 0))) ≤ s := by
  let r : ℝ := 1 / (100000000 * c)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrc : r * c = 1 / 100000000 := by dsimp [r]; field_simp
  let g := coarseAffine hθ hr
  let J : ℝ := r ^ 3 / θ ^ 2
  have hJ : 0 < J := by dsimp [J]; positivity
  have hvol (A : Set V) : volume (g '' A) = O J * volume A :=
    coarseAffine_volume hθ hr A
  have hg : Measurable g := g.toContinuousAffineEquiv.continuous.measurable
  let H' (i : Fin n) : Set V := g '' H i
  let ν' (i : Fin n) : Measure V := O J • (ν i).map g
  have hH'm (i : Fin n) : MeasurableSet (H' i) :=
    g.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hHm i)
  have hν' (i : Fin n) (A : Set V) (hA : MeasurableSet A) :
      ν' i A = O J * ν i (g ⁻¹' A) := by
    change (O J • (ν i).map g) A = _
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hg hA]
  have hν'H (i : Fin n) : ν' i (H' i) = O J * ν i (H i) := by
    rw [hν' i _ (hH'm i)]
    change O J * ν i (g ⁻¹' (g '' H i)) = _
    rw [preimage_image_eq _ g.injective]
  have hdom' (i : Fin n) (A : Set V) (hA : MeasurableSet A) :
      ν' i A ≤ O (m i) * volume A := by
    rw [hν' i A hA]
    calc
      _ ≤ O J * (O (m i) * volume (g ⁻¹' A)) :=
        mul_le_mul' le_rfl (hdom i _ (hA.preimage hg))
      _ = O (m i) * (O J * volume (g ⁻¹' A)) := by ac_rfl
      _ = O (m i) * volume A := by
        rw [← hvol, g.surjective.image_preimage]
  let α := r * a / (2 * θ)
  let β := r * ρ * c / θ
  obtain ⟨hα, hαβ, hβ⟩ := coarse_prism_sizes hθ hρ hρθ ha hac hc hr hrc
  choose u hu0 hbox using fun i => coarse_grain_prism hθ hθ1 hρ hρθ ha hac hc hr hrc
    (z i) (e i) (haxis i)
  have hH'P (i : Fin n) : H' i ⊆ prism α β (g (z i)) (u i) :=
    (image_mono (hHP i)).trans (hbox i)
  have hdense' (i : Fin n) :
      O ((D / 400000) * m i) * volume (prism α β (g (z i)) (u i)) ≤ ν' i (H' i) := by
    have hp := coarse_prism_volume_ratio hθ hρ ha hc hr hrc (z i) (e i) (u i)
    change volume (prism α β (g (z i)) (u i)) = _ at hp
    have hscalar : O ((D / 400000) * m i) * O 400000 = O (D * m i) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hD.le (by norm_num)) (hm i).le)]
      congr 1
      ring
    calc
      _ = O ((D / 400000) * m i) *
          (O 400000 * (O J * volume (P a (ρ * c) c (z i) (e i)))) := by rw [hp, hvol]
      _ = O J * (O (D * m i) * volume (P a (ρ * c) c (z i) (e i))) := by
        rw [← mul_assoc, hscalar]
        ac_rfl
      _ ≤ O J * ν i (H i) := mul_le_mul' le_rfl (hdense i)
      _ = _ := (hν'H i).symm
  have hH'Z (i : Fin n) : g.symm '' H' i ⊆ Z := by
    simpa only [H', image_image, g.symm_apply_apply, image_id'] using hHZ i
  rcases weighted_prism_transverse_or_narrow hα hαβ hβ (by positivity : 0 < D / 400000)
      hs hs1 (coarse_prism_threshold hθ hr has ha.le) hR (by positivity : 0 ≤ r / θ)
      (coarse_radius_fits hθ hr hRs) (inv_pos.mpr hJ) hq g.symm
      (fun i => g (z i)) u H' Z U ν' m hm (inverse_affine_volume hJ g hvol)
      (fun p q => coarseAffine_dist_upper hθ hθ1 hr p q)
      hH'm hH'P hH'Z hZU hUball
      (fun i => by rw [hν'H i]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin i))
      hdom' hdense' hupper with hden | hcut
  · exact Or.inl (by
      simpa only [confinementDensity, transverseDensity, α, β,
        coarse_prism_ratio hθ.ne' hr.ne' ha.ne', div_one] using hden)
  · obtain ⟨G, hG, hnarrow⟩ := hcut
    let C (i : Fin n) : Set V := g ⁻¹' G i
    have hCm (i : Fin n) : MeasurableSet (C i) := (hG i).1.preimage hg
    have hret (i : Fin n) : (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (C i) := by
      have hh := (hG i).2.2.1
      rw [hν'H i, hν' i _ (hG i).1] at hh
      rw [← mul_assoc, mul_comm (1 / 4 : ENNReal), mul_assoc] at hh
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne'
        ENNReal.ofReal_ne_top).mp hh
    refine Or.inr ⟨C, ?_, ?_⟩
    · intro i
      refine ⟨hCm i, fun p hp => g.injective.mem_set_image.mp ((hG i).2.1 hp), hret i, ?_⟩
      have hlow : O (m i) * (O (D / 4) * volume (P a (ρ * c) c (z i) (e i))) ≤
          O (m i) * volume (C i) := by
        calc
          _ = (1 / 4 : ENNReal) * (O (D * m i) * volume (P a (ρ * c) c (z i) (e i))) := by
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (hm i).le]
            congr 1
            rw [show m i * (D / 4) = D * m i / 4 by ring,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
            norm_num [O, div_eq_mul_inv, mul_comm]
          _ ≤ (1 / 4 : ENNReal) * ν i (H i) := mul_le_mul' le_rfl (hdense i)
          _ ≤ ν i (C i) := hret i
          _ ≤ _ := hdom i _ (hCm i)
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm i)).ne'
        ENNReal.ofReal_ne_top).mp hlow
    · intro i j p hi hj
      have hh := hnarrow i j (g p) hi hj
      rwa [hu0 i, hu0 j] at hh

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
