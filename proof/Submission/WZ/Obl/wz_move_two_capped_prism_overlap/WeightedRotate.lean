-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedRotate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedCoarse
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RotationRefinement

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedRotate.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

/-- Rotate the physical data before the weighted coarse normalization, while
retaining exactly the same incidence measures in the conclusion. -/
theorem weighted_rotated_coarse_dichotomy {n : ℕ} {ρ a c s r D q : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * ρ * c)
    (hr : 0 < r) (hrs : r ≤ (s / 2) * ρ * c) (hD : 0 < D) (hq : 0 ≤ q)
    (R : V ≃ₗᵢ[ℝ] V) (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V)
    (H : Fin n → Set V) (Z U : Set V) (ν : Fin n → Measure V)
    (m : Fin n → ℝ) (hm : ∀ i, 0 < m i)
    (haxis : ∀ i, ‖coarseLinear ρ (R (boxAxis (e i) 2))‖ ≤ 43)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ P a (ρ * c) c (z i) (e i))
    (hHZ : ∀ i, H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ O (m i) * volume A)
    (hdense : ∀ i, O (D * m i) * volume (P a (ρ * c) c (z i) (e i)) ≤ ν i (H i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ O (q * r ^ 3)) :
    confinementDensity a ρ c D s ≤ 46080 * q ∨
    ∃ C : Fin n → Set V,
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ H i ∧
        (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (C i) ∧
        O (D / 4) * volume (P a (ρ * c) c (z i) (e i)) ≤ volume (C i)) ∧
      ∀ i j p, p ∈ C i → p ∈ C j →
        pd (unit (dualLinear ρ (R (boxAxis (e i) 0))))
          (unit (dualLinear ρ (R (boxAxis (e j) 0)))) ≤ s := by
  let ν' (i : Fin n) := (ν i).map R
  have hν' (i : Fin n) (A : Set V) : ν' i A = ν i (R ⁻¹' A) :=
    R.toHomeomorph.measurableEmbedding.map_apply (ν i) A
  have hνH (i : Fin n) : ν' i (R '' H i) = ν i (H i) := by
    rw [hν', preimage_image_eq _ R.injective]
  have hprevol (A : Set V) : volume (R ⁻¹' A) = volume A := by
    rw [← rotation_volume R, R.surjective.image_preimage]
  have hdom' (i : Fin n) (A : Set V) (hA : MeasurableSet A) :
      ν' i A ≤ O (m i) * volume A := by
    rw [hν']
    exact (hdom i _ (hA.preimage R.continuous.measurable)).trans_eq
      (congrArg (fun t => O (m i) * t) (hprevol A))
  have hdense' (i : Fin n) : O (D * m i) *
      volume (P a (ρ * c) c (R (z i)) (rotatedFrame R (e i))) ≤ ν' i (R '' H i) := by
    rw [← rotated_prism, rotation_volume, hνH]
    exact hdense i
  rcases weighted_coarse_grains_transverse_or_narrow hρ hρ1 hρ le_rfl ha hac hc hs hs1 has
      hr hrs hD hq (fun i => R (z i)) (fun i => rotatedFrame R (e i))
      (fun i => R '' H i) (R '' Z) (R '' U) ν' m hm
      (fun i => by simpa only [rotated_boxAxis] using haxis i)
      (fun i => rotation_measurable R (hHm i))
      (fun i => by rw [← rotated_prism]; exact image_mono (hHP i))
      (fun i => image_mono (hHZ i)) (image_mono hZU) (rotation_subset_unit_ball R hUball)
      (fun i => by rw [hνH]; exact hfin i) hdom' hdense'
      (by rintro _ ⟨p, hp, rfl⟩; rw [rotation_ball_inter]; exact hupper p hp) with hden | hcut
  · exact Or.inl hden
  · obtain ⟨G, hG, hnarrow⟩ := hcut
    refine Or.inr ⟨fun i => R ⁻¹' G i, ?_, ?_⟩
    · intro i
      refine ⟨(hG i).1.preimage R.continuous.measurable,
        fun p hp => R.injective.mem_set_image.mp ((hG i).2.1 hp), ?_, ?_⟩
      · have hh := (hG i).2.2.1
        rwa [hνH i, hν' i] at hh
      · have hh := (hG i).2.2.2
        rwa [← rotated_prism, rotation_volume, ← hprevol (G i)] at hh
    · intro i j p hi hj
      simpa only [rotated_boxAxis] using hnarrow i j (R p) hi hj

/-- Apply the weighted dichotomy separately inside each coarse fibre. Each
fibre may use its own rotation. -/
theorem weighted_fibre_coarse_dichotomy {n N : ℕ} {ρ a c s r D q : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * ρ * c)
    (hr : 0 < r) (hrs : r ≤ (s / 2) * ρ * c) (hD : 0 < D) (hq : 0 ≤ q)
    (R : Fin N → V ≃ₗᵢ[ℝ] V) (γ : Fin n → Fin N)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V)
    (H : Fin n → Set V) (Z U : Set V) (ν : Fin n → Measure V)
    (m : Fin n → ℝ) (hm : ∀ i, 0 < m i)
    (haxis : ∀ i, ‖coarseLinear ρ (R (γ i) (boxAxis (e i) 2))‖ ≤ 43)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ P a (ρ * c) c (z i) (e i))
    (hHZ : ∀ i, H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ O (m i) * volume A)
    (hdense : ∀ i, O (D * m i) * volume (P a (ρ * c) c (z i) (e i)) ≤ ν i (H i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ O (q * r ^ 3)) :
    confinementDensity a ρ c D s ≤ 46080 * q ∨
    ∃ C : Fin n → Set V,
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ H i ∧
        (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (C i) ∧
        O (D / 4) * volume (P a (ρ * c) c (z i) (e i)) ≤ volume (C i)) ∧
      ∀ i j p, γ i = γ j → p ∈ C i → p ∈ C j →
        pd (unit (dualLinear ρ (R (γ i) (boxAxis (e i) 0))))
          (unit (dualLinear ρ (R (γ j) (boxAxis (e j) 0)))) ≤ s := by
  classical
  by_cases hden : confinementDensity a ρ c D s ≤ 46080 * q
  · exact Or.inl hden
  have hfibre (k : Fin N) : ∃ C : Fin n → Set V,
      (∀ i, γ i = k → MeasurableSet (C i) ∧ C i ⊆ H i ∧
        (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (C i) ∧
        O (D / 4) * volume (P a (ρ * c) c (z i) (e i)) ≤ volume (C i)) ∧
      ∀ i j p, γ i = k → γ j = k → p ∈ C i → p ∈ C j →
        pd (unit (dualLinear ρ (R k (boxAxis (e i) 0))))
          (unit (dualLinear ρ (R k (boxAxis (e j) 0)))) ≤ s := by
    by_cases hex : ∃ i, γ i = k
    · obtain ⟨i₀, hi₀⟩ := hex
      let f (i : Fin n) := if γ i = k then i else i₀
      have hfk (i : Fin n) : γ (f i) = k := by
        dsimp [f]
        split_ifs with hi
        · exact hi
        · exact hi₀
      have hfi (i : Fin n) (hi : γ i = k) : f i = i := if_pos hi
      rcases weighted_rotated_coarse_dichotomy hρ hρ1 ha hac hc hs hs1 has hr hrs hD hq
          (R k) (z ∘ f) (e ∘ f) (H ∘ f) Z U (ν ∘ f) (m ∘ f)
          (fun i => hm (f i))
          (fun i => by simpa only [Function.comp_apply, hfk i] using haxis (f i))
          (fun i => hHm (f i)) (fun i => hHP (f i)) (fun i => hHZ (f i))
          hZU hUball (fun i => hfin (f i)) (fun i => hdom (f i))
          (fun i => hdense (f i)) hupper with hd | hcuts
      · exact (hden hd).elim
      · obtain ⟨C, hC, hn⟩ := hcuts
        refine ⟨C, ?_, ?_⟩
        · intro i hi
          simpa only [Function.comp_apply, hfi i hi] using hC i
        · intro i j p hi hj hpi hpj
          simpa only [Function.comp_apply, hfi i hi, hfi j hj] using hn i j p hpi hpj
    · refine ⟨fun _ => ∅, ?_, ?_⟩
      · intro i hi
        exact (hex ⟨i, hi⟩).elim
      · intro i j p hi
        exact (hex ⟨i, hi⟩).elim
  choose C hC hn using hfibre
  refine Or.inr ⟨fun i => C (γ i) i, fun i => hC (γ i) i rfl, ?_⟩
  intro i j p hij hi hj
  have hj' : p ∈ C (γ i) j := by simpa only [hij] using hj
  simpa only [← hij] using hn (γ i) i j p rfl hij.symm hi hj'

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
