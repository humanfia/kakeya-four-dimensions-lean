-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormAfterZoom.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormVolume
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.FinalPackaging

/-!
# After the zoom: the body of `Grains σ`

Given the data of `GGX σ` at a scale `δ` (slope `f`, plane map `V`, slice and local coverings with
constant `C`) and a family at the zoomed scale `δ' = lam δ` whose shadings lie in the zoomed union
and inherit the plane-map precision, the zoomed slope `f (c 2 + · / lam)` and plane map
`V (c + lam⁻¹ • ·)` have Lipschitz constants `≤ 1/3` once `lam` dominates `3 L`, the coverings
transfer, the volume is bounded through the slices, and the final packaging gives the body of
`Grains σ` at `δ'`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

theorem zoom_inv_zoom {c : Space} {lam : ℝ} (hlam : lam ≠ 0) (q : Space) :
    c + lam⁻¹ • zoom c lam q = q := by
  simp only [zoom, smul_smul, inv_mul_cancel₀ hlam, one_smul]; abel

/-- **Post-zoom packaging** (the end of the normalization, sticky Lemma 3.5). -/
theorem grains_body_after_zoom {σ δ lam L C ηF ηo : ℝ} {E : Set Space} {f : ℝ → ℝ}
    {V : Space → Space} {c : Space}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ : 0 < δ) (hlam : 1 ≤ lam) (hlδ : lam * δ ≤ 1)
    (hL : 0 ≤ L) (hLlam : 3 * L ≤ lam) (hC : 0 ≤ C)
    (hEb : E ⊆ ball 0 1)
    (hf : ∀ a b : ℝ, dist (f a) (f b) ≤ L * dist a b)
    (hslice : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) C (projectedSlice f E z))
    (hVu : ∀ p ∈ E, ‖V p‖ = 1)
    (hVL : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ L * dist p q)
    (hloc : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ E,
      Covering ρ (1 - σ) C ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))))
    {m : ℕ} {x' v' : Fin m → Space} {Y' : Fin m → Set Space}
    (hF : Family ηF (lam * δ) m x' v' Y') (hS : Separated ηF (lam * δ) m x' v')
    (hY'E : ∀ j, Y' j ⊆ zoom c lam '' E)
    (hprec : ∀ j, ∀ q ∈ E, zoom c lam q ∈ Y' j → |inner ℝ (v' j) (V q)| ≤ lam * δ)
    (hηFo : ηF ≤ ηo) (hfam : (lam * δ) ^ ηo ≤ (lam * δ) ^ ηF / 2)
    (hCo : C ≤ (lam * δ) ^ (-ηo)) (hvolC : 32 * C ≤ (lam * δ) ^ (-ηo)) :
    ∃ (Y'' : Fin m → Set Space),
      Family ηo (lam * δ) m x' v' Y'' ∧ Separated ηo (lam * δ) m x' v' ∧ (∀ i, IsCompact (Y'' i)) ∧
      volume (⋃ i, Y'' i) ≤ ENNReal.ofReal ((lam * δ) ^ (σ - ηo)) ∧
      ∃ (g : ℝ → ℝ) (P : Space → Space), LipschitzWith 1 g ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 →
          Covering (lam * δ) (1 - σ) ((lam * δ) ^ (-ηo)) (projectedSlice g (⋃ i, Y'' i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y'' i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y'' i → |inner ℝ (v' i) (P p)| ≤ lam * δ) ∧
        (∀ ρ : ℝ, lam * δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y'' i) →
          Covering ρ (1 - σ) ((lam * δ) ^ (-ηo))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y'' i) ∩ ball p (Real.sqrt ρ)))) := by
  have hlam0 : 0 < lam := by linarith
  have hlamne : lam ≠ 0 := hlam0.ne'
  set δ' := lam * δ with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set E' := ⋃ j, Y' j with hE'
  have hE'Z : E' ⊆ zoom c lam '' E := iUnion_subset hY'E
  -- the zoomed slope and plane map
  set f' : ℝ → ℝ := fun z => f (c 2 + z / lam) with hf'
  set V' : Space → Space := fun q => V (c + lam⁻¹ • q) with hV'
  have hV'z : ∀ q, V' (zoom c lam q) = V q := fun q => by
    simp only [hV']; rw [zoom_inv_zoom hlamne]
  have hf'L : LipschitzOnWith 1 f' (Icc (-1 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a _ b _
    simp only [hf', NNReal.coe_one, one_mul]
    calc dist (f (c 2 + a / lam)) (f (c 2 + b / lam)) ≤ L * dist (c 2 + a / lam) (c 2 + b / lam) :=
          hf _ _
      _ = L / lam * dist a b := by
          rw [Real.dist_eq, Real.dist_eq, show c 2 + a / lam - (c 2 + b / lam) = (a - b) / lam by
            ring, abs_div, abs_of_pos hlam0]; ring
      _ ≤ 1 * dist a b := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          rw [div_le_iff₀ hlam0]; linarith
      _ = dist a b := one_mul _
  have hf'cont : Continuous f' := by
    have : LipschitzWith ⟨L, hL⟩ f := LipschitzWith.of_dist_le_mul fun a b => hf a b
    exact this.continuous.comp (continuous_const.add (continuous_id.div_const lam))
  -- slices
  have hsl' : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ' (1 - σ) C (projectedSlice f' E' z) := by
    intro z _
    have h := covering_projectedSlice_zoom (c := c) (E₀ := E) hlam0 subset_rfl hEb hδ hC hslice z
    exact h.mono (projectedSlice_mono hE'Z z)
  -- the plane map on the zoomed union
  have hV'L : LipschitzOnWith (1 / 3) V' E' := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a' ha' b' hb'
    obtain ⟨a, haE, rfl⟩ := hE'Z ha'
    obtain ⟨b, hbE, rfl⟩ := hE'Z hb'
    rw [hV'z, hV'z]
    have hd : dist (zoom c lam a) (zoom c lam b) = lam * dist a b := by
      rw [dist_eq_norm, dist_eq_norm, norm_zoom_sub hlam0.le]
    rw [hd]
    calc dist (V a) (V b) ≤ L * dist a b := hVL a haE b hbE
      _ ≤ (lam / 3) * dist a b := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ = ((1 / 3 : NNReal) : ℝ) * (lam * dist a b) := by push_cast; ring
  have hV'u : ∀ p ∈ E', ‖V' p‖ = 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := hE'Z hp
    rw [hV'z]; exact hVu q hq
  have hV'p : ∀ j p, p ∈ Y' j → |inner ℝ (v' j) (V' p)| ≤ δ' := by
    intro j p hp
    obtain ⟨q, hq, rfl⟩ := hY'E j hp
    rw [hV'z]; exact hprec j q hq hp
  have hloc' : ∀ ρ : ℝ, δ' ≤ ρ → ρ ≤ 1 → ∀ p ∈ E',
      Covering ρ (1 - σ) C ((fun q => inner ℝ (V' p) q) '' (E' ∩ ball p (Real.sqrt ρ))) := by
    intro ρ hρ hρ1 p hp
    obtain ⟨q, hq, rfl⟩ := hE'Z hp
    rw [hV'z]
    have h := covering_local_zoom (c := c) (E₀ := E) hlam subset_rfl hq hδ hloc hρ hρ1
    exact h.mono (image_mono (inter_subset_inter_left _ hE'Z))
  -- the volume through the slices
  have hEb' : E' ⊆ ball 0 1 := hF.union_subset_ball
  have hvol : volume E' ≤ ENNReal.ofReal (δ' ^ (σ - ηo)) := by
    have h := volume_le_of_slices hf'cont (MeasurableSet.iUnion hF.2.2.2.2.1) hEb' hδ'0 hlδ
      (by linarith) (by linarith) hC hsl'
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : δ' ^ (1 - (1 - σ)) = δ' ^ σ := by ring_nf
    rw [e]
    have e2 : δ' ^ (σ - ηo) = δ' ^ (-ηo) * δ' ^ σ := by
      rw [← Real.rpow_add hδ'0]; ring_nf
    rw [e2]
    have hp : 0 ≤ δ' ^ σ := Real.rpow_nonneg hδ'0.le _
    nlinarith
  -- packaging
  have hCo' : 0 < δ' := hδ'0
  refine grains_body_of_normalized hδ'0 hfam hF (hS.mono_error hδ'0 hlδ hηFo) hvol hf'L
    (fun z hz => (hsl' z hz).mono_constant hδ'0 hCo) hV'L hV'u hV'p
    (fun ρ hρ hρ1 p hp => (hloc' ρ hρ hρ1 p hp).mono_constant (hδ'0.trans_le hρ) hCo)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
