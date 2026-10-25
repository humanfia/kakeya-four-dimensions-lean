-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.WeightedClassMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.WeightedExtraction
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LightClass

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

lemma ncard_finset_reindex {α : Type*} (V : Finset α)
    (e : Fin V.card ≃ ↥V) (P : α → Prop) :
    Set.ncard {i : Fin V.card | P (e i)} = (V.filter P).card := by
  classical
  let g : Fin V.card → α := fun i => e i
  have hg : Function.Injective g := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have he : g '' {i : Fin V.card | P (g i)} = (↑(V.filter P) : Set α) := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨(e i).property, hi⟩
    · intro ha
      obtain ⟨haV, hPa⟩ := Finset.mem_filter.mp ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, haV⟩
      refine ⟨i, ?_, ?_⟩
      · change P (e i).val
        simpa only [hi] using hPa
      · exact congrArg Subtype.val hi
  change Set.ncard {i : Fin V.card | P (g i)} = _
  rw [← Set.ncard_image_of_injective _ hg, he, Set.ncard_coe_finset]

lemma sum_finset_reindex {α M : Type*} [AddCommMonoid M] (V : Finset α)
    (e : Fin V.card ≃ ↥V) (w : α → M) :
    (∑ i : Fin V.card, w (e i)) = ∑ i ∈ V, w i := by
  rw [e.sum_comp (fun i : V => w i)]
  exact Finset.sum_attach V w

/-- A complete light-mass estimate for a dyadic parameter class, with arbitrary shading
weights. The selected Katz--Tao subset is used only to estimate the removed mass. -/
theorem light_mass_of_dyadic_quotas {α : Type*} [DecidableEq α]
    (U : Finset α) (x v : α → Space) (Y : α → Set Space)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h ρ c η ε D R : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h)
    (hrρ : 12 * δ + h ≤ ρ) (hρ1 : ρ ≤ 1) (hc : |c| ≤ 3)
    (q₀ : Space) (hq₀ : ‖q₀‖ ≤ 6)
    (hv : ∀ i ∈ U, ‖v i‖ = 1) (htrans : ∀ i ∈ U, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i ∈ U, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i ∈ U, Y i ⊆ Tube δ (x i) (v i))
    (hclass : ∀ i ∈ U, |slope (v i) 0 - c| ≤ h)
    (hdiam : ∀ i ∈ U, dist (parameters (x i) (v i)) q₀ ≤ ρ)
    (J : ℕ) (hscale : 12 * δ + h = ρ * ((2 : ℝ) ^ J)⁻¹)
    (hD : 1 ≤ D) (hR : 1 < R) {q : ℕ} (hq : 0 < q)
    (hsize : 2 * (U.card : ℝ) < R ^ q)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin 3 → ℤ,
      ((U.filter (fun i => dyadicLabel k (normalizedParameters ρ q₀ (parameters (x i) (v i))) = l)).card : ℝ) ≤
        D * (2 : ℝ) ^ (J - k))
    (hη : 54 ≤ (((2 : ℝ) ^ J)⁻¹) ^ (-η))
    (hC : CinematicMomentAt (((2 : ℝ) ^ J)⁻¹) η ε f)
    {X L : Set (ℝ × ℝ)} {θ : ℝ≥0∞}
    (hX : ∀ i ∈ U, projection f '' Y i ⊆ X)
    (hlight : ∀ S : Set (ℝ × ℝ), volume (X ∩ L ∩ S) ≤ θ * volume (thickening ρ S)) :
    (∑ i ∈ U, volume (Y i ∩ projection f ⁻¹' L)) ^ 3 ≤
      ENNReal.ofReal (2 * q * R * (D * 28)) ^ 3 *
        (ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
          (θ * ENNReal.ofReal (432 * ρ)) *
            ENNReal.ofReal ((((2 : ℝ) ^ J)⁻¹) ^ (-ε)) ^ 2) := by
  have hρ : 0 < ρ := (by linarith : 0 < 12 * δ + h).trans_le hrρ
  let τ := ((2 : ℝ) ^ J)⁻¹
  let p : α → Space := fun i => normalizedParameters ρ q₀ (parameters (x i) (v i))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hrel : (12 * δ + h) / ρ = τ := by
    rw [hscale]
    exact mul_div_cancel_left₀ _ hρ.ne'
  have hw : ∀ i ∈ U, volume (Y i ∩ projection f ⁻¹' L) ≠ ⊤ := by
    intro i hi
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (inter_subset_left.trans ((hY i hi).trans (hball i hi))))
  have hbound := dyadic_weighted_cubic_bound U p J
    (fun i => volume (Y i ∩ projection f ⁻¹' L)) hD hR hq hsize hw hcount
    (B := ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
      (θ * ENNReal.ofReal (432 * ρ)) * ENNReal.ofReal (τ ^ (-ε)) ^ 2)
  norm_num only [show (3 : ℝ) ^ 3 + 1 = 28 by norm_num] at hbound
  apply hbound
  intro V hVU hsep hcounts
  let e := (Finset.equivFin V).symm
  let g : Fin V.card → α := fun i => e i
  have hgU (i : Fin V.card) : g i ∈ U := hVU (e i).property
  have hsep' : ∀ i j : Fin V.card, i ≠ j →
      12 * δ + h ≤ dist (parameters (x (g i)) (v (g i)))
        (parameters (x (g j)) (v (g j))) := by
    intro i j hij
    have hne : g i ≠ g j := fun he => hij (e.injective (Subtype.ext he))
    have hs := hsep (g i) (e i).property (g j) (e j).property hne
    change τ ≤ dist (normalizedParameters ρ q₀ (parameters (x (g i)) (v (g i))))
      (normalizedParameters ρ q₀ (parameters (x (g j)) (v (g j)))) at hs
    rw [dist_normalizedParameters hρ] at hs
    have hm := (le_div_iff₀ hρ).mp hs
    rw [hscale]
    nlinarith
  have hcount' : ∀ (b : Space) (s : ℝ), 12 * δ + h ≤ s → s ≤ ρ →
      (ncard {i : Fin V.card | parameters (x (g i)) (v (g i)) ∈ ball b s} : ℝ) ≤
        ((12 * δ + h) / ρ) ^ (-η) * (s / (12 * δ + h)) := by
    intro b s hrs hsρ
    have hrs' : τ ≤ s / ρ := by rw [← hrel]; exact div_le_div_of_nonneg_right hrs hρ.le
    have hs1 : s / ρ ≤ 1 := (div_le_one hρ).mpr hsρ
    have hm := hcounts (normalizedParameters ρ q₀ b) (s / ρ) hrs' hs1
    have heq : V.filter (fun i => p i ∈ ball (normalizedParameters ρ q₀ b) (s / ρ)) =
        V.filter (fun i => parameters (x i) (v i) ∈ ball b s) := by
      apply Finset.filter_congr
      intro i hi
      simp only [p, mem_ball, dist_normalizedParameters hρ,
        div_lt_div_iff_of_pos_right hρ]
    rw [heq] at hm
    rw [ncard_finset_reindex V e (fun i => parameters (x i) (v i) ∈ ball b s), hrel]
    have hratio : (s / ρ) / τ = s / (12 * δ + h) := by
      rw [hscale]
      dsimp [τ]
      ring
    norm_num only [show (2 : ℝ) * 3 ^ 3 = 54 by norm_num] at hm
    rw [hratio] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right hη (div_nonneg (by linarith) (by linarith)))
  have hX' : projection f '' (⋃ i : Fin V.card, Y (g i)) ⊆ X := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    exact hX (g i) (hgU i) (mem_image_of_mem _ hi)
  have hm := light_tube_class_mass hf hderiv hf0 hδ hh hrρ hρ1 hc
    (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i)) q₀ hq₀
    (fun i => hv (g i) (hgU i)) (fun i => htrans (g i) (hgU i))
    (fun i => hball (g i) (hgU i)) (fun i => hY (g i) (hgU i))
    (fun i => hclass (g i) (hgU i)) (fun i => hdiam (g i) (hgU i))
    hsep' hcount' (by rwa [hrel]) hX' hlight
  rw [hrel] at hm
  have hsum := sum_finset_reindex V e (fun i => volume (Y i ∩ projection f ⁻¹' L))
  simp only [g] at hm
  rw [hsum] at hm
  exact hm

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
