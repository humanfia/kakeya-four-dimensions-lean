-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarTwoScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarConcentrationExact

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- Planar concentration with the error scale independent of the tube radius.
This form is stable under spatial rescaling of a localized family. -/
theorem planar_concentration_two_scales {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → δ / 100 ≤ ρ → ρ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube ρ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube ρ (x i) (v i)) →
        ENNReal.ofReal (δ ^ η * (n : ℝ) * ρ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (-η) * ρ) →
        (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
            (δ ^ (-η) * s ^ β) * incidence Y p) →
        ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
          (∀ i ∈ F, Tube ρ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 2 * ρ}) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i ∈ F, volume (Y i) := by
  let a := ε / 12
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨η₀, hη₀, hη₀1, d₀, hd₀, hplane⟩ :=
    planar_concentration_tube_scale (ε := ε / 2) (by positivity) hβ
  let η := min 1 (a * η₀ / 4)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηa : η ≤ a * η₀ / 4 := min_le_right _ _
  have hgap : 0 < a * η₀ - η := by nlinarith
  have hC : 0 < (100 : ℝ) ^ β := by positivity
  have hC1 : 1 ≤ (100 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ.le
  obtain ⟨d₁, hd₁, hcut₁⟩ := exists_power_cutoff ha hd₀
  obtain ⟨d₂, hd₂, hcut₂⟩ := exists_power_cutoff hgap
    (c := 1 / (100 : ℝ) ^ β) (by positivity)
  obtain ⟨d₃, hd₃, hcut₃⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (c := (1 / 100 : ℝ) ^ (ε / 2)) (by positivity)
  obtain ⟨d₄, hd₄, hcut₄⟩ := exists_power_cutoff (a := ε - 6 * a)
    (by dsimp [a]; linarith) (c := 1 / (100 : ℝ) ^ 6) (by norm_num)
  refine ⟨η, hη, hη1, min d₁ (min d₂ (min d₃ d₄)),
    lt_min hd₁ (lt_min hd₂ (lt_min hd₃ hd₄)), ?_⟩
  intro δ ρ hδ hδ100 hδd hδρ hρ100 n x v Y hn hv hT hY hYT hdense hvol hbroad
  have hδ1 : δ ≤ 1 := by linarith
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity : 0 < δ / 100) hδρ
  have hρ1 : ρ ≤ 1 := by linarith
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ : δ ≤ d₃ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₄ : δ ≤ d₄ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono ((hYT i).trans (hT i)))
  have hsumY : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  by_cases hsmall : ρ ≤ δ ^ a
  · have hρd : ρ ≤ d₀ := hsmall.trans (hcut₁ δ hδ hδd₁)
    have hdensity : ρ ^ η₀ ≤ δ ^ η := by
      calc
        _ ≤ (δ ^ a) ^ η₀ := Real.rpow_le_rpow hρ.le hsmall hη₀.le
        _ = δ ^ (a * η₀) := (Real.rpow_mul hδ.le _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    have hneg : δ ^ (-η) ≤ ρ ^ (-η₀) := by
      calc
        _ ≤ δ ^ (-(a * η₀)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
        _ = (δ ^ a) ^ (-η₀) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hρ hsmall (neg_nonpos.mpr hη₀.le)
    have hcaperr : (100 : ℝ) ^ β * δ ^ (-η) ≤ ρ ^ (-η₀) := by
      have hconst : (100 : ℝ) ^ β * δ ^ (a * η₀ - η) ≤ 1 := by
        have hh := hcut₂ δ hδ hδd₂
        convert (le_div_iff₀ hC).mp hh using 1 <;> ring
      calc
        _ = ((100 : ℝ) ^ β * δ ^ (a * η₀ - η)) * δ ^ (-(a * η₀)) := by
          rw [mul_assoc, ← Real.rpow_add hδ]
          congr 2
          ring
        _ ≤ 1 * δ ^ (-(a * η₀)) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hδ.le _)
        _ = (δ ^ a) ^ (-η₀) := by rw [one_mul, ← Real.rpow_mul hδ.le]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hρ hsmall (neg_nonpos.mpr hη₀.le)
    have hbroad' : ∀ p u s, ‖u‖ = 1 → ρ ≤ s → s ≤ 1 →
        ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
          (ρ ^ (-η₀) * s ^ β) * incidence Y p := by
      intro p u s hu hs hs1
      have hs0 : 0 < s := hρ.trans_le hs
      have hmono : ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ max δ s}.ncard : ℝ) := by
        have hsub : {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} ⊆
            {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ max δ s} :=
          fun i hi => ⟨hi.1, hi.2.trans (le_max_right _ _)⟩
        exact_mod_cast Set.ncard_mono hsub
      have hmax : max δ s ≤ 100 * s := max_le (by linarith) (by linarith)
      have hpow : (max δ s) ^ β ≤ (100 : ℝ) ^ β * s ^ β := by
        have hh := Real.rpow_le_rpow (le_trans hδ.le (le_max_left _ _)) hmax hβ.le
        simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100) hs0.le] using hh
      calc
        _ ≤ _ := hmono.trans (hbroad p u (max δ s) hu (le_max_left _ _) (max_le hδ1 hs1))
        _ ≤ (δ ^ (-η) * ((100 : ℝ) ^ β * s ^ β)) * incidence Y p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hδ.le _))
            (incidence_nonneg Y p)
        _ = (((100 : ℝ) ^ β * δ ^ (-η)) * s ^ β) * incidence Y p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcaperr (Real.rpow_nonneg hs0.le _)) (incidence_nonneg Y p)
    have hvol' : volume (⋃ i, Y i) ≤ ENNReal.ofReal (ρ ^ (1 - η₀)) := by
      refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [show 1 - η₀ = -η₀ + 1 by ring, Real.rpow_add hρ, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right hneg hρ.le
    obtain ⟨e, t, F, he, hslab, hkeep⟩ := hplane ρ hρ hρ100 hρd n x v Y hn hv hT hY hYT
      ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg n)) (sq_nonneg ρ))).trans hdense)
      hvol' hbroad'
    have hcoef : δ ^ ε ≤ ρ ^ (ε / 2) := by
      calc
        _ = δ ^ (ε / 2) * δ ^ (ε / 2) := by rw [← Real.rpow_add hδ]; congr 1; ring
        _ ≤ (1 / 100 : ℝ) ^ (ε / 2) * δ ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right (hcut₃ δ hδ hδd₃) (Real.rpow_nonneg hδ.le _)
        _ = (δ / 100) ^ (ε / 2) := by
          rw [← Real.mul_rpow (by positivity) hδ.le]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hδρ (by positivity)
    exact ⟨e, t, F, he, hslab,
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoef) (by positivity)).trans hkeep⟩
  · obtain ⟨e, t, F, _, he, hslab, hmass⟩ := global_slab_weighted hρ hρ1 x v
      (fun i => (volume (Y i)).toReal) Finset.univ (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hT i)
    have hlarge : δ ^ a ≤ ρ := le_of_not_ge hsmall
    have hcoef : (100 / ρ) ^ 6 * δ ^ ε ≤ 1 := by
      have hpower : (δ ^ a) ^ 6 = δ ^ (6 * a) := by
        rw [← Real.rpow_natCast (δ ^ a), ← Real.rpow_mul hδ.le]
        norm_num only [Nat.cast_ofNat]
        congr 1
        ring
      have hmono : (100 / ρ) ^ 6 ≤ (100 / δ ^ a) ^ 6 :=
        pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num)
          (Real.rpow_pos_of_pos hδ _) hlarge) 6
      calc
        _ ≤ (100 / δ ^ a) ^ 6 * δ ^ ε := mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hδ.le _)
        _ = (100 : ℝ) ^ 6 * δ ^ (ε - 6 * a) := by
          rw [div_pow, hpower, Real.rpow_sub hδ]
          ring
        _ ≤ 1 := by have hh := hcut₄ δ hδ hδd₄; nlinarith only [hh]
    have hmassY : 0 ≤ shadingMass Y := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hFfin : (∑ i ∈ F, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
    have hreal : δ ^ ε * shadingMass Y ≤ ∑ i ∈ F, (volume (Y i)).toReal := by
      apply (mul_le_mul_iff_right₀ (by positivity : 0 < (100 / ρ) ^ 6)).mp
      calc
        _ = ((100 / ρ) ^ 6 * δ ^ ε) * shadingMass Y := by ring
        _ ≤ 1 * shadingMass Y := mul_le_mul_of_nonneg_right hcoef hmassY
        _ ≤ _ := by simpa only [one_mul, shadingMass] using hmass
    refine ⟨e, t, F, he, hslab, ?_⟩
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumY) hFfin).mp
    simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i)] using hreal

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
