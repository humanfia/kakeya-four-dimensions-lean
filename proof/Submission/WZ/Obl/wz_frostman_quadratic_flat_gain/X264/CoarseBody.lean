-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.CoarseBody.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.BodyCoarse
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.FineBall
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.LevelTwo
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file CoarseBody.lean), namespace renamed.

/-!
# Level ii for the prisms of the frozen structure, from o065

The prisms `prism a b c e₁ e₂ e₃` (half length one) sit in the frame images of o065's
standard prisms (half length two), so `body_coarse_estimate` applies with the Frostman count
and the global quadratic count of the prisms. No half-overlap of the prisms is needed.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (StandardPrism dilatedPrism BodyPacking
  standardPrism_subset_dilated body_estimate_of_tube_estimate)

/-- Packing from the global quadratic count. -/
theorem packing_of_quadratic {q : ℕ} {W : Fin q → Set Space} {w D : ℝ} (hw : 0 ≤ w)
    (hD : 0 < D)
    (h : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | W j ⊆ U}) * ENNReal.ofReal (w ^ 2) ≤
        ENNReal.ofReal D * (volume U) ^ 2) :
    BodyPacking W w (Real.sqrt D) := by
  intro U hU
  by_cases htop : volume U = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hD)).ne']
    exact le_top
  · obtain ⟨V, hV0, hV⟩ : ∃ V : ℝ, 0 ≤ V ∧ volume U = ENNReal.ofReal V :=
      ⟨(volume U).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
    have hh := h U hU
    rw [hV, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hV0,
      ← ENNReal.ofReal_mul hD.le] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    rw [hV, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hs := Real.sqrt_le_sqrt hh'
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hw, Real.sqrt_mul hD.le,
      Real.sqrt_sq hV0] at hs
    exact hs

set_option maxHeartbeats 800000 in
/-- Level ii from E, through o065's body estimate, for the frozen prisms. -/
theorem coarse_level_two_body {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : EstimateE σ ω) {e : ℝ} (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ d : ℝ, 0 < d ∧
    ∀ δ a b : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ 1 →
    ∀ (q : ℕ) (c e₁ e₂ e₃ : Fin q → Space) (Z : Fin q → Set Space),
    0 < q → (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
    (∀ j, (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ball 0 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
    (∀ j, ENNReal.ofReal (δ ^ η * a * b) ≤ volume (Z j)) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) ≤
        ENNReal.ofReal (δ ^ (-η) * q) * volume U) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) *
          ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η)) * (volume U) ^ 2) →
    ENNReal.ofReal (A * δ ^ e * b ^ ω * (q * (a * b) ^ 2) ^ (σ / 2)) ≤
      volume (⋃ j, Z j) := by
  have hB := body_estimate_of_tube_estimate hσ hσhalf hω (tubeEstimate_of_estimateE hE)
  obtain ⟨A₀, η₀, d₀, hA₀, hη₀, hd₀, hd₀small, H⟩ :=
    body_coarse_estimate hσ hσhalf hB (by positivity : 0 < e / 2)
  let V₁₀ : ℝ := (volume (ball (0 : Space) 10)).toReal
  have hV₁₀ : 0 ≤ V₁₀ := ENNReal.toReal_nonneg
  have hV₁₀eq : volume (ball (0 : Space) 10) = ENNReal.ofReal V₁₀ :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  let η := min (min η₀ (e / 4)) 1
  have hη : 0 < η := lt_min (lt_min hη₀ (by positivity)) zero_lt_one
  have hηη₀ : η ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηe : η ≤ e / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hη1 : η ≤ 1 := min_le_right _ _
  let d := min (min d₀ (1 / 2)) (1 / (1 + V₁₀ ^ 2))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨A₀, hA₀, η, hη, d, hd, ?_⟩
  intro δ a b hδ hδd hδa hab hb1 q c e₁ e₂ e₃ Z hq hframe hmeet hZm hZP hZd hfrost hquad
  have hδd₀ : δ ≤ d₀ := (hδd.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := (hδd.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hδV : δ ≤ 1 / (1 + V₁₀ ^ 2) := hδd.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  let f := fun j => frameIso (hframe j) (c j)
  have hsub : ∀ j, prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ f j '' StandardPrism a b :=
    fun j => prism_subset_frameIso_image (hframe j) a b (c j)
  -- the number of prisms is polynomially bounded by the quadratic count
  have hqmax : (q : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hall : {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ ball (0 : Space) 10} = univ := by
      ext j
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact prism_subset_ball_ten hab hb1 (hframe j) (hmeet j)
    have hh := hquad (ball (0 : Space) 10) (convex_ball _ _)
    rw [hall, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hV₁₀eq,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hV₁₀,
      ← ENNReal.ofReal_mul (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    have hab2 : δ ^ (4 : ℕ) ≤ (a * b) ^ 2 := by
      have h1 : δ ^ 2 ≤ a * b := by
        rw [sq]
        exact mul_le_mul hδa (hδa.trans hab) hδ.le ha.le
      calc
        δ ^ (4 : ℕ) = (δ ^ 2) ^ 2 := by ring
        _ ≤ (a * b) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have hδ4 : (0 : ℝ) < δ ^ (4 : ℕ) := by positivity
    have hq4 : (q : ℝ) * δ ^ (4 : ℕ) ≤ δ ^ (-η) * V₁₀ ^ 2 :=
      (mul_le_mul_of_nonneg_left hab2 (Nat.cast_nonneg q)).trans hh'
    -- δ^(-η) * V₁₀^2 * δ^(-4) ≤ δ^(-100)
    have hpow : δ ^ (-η) * V₁₀ ^ 2 ≤ δ ^ (-100 : ℝ) * δ ^ (4 : ℕ) := by
      have hV : V₁₀ ^ 2 ≤ δ⁻¹ := by
        have h1 : δ * (1 + V₁₀ ^ 2) ≤ 1 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + V₁₀ ^ 2)).mp hδV
        have h2 : V₁₀ ^ 2 * δ ≤ 1 := by nlinarith [sq_nonneg V₁₀]
        calc
          V₁₀ ^ 2 = V₁₀ ^ 2 * δ * δ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hδ.ne', mul_one]
          _ ≤ 1 * δ⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hδ.le)
          _ = δ⁻¹ := one_mul _
      have he1 : δ ^ (-η) ≤ δ⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have h2 : δ ^ (-100 : ℝ) * δ ^ (4 : ℕ) = δ ^ (-96 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hδ]
        norm_num
      have h3 : δ⁻¹ * δ⁻¹ ≤ δ ^ (-96 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
      rw [h2]
      calc
        δ ^ (-η) * V₁₀ ^ 2 ≤ δ⁻¹ * δ⁻¹ :=
          mul_le_mul he1 hV (by positivity) (by positivity)
        _ ≤ _ := h3
    have hfin := hq4.trans hpow
    exact le_of_mul_le_mul_right hfin hδ4
  have hfrost' : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {j | f j '' StandardPrism a b ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * q) * volume Q := by
    intro Q hQ
    apply le_trans _ (hfrost Q hQ)
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast Set.ncard_mono (fun j hj => (hsub j).trans hj)
  have hquad' : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | f j '' StandardPrism a b ⊆ U}) *
          ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η)) * (volume U) ^ 2 := by
    intro U hU
    apply le_trans _ (hquad U hU)
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
    exact_mod_cast Set.ncard_mono (fun j hj => (hsub j).trans hj)
  have hpack := packing_of_quadratic (by positivity) (Real.rpow_pos_of_pos hδ _) hquad'
  have hF1 : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hP1 : 1 ≤ Real.sqrt (δ ^ (-η)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hF1
  have hmeet' : ∀ j, (f j '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty := by
    intro j
    obtain ⟨y, hy, hyB⟩ := hmeet j
    exact ⟨y, hsub j hy, hyB⟩
  have hZP' : ∀ j, Z j ⊆ f j '' dilatedPrism 3 a b := fun j =>
    (hZP j).trans ((hsub j).trans
      (image_mono (standardPrism_subset_dilated ha.le hb.le (by norm_num))))
  have hZd' : ∀ j, ENNReal.ofReal (δ ^ η₀ * (a * b)) ≤ volume (Z j) := by
    intro j
    apply le_trans (ENNReal.ofReal_le_ofReal _) (hZd j)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηη₀) ha.le) hb.le
  have hbound := H δ a b (δ ^ (-η)) (Real.sqrt (δ ^ (-η))) hδ hδd₀ hδa hab
    (hb1.trans (by norm_num)) hF1 hP1 q f Z hq hqmax hmeet' hZm hZP' hZd' hfrost' hpack
  apply le_trans (ENNReal.ofReal_le_ofReal _) hbound
  have hFinv : (δ ^ (-η))⁻¹ = δ ^ η := by rw [Real.rpow_neg hδ.le, inv_inv]
  have hPs : Real.sqrt (δ ^ (-η)) ^ (-σ) = δ ^ (η * σ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hFinv, hPs]
  have hpow : δ ^ e ≤ δ ^ (e / 2) * δ ^ η * δ ^ (η * σ / 2) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    nlinarith
  have hW : 0 ≤ (q * (a * b) ^ 2 : ℝ) ^ (σ / 2) := by positivity
  calc
    A₀ * δ ^ e * b ^ ω * (q * (a * b) ^ 2) ^ (σ / 2) ≤
        A₀ * (δ ^ (e / 2) * δ ^ η * δ ^ (η * σ / 2)) * b ^ ω * (q * (a * b) ^ 2) ^ (σ / 2) := by
      gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
