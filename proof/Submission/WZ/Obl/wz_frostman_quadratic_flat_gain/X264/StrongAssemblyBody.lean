-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.StrongAssemblyBody.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.FactoredFineBall
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.FactoredThickening
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.CoarseBody
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PowerCellRefinement
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismProduct
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.ProductAssembly
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file StrongAssemblyBody.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion gridUnion_measurable)

/-- The full fine/coarse assembly, from `E` alone through the accepted o065, for a factored
cover that also satisfies the global quadratic count of its prisms. No separation of the
prisms is needed. The quadratic count is an explicit additional hypothesis; it is not a
consequence of `Factored`. -/
theorem strong_prism_aspect_body {σ ω : ℝ} (hσ : 0 ≤ σ) (hσupper : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : EstimateE σ ω) (e : ℝ) (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∃ d : ℝ, 0 < d ∧ ∀ ζ δ : ℝ, 0 ≤ ζ → ζ ≤ ζ₀ → 0 < δ → δ ≤ d →
    ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 → a ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
    (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ ball 0 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
    (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
    Factored (δ ^ (-ζ)) b (fun i => tube δ (x i) (v i))
      (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) *
        ENNReal.ofReal ((a * b) ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ)) * (volume U) ^ 2) →
    ENNReal.ofReal (A * δ ^ (ω + e) * (b / a) ^ ω * (n * δ ^ 4) ^ (σ / 2)) ≤
      volume (⋃ i, Y i) := by
  classical
  obtain ⟨Af, hAf, ηf, hηf, df, hdf, hfine⟩ :=
    factored_fine_prism_ball (fine_prism_estimate_ball hσ hσupper hω hE) (e / 4) (by positivity)
  obtain ⟨Ac, hAc, ηc, hηc, dc, hdc, hcoarse⟩ := coarse_level_two_body hσ hσupper hω hE
    (e := e / 4) (by positivity)
  obtain ⟨Al, hAl, ηl, hηl, hlocal⟩ :=
    factored_prism_thickening_restricted (ηc / 2) (by positivity)
  let θ : ℝ := min ηf (min ηl (min ηc e)) / 16
  have hθ : 0 < θ := div_pos (lt_min hηf (lt_min hηl (lt_min hηc he))) (by norm_num)
  have hθf : 16 * θ ≤ ηf := by dsimp [θ]; linarith [min_le_left ηf (min ηl (min ηc e))]
  have hθl : 16 * θ ≤ ηl := by
    have hh := (min_le_right ηf (min ηl (min ηc e))).trans (min_le_left ηl (min ηc e))
    dsimp [θ]; linarith
  have hθc : 16 * θ ≤ ηc := by
    have hh := ((min_le_right ηf (min ηl (min ηc e))).trans
      (min_le_right ηl (min ηc e))).trans (min_le_left ηc e)
    dsimp [θ]; linarith
  have hθe : 16 * θ ≤ e := by
    have hh := ((min_le_right ηf (min ηl (min ηc e))).trans
      (min_le_right ηl (min ηc e))).trans (min_le_right ηc e)
    dsimp [θ]; linarith
  obtain ⟨dr, hdr, hrefine⟩ := power_cell_refinement θ θ hθ.le hθ
  obtain ⟨dl, hdl, habsorb⟩ := power_absorption Al⁻¹ (by positivity : 0 < ηc / 2)
  refine ⟨Af * Ac / 39366, by positivity, θ, hθ, θ, hθ,
    min (min 1 (min df (min dr dl))) dc,
    lt_min (lt_min zero_lt_one (lt_min hdf (lt_min hdr hdl))) hdc, ?_⟩
  intro ζ δ hζ hζθ hδ hδd₀ a b hδa hab hb1 ha4 n x v Y hn hv hB hover hYm hYT hden
    p c e₁ e₂ e₃ hframe hfact hPquad
  have hδd : δ ≤ min 1 (min df (min dr dl)) := hδd₀.trans (min_le_left _ _)
  have hδdc : δ ≤ dc := hδd₀.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδdf : δ ≤ df := (hδd.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδdr : δ ≤ dr := ((hδd.trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hδdl : δ ≤ dl := ((hδd.trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  let P := fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)
  obtain ⟨S, t, k, q, g, h, ht, hblocks, hk, hq, hg, hh, hpoint, hfact', hcount⟩ :=
    hrefine δ hδ hδdr ζ a b ha (hab.trans hb1) n p x v Y P hn hv hB hYm hYT hden hfact
  let Y' : Fin k → Set Space := fun i => Y (g i) ∩ gridUnion a S
  let Z : Fin q → Set Space := fun j => P (h j) ∩ thickening a (P (h j) ∩ ⋃ i, Y' i)
  have hYm' : ∀ i, MeasurableSet (Y' i) := fun i =>
    (hYm (g i)).inter (gridUnion_measurable a S)
  have hYT' : ∀ i, Y' i ⊆ tube δ (x (g i)) (v (g i)) :=
    fun i => inter_subset_left.trans (hYT (g i))
  have hηref_f : θ + 2 * ζ + 2 * θ ≤ ηf := by linarith
  have hηref_l : θ + 2 * ζ + 2 * θ ≤ ηl := by linarith
  have hηref_c : θ + 2 * ζ + 2 * θ ≤ ηc := by linarith
  have hηpoint_f : θ + 2 * θ ≤ ηf := by linarith
  have hηpoint_l : θ + 2 * θ ≤ ηl := by linarith
  have hfactf := hfact'.mono_error
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηref_f))
  have hfactl := hfact'.mono_error
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηref_l))
  have hfactc := hfact'.mono_error
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηref_c))
  have hpointf (i : Fin k) : ENNReal.ofReal (δ ^ ηf * δ ^ 2) ≤ volume (Y' i) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηpoint_f) (sq_nonneg δ))).trans (hpoint i)
  have hpointl (i : Fin k) : ENNReal.ofReal (δ ^ ηl * δ ^ 2) ≤ volume (Y' i) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηpoint_l) (sq_nonneg δ))).trans (hpoint i)
  have hfine' := hfine δ hδ hδdf a b hδa hab hb1 ha4 k (x ∘ g) (v ∘ g) Y' hk
    (fun i => hv (g i)) (fun i => hB (g i))
    (fun i j hij => hover (g i) (g j) (fun heq => hij (hg heq)))
    hYm' hYT' hpointf q (c ∘ h) (e₁ ∘ h) (e₂ ∘ h) (e₃ ∘ h)
    (fun j => hframe (h j)) hfactf
  have hlocal' := hlocal δ hδ hδ1 a b hδa hab hb1 k (x ∘ g) (v ∘ g) Y' hk
    (fun i => hv (g i)) hYm' hYT' hpointl q (c ∘ h) (e₁ ∘ h) (e₂ ∘ h) (e₃ ∘ h)
    (fun j => hframe (h j)) hfactl
  have hmeet (j : Fin q) : (P (h j) ∩ ball 0 1).Nonempty := by
    obtain ⟨i, hi⟩ := hfact'.occupied hk j
    have hx : x (g i) ∈ tube δ (x (g i)) (v (g i)) :=
      self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
    exact ⟨x (g i), hi hx, hB (g i) hx⟩
  have hZm (j : Fin q) : MeasurableSet (Z j) :=
    (prism_isClosed a b (c (h j)) (e₁ (h j)) (e₂ (h j)) (e₃ (h j))).measurableSet.inter
      isOpen_thickening.measurableSet
  have habs := habsorb δ hδ hδdl
  rw [inv_mul_eq_div, div_le_one hAl] at habs
  have hdensity : δ ^ ηc ≤ Al * δ ^ (ηc / 2) := by
    calc
      _ = δ ^ (ηc / 2) * δ ^ (ηc / 2) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hδ.le _)
  have hZlow (j : Fin q) : ENNReal.ofReal (δ ^ ηc * a * b) ≤ volume (Z j) := by
    apply le_trans _ (hlocal' j)
    simp only [Function.comp_apply]
    rw [prism_volume ha.le hb.le (c (h j)) _ _ _ (hframe (h j)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Al * δ ^ (ηc / 2))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Al * δ ^ (ηc / 2) * a * b := by gcongr
      _ ≤ Al * δ ^ (ηc / 2) * (8 * a * b) := by
        have hh : a * b ≤ 8 * a * b := by nlinarith [mul_pos ha hb]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ Al * δ ^ (ηc / 2))
  have hmass : ENNReal.ofReal (δ ^ ηc * q * a * b) ≤ ∑ j, volume (Z j) := by
    have hm := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => hZlow j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg q),
      mul_left_comm (q : ℝ) (δ ^ ηc), mul_assoc] using hm
  have hquad' (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (Set.ncard {j : Fin q | P (h j) ⊆ U}) * ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ηc)) * (volume U) ^ 2 := by
    have hc : Set.ncard {j : Fin q | P (h j) ⊆ U} ≤ Set.ncard {j : Fin p | P j ⊆ U} :=
      Set.ncard_le_ncard_of_injOn h (fun _ hj => hj) hh.injOn
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {j : Fin p | P j ⊆ U}) * ENNReal.ofReal ((a * b) ^ 2) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl
      _ ≤ ENNReal.ofReal (δ ^ (-ζ)) * (volume U) ^ 2 := hPquad U hU
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : -ηc ≤ -ζ))) le_rfl
  have hcoarse' := hcoarse δ a b hδ hδdc hδa hab hb1 q
    (c ∘ h) (e₁ ∘ h) (e₂ ∘ h) (e₃ ∘ h) Z hq (fun j => hframe (h j)) hmeet
    hZm (fun _ => inter_subset_left) hZlow hfactc.2.2.1 hquad'
  have hprod := prism_cell_product ha hab hb1 ht.le (MeasurableSet.iUnion hYm) S hblocks
    Y' (fun _ => inter_subset_right)
    (fun i => inter_subset_left.trans (Set.subset_iUnion Y (g i)))
    (c ∘ h) (e₁ ∘ h) (e₂ ∘ h) (e₃ ∘ h) (fun j => hframe (h j))
  let j₀ : Fin q := ⟨0, hq⟩
  let N : ℝ := Set.ncard {i : Fin k | tube δ (x (g i)) (v (g i)) ⊆ P (h j₀)}
  have hvolpos : 0 < volume (P (h j₀)) := by
    dsimp only [P]
    rw [prism_volume ha.le hb.le (c (h j₀)) _ _ _ (hframe (h j₀))]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hvolfinite : volume (P (h j₀)) ≠ ⊤ := by
    dsimp only [P]
    rw [prism_volume ha.le hb.le (c (h j₀)) _ _ _ (hframe (h j₀))]
    exact ENNReal.ofReal_ne_top
  have hfineq : ENNReal.ofReal (Af * δ ^ (e / 4) * (δ / a) ^ ω *
      (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2)) ≤ ENNReal.ofReal (1458 * t) :=
    (ENNReal.mul_le_mul_iff_left hvolpos.ne' hvolfinite).mp ((hfine' j₀).trans (hprod.1 j₀))
  have hfinal := measure_product_lower (by positivity : 0 ≤ Af * δ ^ (e / 4) * (δ / a) ^ ω *
      (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2))
    (by norm_num : (0 : ℝ) < 1458) (by norm_num : (0 : ℝ) < 27)
    hfineq hcoarse' (by simpa using hprod.2)
  have hloss : e / 4 + e / 4 + (2 * θ + ζ + 3 * θ) * σ / 2 ≤ e := by
    have hr : 2 * θ + ζ + 3 * θ ≤ 6 * θ := by linarith
    have hp := mul_le_mul hr hσupper hσ (by positivity : 0 ≤ 6 * θ)
    nlinarith only [hp, hθe, hθ]
  have hscalar := prism_power_product_lower (ω := ω) hδ hδ1 ha hb
    (Nat.cast_nonneg _) (Nat.cast_nonneg q) (Nat.cast_nonneg n) hAf.le hAc.le hσ
    (hcount j₀) hloss
  exact (ENNReal.ofReal_le_ofReal hscalar).trans (by norm_num at hfinal ⊢; exact hfinal)

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
