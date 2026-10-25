import Mathlib
import Submission.Lib.K4ContactTransfer.ZoomLaw
import Submission.Lib.K4ContactTransfer.ZoomLabel
import Submission.Lib.K4ContactTransfer.ZoomBlocks

/-!
# Pulling candidates back from a zoomed parent

The contact instance built inside a parent `Q` has prior `ν(·|A_Q)`, laws
zoomed in time and divided by `W = q_Q ν(A_Q)`, trajectory coefficients
normalized by the parent zoom and the row, and the time blocks of descendants
rebased inside the unit block. This file transports the masses of candidate
events back to the original law:

* `zoom_event_mass`: a zoomed event of the form `label ∧ rebased block ∧ P`
  has original mass `W` times its zoomed mass;
* `pullback_mass`: a zoomed mass floor `N^(-ε) q' ν'(A)` becomes the original
  floor `N^(-ε) q ν(A)`;
* `strip_pullback`: zoomed velocity strips become original strips of width
  `g |λ|` times the zoomed width.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- Preimage of a rebased block event under the time zoom. -/
theorem preimage_zoom_event {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) (Bset : Set α) (Φ : α → Prop) :
    zoomTime (blockStart TQ jQ) ((2 : ℝ) ^ (-(TQ : ℤ))) ⁻¹'
        {w : α × ℝ | w.1 ∈ Bset ∧ w.2 ∈ interval (T - TQ) (relFin h) ∧ Φ w.1} =
      {w : α × ℝ | w.1 ∈ Bset ∧ w.2 ∈ interval T j ∧ Φ w.1} := by
  ext w
  simp only [mem_preimage, zoomTime, mem_ofPred_eq]
  rw [← zoom_interval h w.2]

/-- Zoomed mass of a rebased block event. -/
theorem zoom_event_mass (ρ : Measure (α × ℝ)) {G : Set (α × ℝ)} (hG : MeasurableSet G)
    {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) (Bset : Set α) (Φ : α → Prop) (W : ℝ≥0∞)
    (hmeas : MeasurableSet {w : α × ℝ | w.1 ∈ Bset ∧ w.2 ∈ interval (T - TQ) (relFin h) ∧
      Φ w.1}) :
    zoomLaw ρ G (blockStart TQ jQ) ((2 : ℝ) ^ (-(TQ : ℤ))) W
        {w | w.1 ∈ Bset ∧ w.2 ∈ interval (T - TQ) (relFin h) ∧ Φ w.1} =
      W⁻¹ * ρ (G ∩ {w | w.1 ∈ Bset ∧ w.2 ∈ interval T j ∧ Φ w.1}) := by
  rw [zoomLaw_apply ρ hG _ _ W hmeas, preimage_zoom_event h Bset Φ]

/-- **Mass floors pull back.** -/
theorem pullback_mass {ν : Measure α} {ρ : Measure (α × ℝ)} {G : Set (α × ℝ)}
    (hG : MeasurableSet G) {AQ A : Set α} (hA : MeasurableSet A) (hAQ : A ⊆ AQ)
    (hν0 : ν AQ ≠ 0) (hνt : ν AQ ≠ ⊤)
    {T TQ : ℕ} {j : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) (Bset : Set α) (Φ : α → Prop)
    (hmeas : MeasurableSet {w : α × ℝ | w.1 ∈ Bset ∧ w.2 ∈ interval (T - TQ) (relFin h) ∧
      Φ w.1})
    {c : ℝ}
    (hfloor : ENNReal.ofReal (c * (2 : ℝ) ^ (-((T - TQ : ℕ) : ℤ))) * condPrior ν AQ A ≤
      zoomLaw ρ G (blockStart TQ jQ) ((2 : ℝ) ^ (-(TQ : ℤ)))
        (ENNReal.ofReal ((2 : ℝ) ^ (-(TQ : ℤ))) * ν AQ)
        {w | w.1 ∈ Bset ∧ w.2 ∈ interval (T - TQ) (relFin h) ∧ Φ w.1}) :
    ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) * ν A ≤
      ρ (G ∩ {w | w.1 ∈ Bset ∧ w.2 ∈ interval T j ∧ Φ w.1}) := by
  rw [zoom_event_mass ρ hG h Bset Φ _ hmeas, condPrior_apply ν AQ A hA,
    inter_eq_left.mpr hAQ] at hfloor
  have hTQ := level_le_of_interval_subset h
  set qQ : ℝ := (2 : ℝ) ^ (-(TQ : ℤ))
  have hqQ : 0 < qQ := by positivity
  have hrel : (2 : ℝ) ^ (-((T - TQ : ℕ) : ℤ)) = (2 : ℝ) ^ (-(T : ℤ)) / qQ := rel_length hTQ
  set X := ρ (G ∩ {w | w.1 ∈ Bset ∧ w.2 ∈ interval T j ∧ Φ w.1})
  have hW0 : ENNReal.ofReal qQ * ν AQ ≠ 0 := mul_ne_zero (by simp [hqQ]) hν0
  have hWt : ENNReal.ofReal qQ * ν AQ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνt
  -- multiply the floor by `W`
  have h2 := mul_le_mul_right hfloor (ENNReal.ofReal qQ * ν AQ)
  rw [← mul_assoc (ENNReal.ofReal qQ * ν AQ) _ X, ENNReal.mul_inv_cancel hW0 hWt, one_mul] at h2
  refine le_trans (le_of_eq ?_) h2
  rw [hrel]
  have hq0 : ENNReal.ofReal qQ ≠ 0 := by simp [hqQ]
  have hqt : ENNReal.ofReal qQ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [mul_div_assoc', ENNReal.ofReal_div_of_pos hqQ]
  -- `qQ ν(AQ) · (c 2^-T / qQ) (ν(AQ))⁻¹ ν(A) = c 2^-T ν(A)`
  have e1 : ENNReal.ofReal qQ * ν AQ *
      (ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) / ENNReal.ofReal qQ * ((ν AQ)⁻¹ * ν A)) =
      ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) * ν A *
        ((ENNReal.ofReal qQ * (ENNReal.ofReal qQ)⁻¹) * (ν AQ * (ν AQ)⁻¹)) := by
    rw [ENNReal.div_eq_inv_mul]; ring
  rw [e1, ENNReal.mul_inv_cancel hq0 hqt, ENNReal.mul_inv_cancel hν0 hνt, one_mul, mul_one]

/-- **Strips pull back.** A zoomed velocity strip of width `E'` is an original
strip of width `g |λ| E'`. -/
theorem strip_pullback {Z : Zoom} (hZ : Z.Ok) {B : Fin 2 → ℝ} {lam : ℝ} (hlam : lam ≠ 0)
    {b : Fin 6 → ℝ} {z : Fin 2 → ℝ} {E' : ℝ}
    (h : |Zoom.nCoeff Z B lam b 4 - z 0 - z 1 * Zoom.nCoeff Z B lam b 3| ≤ E') :
    |b 4 - (Z.c₃ + Z.w / Z.q * (B 0 + lam * z 0)) -
        (Z.c₄ + Z.w / Z.q * (B 1 + lam * z 1)) * b 3| ≤ |Z.w / Z.q * lam| * E' := by
  have hq := hZ.q_ne
  have hw := hZ.w_ne
  have e : b 4 - (Z.c₃ + Z.w / Z.q * (B 0 + lam * z 0)) -
      (Z.c₄ + Z.w / Z.q * (B 1 + lam * z 1)) * b 3 =
      Z.w / Z.q * lam * (Zoom.nCoeff Z B lam b 4 - z 0 - z 1 * Zoom.nCoeff Z B lam b 3) := by
    simp only [Zoom.nCoeff, Submission.Lib.K4ContactNormalization.skewCoeff, Zoom.coeff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

end

end Submission.Lib.K4ContactTransfer
