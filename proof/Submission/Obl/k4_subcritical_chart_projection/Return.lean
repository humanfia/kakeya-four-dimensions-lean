import Submission.Obl.k4_subcritical_chart_projection.LayerDefs
import Submission.Obl.k4_horizontal_supercritical_three_projections.Refinement
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs

/-!
# Physical return of corrected scalar layers

A corrected coarse layer stores, on disjoint assignments inside corrected
parameter charts, the original chart labels, the chart baseline `g` and a
quadratic `P` in the scalar coordinates `(t, R)`, with a full-time fit of the
corrected signal `(x₃ - g(t, b₀, b₁)) / A₀ ≈ P(t, R)`.

`refine_corrected_layer` slices the first intercept to the fine mesh `χ`, keeps
the heavy slices (floors measured in the current law, hence in every larger
original law), and returns each slice to a physical quadratic in `(t, Y)`:
the baseline with the intercept frozen, plus `A₀` times the returned scalar
polynomial. It follows o226's `refine_coarse_layer`, adding the baseline.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections
  (ProjectionLayer physicalPredictor physicalPredictor_eval physicalPredictor_degree
    physicalPredictor_coeff physicalPredictor_moving_norm physicalPredictor_fit
    returned_parameter_error fine_intercept_error finite_intercept_bins
    heavy_intercept_slices interceptSlice measurableSet_interceptSlice
    disjoint_interceptSlice sliced_weight_identity floor_cell_mem)
open Submission.Obl.k4_fixed_budget_quadratic_recovery
  (quadraticPolynomial quadraticValue eval_quadraticPolynomial quadraticPolynomial_degree
    quadraticPolynomial_coeff_bound)

noncomputable section

namespace CorrectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The unsliced reference numerator `π(bin) D² a^d` of an assignment. -/
def weight (L : CorrectedLayer α) (π : Measure ℝ) (χ D a d : ℝ) (i : Fin L.n) : ℝ :=
  (π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ))).toReal * D ^ 2 * a ^ d

end CorrectedLayer

/-- The six coefficients of the baseline with the first intercept frozen at
`pa`, written in the physical coordinates `(t, Y)`, `Y = b₁ + t b₄ ≈ b₁ - t pa`. -/
def baselineCoefficients (g : Fin 6 → ℝ) (pa : ℝ) : Fin 6 → ℝ :=
  ![g 0 + g 2 * pa, g 1 + g 3 * pa + g 4 * pa, g 4, g 5 * pa, g 5, 0]

/-- The baseline with frozen intercept as a quadratic polynomial in `(t, Y)`. -/
def baselinePolynomial (g : Fin 6 → ℝ) (pa : ℝ) : MvPolynomial (Fin 2) ℝ :=
  quadraticPolynomial (baselineCoefficients g pa)

theorem baselinePolynomial_eval (g : Fin 6 → ℝ) (pa t Y : ℝ) :
    MvPolynomial.eval ![t, Y] (baselinePolynomial g pa) =
      predictor g t pa (Y + t * pa) := by
  rw [baselinePolynomial, eval_quadraticPolynomial]
  simp only [quadraticValue, baselineCoefficients, predictor,
    Submission.Lib.K4FullTimeLayers.parameterPredictor, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem baselinePolynomial_coeff {g : Fin 6 → ℝ} {Γ pa : ℝ} (hΓ : 0 ≤ Γ)
    (hg : ∀ e, |g e| ≤ Γ) (e : Fin 2 →₀ ℕ) :
    |(baselinePolynomial g pa).coeff e| ≤ 6 * (Γ * (1 + 2 * |pa|)) := by
  have hpa := abs_nonneg pa
  have hc : ∀ i, |baselineCoefficients g pa i| ≤ Γ * (1 + 2 * |pa|) := by
    have h0 := hg 0
    have h1 := hg 1
    have h2 := hg 2
    have h3 := hg 3
    have h4 := hg 4
    have h5 := hg 5
    intro i
    fin_cases i <;>
      simp only [baselineCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, abs_zero]
    · calc |g 0 + g 2 * pa| ≤ |g 0| + |g 2| * |pa| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ Γ + Γ * |pa| := add_le_add h0 (mul_le_mul_of_nonneg_right h2 hpa)
        _ ≤ _ := by nlinarith
    · calc |g 1 + g 3 * pa + g 4 * pa| ≤ |g 1| + |g 3| * |pa| + |g 4| * |pa| := by
            rw [← abs_mul, ← abs_mul]
            exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ Γ + Γ * |pa| + Γ * |pa| :=
            add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h3 hpa))
              (mul_le_mul_of_nonneg_right h4 hpa)
        _ = _ := by ring
    · nlinarith
    · rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right h5 hpa]
    · nlinarith
    · nlinarith
  exact quadraticPolynomial_coeff_bound (by positivity) hc e

/-- The physical predictor of one fine slice: frozen baseline plus the returned
scalar polynomial, scaled by the corrected signal width `A₀`. -/
def slicePolynomial (g : Fin 6 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (pc qc pa D A₀ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  baselinePolynomial g pa + A₀ • physicalPredictor P pc qc pa D

theorem slicePolynomial_eval (g : Fin 6 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (pc qc pa D A₀ t Y : ℝ) :
    MvPolynomial.eval ![t, Y] (slicePolynomial g P pc qc pa D A₀) =
      predictor g t pa (Y + t * pa) +
        A₀ * MvPolynomial.eval ![t, Y] (physicalPredictor P pc qc pa D) := by
  rw [slicePolynomial, map_add, baselinePolynomial_eval, MvPolynomial.smul_eval]

theorem slicePolynomial_degree (g : Fin 6 → ℝ) {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) (pc qc pa D A₀ : ℝ) :
    (slicePolynomial g P pc qc pa D A₀).totalDegree ≤ 2 := by
  unfold slicePolynomial
  refine (totalDegree_add _ _).trans (max_le (quadraticPolynomial_degree _) ?_)
  exact (totalDegree_smul_le _ _).trans (physicalPredictor_degree hP _ _ _ _)

theorem slicePolynomial_coeff (g : Fin 6 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    {pc qc pa D A₀ X Y : ℝ} (hA₀ : 0 ≤ A₀)
    (hX : ∀ e, |(baselinePolynomial g pa).coeff e| ≤ X)
    (hY : ∀ e, |(physicalPredictor P pc qc pa D).coeff e| ≤ Y) (e : Fin 2 →₀ ℕ) :
    |(slicePolynomial g P pc qc pa D A₀).coeff e| ≤ X + A₀ * Y := by
  rw [slicePolynomial, MvPolynomial.coeff_add, coeff_smul, smul_eq_mul]
  calc _ ≤ |(baselinePolynomial g pa).coeff e| +
        |A₀ * (physicalPredictor P pc qc pa D).coeff e| := abs_add_le _ _
    _ ≤ X + A₀ * Y := by
        rw [abs_mul, abs_of_nonneg hA₀]
        exact add_le_add (hX e) (mul_le_mul_of_nonneg_left (hY e) hA₀)

/-- The two intercept slopes of the baseline at any fixed time are controlled
by the full parameter-square norm. -/
theorem predictor_slopes {g : Fin 6 → ℝ} {pc qc D H t : ℝ} (hD : 0 < D)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D),
      ∀ q ∈ Icc qc (qc + D), |predictor g t p q| ≤ H) :
    |g 2 + g 3 * t| ≤ 2 * H / D ∧ |g 4 + g 5 * t| ≤ 2 * H / D := by
  have hp : pc ∈ Icc pc (pc + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hq : qc ∈ Icc qc (qc + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hpD : pc + D ∈ Icc pc (pc + D) := ⟨hp.2, le_rfl⟩
  have hqD : qc + D ∈ Icc qc (qc + D) := ⟨hq.2, le_rfl⟩
  have h00 := hnorm t ht pc hp qc hq
  have h10 := hnorm t ht (pc + D) hpD qc hq
  have h01 := hnorm t ht pc hp (qc + D) hqD
  simp only [predictor, Submission.Lib.K4FullTimeLayers.parameterPredictor] at h00 h10 h01
  apply Submission.Lib.K4FullTimeLayers.affine_square_slopes hD
    (a := g 0 + g 1 * t) (p := pc) (q := qc)
  · convert h00 using 2
  · convert h10 using 2
  · convert h01 using 2

/-- Freezing the first intercept and reading the second one off the physical
coordinate costs only the fine errors divided by the chart width. -/
theorem predictor_frozen_error {g : Fin 6 → ℝ} {pc qc D H t E χ p q slope pa : ℝ}
    (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D),
      ∀ q ∈ Icc qc (qc + D), |predictor g t p q| ≤ H)
    (hcontact : |slope + p| ≤ E) (hintercept : |p - pa| ≤ χ) :
    |predictor g t p q - predictor g t pa (q + t * slope + t * pa)| ≤
      2 * H / D * χ + 2 * H / D * (E + χ) := by
  obtain ⟨h1, h2⟩ := predictor_slopes hD ht hnorm
  have ht₁ : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have heq : predictor g t p q - predictor g t pa (q + t * slope + t * pa) =
      (g 2 + g 3 * t) * (p - pa) + (g 4 + g 5 * t) * (-(t * ((slope + p) - (p - pa)))) := by
    simp only [predictor, Submission.Lib.K4FullTimeLayers.parameterPredictor]
    ring
  have hE : 0 ≤ E := (abs_nonneg _).trans hcontact
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hintercept
  have hH : 0 ≤ 2 * H / D := (abs_nonneg _).trans h1
  rw [heq]
  calc _ ≤ |(g 2 + g 3 * t) * (p - pa)| +
        |(g 4 + g 5 * t) * (-(t * ((slope + p) - (p - pa))))| := abs_add_le _ _
    _ ≤ 2 * H / D * χ + 2 * H / D * (E + χ) := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul]
        apply add_le_add (mul_le_mul h1 hintercept (abs_nonneg _) hH)
        apply mul_le_mul h2 _ (by positivity) hH
        calc |t| * |slope + p - (p - pa)| ≤ 1 * (E + χ) :=
              mul_le_mul ht₁ ((abs_sub _ _).trans (add_le_add hcontact hintercept))
                (abs_nonneg _) zero_le_one
          _ = E + χ := one_mul _

/-- The coarse coordinates of a corrected assignment, in the form used by o226. -/
theorem certified_coordinates {α : Type} [MeasurableSpace α] {L : CorrectedLayer α}
    {b : α → Fin 6 → ℝ} {χ D A₀ H B error : ℝ} (hL : L.Certified b χ D A₀ H B error)
    (hD : 0 < D) (hχ : 0 < χ) (i : Fin L.n) {l : α} (hl : l ∈ L.A i) :
    b l 0 ∈ Ico ((L.q i 1 : ℝ) * D) ((L.q i 1 : ℝ) * D + D) ∧
      b l 1 ∈ Ico ((L.q i 2 : ℝ) * D) ((L.q i 2 : ℝ) * D + D) ∧
      |b l 3 - (L.q i 0 : ℝ) * χ| ≤ χ := by
  obtain ⟨h3, h0, h1, -, -⟩ := hL.bins i l hl
  obtain ⟨hp₀, hp₁⟩ := floor_cell_mem (x := b l 0) hD
  obtain ⟨hq₀, hq₁⟩ := floor_cell_mem (x := b l 1) hD
  rw [h0] at hp₀ hp₁
  rw [h1] at hq₀ hq₁
  refine ⟨⟨hp₀, by linarith⟩, ⟨hq₀, by linarith⟩, fine_intercept_error hχ h3⟩


/-- The coordinates of a corrected assignment used by the return. -/
theorem certified_box {α : Type} [MeasurableSpace α] {L : CorrectedLayer α}
    {b : α → Fin 6 → ℝ} {χ D A₀ H B error : ℝ} (hL : L.Certified b χ D A₀ H B error)
    (hD : 0 < D) (hχ : 0 < χ) (i : Fin L.n) {l : α} (hl : l ∈ L.A i) :
    ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 1 / D⌋ = L.q i 2 ∧
      b l 0 ∈ Ico ((L.q i 1 : ℝ) * D) ((L.q i 1 : ℝ) * D + D) ∧
      |b l 1 - (L.q i 2 : ℝ) * D| ≤ D ∧ (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ χ ∧
      |b l 3 - (L.q i 0 : ℝ) * χ| ≤ χ := by
  obtain ⟨h3, -, h1, hH, hE⟩ := hL.bins i l hl
  obtain ⟨hp, hq, hv⟩ := certified_coordinates hL hD hχ i hl
  refine ⟨h3, h1, hp, ?_, hH, hE, hv⟩
  rw [abs_le]
  constructor <;> linarith [hq.1, hq.2]

/-- **Corrected physical return.** Slice the first intercept of a certified
corrected layer to the fine mesh `χ`, keep the heavy slices, and return each to
a physical quadratic in `(t, Y)`. The only loss of current mass is the explicit
light-slice reference budget; all floors are in the current law `ζ ≤ ρ`. -/
theorem refine_corrected_layer {α : Type} [MeasurableSpace α]
    {N d depth ε R χ D A₀ H B error : ℝ} (hN : 1 ≤ N) (hD : 0 < D) (hD₁ : D ≤ 1)
    (hχ : 0 < χ) (hχD : 2 * χ ≤ D) (hA₀ : 0 < A₀) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (π : Measure ℝ) [IsFiniteMeasure π]
    (ζ ρ : Measure (α × ℝ)) (hζρ : ζ ≤ ρ)
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (L : CorrectedLayer α) (hL : L.Certified b χ D A₀ H B error)
    (hpalette : ∀ i, 0 < π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ)))
    (hcorner : 3 * H + 3 ≤ N ^ ε)
    (hnorm : 5 * H + A₀ * (150 * B) ≤ N ^ ε)
    (hfit : A₀ * (error + 4 * B * 4 * ((χ + χ) / D)) +
      (2 * H / D * χ + 2 * H / D * (χ + χ)) ≤ N ^ ε * N ^ (-depth))
    (hcoeff : 6 * ((2 * (H + 2 * H / D * (2 * (H + 1) + 1))) * (1 + 2 * (H + 1))) +
      A₀ * (9 * B * ((1 + 4 * (H + 1)) / D) ^ 2) ≤ N ^ R)
    (hbudget : 4 * ∑ i, L.weight π χ D (N ^ (-depth)) d i ≤ N ^ ε) :
    ∃ (ζ' : Measure (α × ℝ)) (L' : ProjectionLayer α),
      ζ' ≤ ζ ∧ (∀ᵐ p ∂ζ', p ∈ L'.covered) ∧
      L'.Good N d depth ε R χ D b π ρ ∧
      ζ {p | ∃ i, p.1 ∈ L.A i} ≤ ζ' univ +
        ENNReal.ofReal ((N ^ ε)⁻¹ *
          (4 * ∑ i, L.weight π χ D (N ^ (-depth)) d i)) := by
  classical
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have ha : 0 < N ^ (-depth) := Real.rpow_pos_of_pos hN₀ _
  have hχD' : χ ≤ D := by linarith
  have hχ₁ : χ ≤ 1 := hχD'.trans hD₁
  let w := L.weight π χ D (N ^ (-depth)) d
  have hw (i) : 0 ≤ w i := by unfold w CorrectedLayer.weight; positivity
  have hwpos (i) : 0 < w i := by
    have hp : 0 < (π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ))).toReal :=
      ENNReal.toReal_pos (hpalette i).ne' (measure_ne_top _ _)
    unfold w CorrectedLayer.weight
    exact mul_pos (mul_pos hp (sq_pos_of_pos hD)) (Real.rpow_pos_of_pos ha _)
  have hfinite (i) := finite_intercept_bins (L.A i) (fun l => b l 0) hD.le hχ (by
    intro l hl l' hl'
    have hl₀ := (certified_box hL hD hχ i hl).2.2.1
    have hl₀' := (certified_box hL hD hχ i hl').2.2.1
    rw [abs_le]
    constructor <;> linarith [hl₀.1, hl₀.2, hl₀'.1, hl₀'.2])
  let bins := fun i => (hfinite i).1.toFinset
  have hbins (i) : ((bins i).card : ℝ) ≤ 2 * D / χ + 2 := by
    change ((hfinite i).1.toFinset.card : ℝ) ≤ _
    rw [← Set.ncard_eq_toFinset_card _ (hfinite i).1]
    exact (hfinite i).2
  have hcovbins (i) (l) (hl : l ∈ L.A i) : ⌊b l 0 / χ⌋ ∈ bins i := by
    simpa only [bins, Set.Finite.mem_toFinset] using
      (show ⌊b l 0 / χ⌋ ∈ (fun l => ⌊b l 0 / χ⌋) '' L.A i from ⟨l, hl, rfl⟩)
  obtain ⟨S, hS, hfloor, hsum, hlost⟩ :=
    heavy_intercept_slices ζ L.A (fun l => b l 0) bins w hD hχ hχD'
      (inv_nonneg.mpr (Real.rpow_pos_of_pos hN₀ ε).le) hw hbins hcovbins
  let e := (Fintype.equivFin S).symm
  let idx : Fin (Fintype.card S) → Fin L.n × ℤ := fun j => (e j).val
  have hidx (j) : idx j ∈ S := (e j).property
  let L' : ProjectionLayer α := {
    n := Fintype.card S
    C := fun j => interceptSlice L.A (fun l => b l 0) χ (idx j)
    q := fun j => ![L.q (idx j).1 0, (idx j).2, L.q (idx j).1 2]
    G := fun j => slicePolynomial (L.g (idx j).1) (L.P (idx j).1)
      ((L.q (idx j).1 1 : ℝ) * D) ((L.q (idx j).1 2 : ℝ) * D) ((idx j).2 * χ) D A₀ }
  have hC (j) : MeasurableSet (L'.C j) :=
    measurableSet_interceptSlice hL.measurable ((measurable_pi_apply 0).comp hb) χ (idx j)
  have hcover : L'.covered = {p : α × ℝ | ∃ q ∈ S,
      p.1 ∈ interceptSlice L.A (fun l => b l 0) χ q} := by
    ext p
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨idx j, hidx j, hj⟩
    · rintro ⟨q, hq, hp⟩
      refine ⟨e.symm ⟨q, hq⟩, ?_⟩
      simpa only [L', idx, e.apply_symm_apply] using hp
  have hcovered : MeasurableSet L'.covered := by
    change MeasurableSet {p : α × ℝ | ∃ j, p.1 ∈ L'.C j}
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun j => (hC j).preimage measurable_fst
  let ζ' := ζ.restrict L'.covered
  refine ⟨ζ', L', Measure.restrict_le_self, ae_restrict_mem hcovered, ?_, ?_⟩
  · refine ⟨hC, ?_, ?_, ?_⟩
    · intro j j' hjj'
      apply disjoint_interceptSlice (fun l => b l 0) χ hL.disjoint
      intro heq
      apply hjj'
      exact e.injective (Subtype.ext heq)
    · intro j
      let q := idx j
      have hmem := hidx j
      have hmasspos : 0 < ζ (L'.C j ×ˢ Icc (0 : ℝ) 1) := by
        apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ?_) (hfloor q hmem)
        exact mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos hN₀ _))
          (div_pos (mul_pos (hwpos q.1) hχ) hD)
      obtain ⟨l, hl⟩ : (L'.C j).Nonempty := by
        obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hmasspos.ne'
        exact ⟨p.1, hp.1⟩
      have hlA := hl.1
      have hpa : |b l 0 - (q.2 : ℝ) * χ| ≤ χ := fine_intercept_error hχ hl.2
      obtain ⟨hc3, hc1, hc0, hc1', hcH, hcE, hcv⟩ := certified_box hL hD hχ q.1 hlA
      have hpcH : |(L.q q.1 1 : ℝ) * D| ≤ H + 1 := by
        have := hcH 0
        rw [abs_le] at this ⊢
        constructor <;> linarith [hc0.1, hc0.2]
      have hqcH : |(L.q q.1 2 : ℝ) * D| ≤ H + 1 := by
        have := hcH 1
        rw [abs_le] at hc1' this ⊢
        constructor <;> linarith
      have hpaH : |(q.2 : ℝ) * χ| ≤ H + 1 := by
        have := hcH 0
        rw [abs_le] at hpa this ⊢
        constructor <;> linarith
      have hvH : |(L.q q.1 0 : ℝ) * χ| ≤ H + 1 := by
        have := hcH 3
        rw [abs_le] at hcv this ⊢
        constructor <;> linarith
      have hpa_lo : (q.2 : ℝ) * χ ≤ b l 0 := by
        have h := (floor_cell_mem (x := b l 0) hχ).1
        rw [hl.2] at h
        exact h
      have hpapc : |(q.2 : ℝ) * χ - (L.q q.1 1 : ℝ) * D| ≤ D := by
        rw [abs_le] at hpa ⊢
        constructor <;> linarith [hc0.1, hc0.2]
      have hcorner' : |(L.q q.1 0 : ℝ) * χ| + |(q.2 : ℝ) * χ| +
          |(L.q q.1 2 : ℝ) * D| ≤ N ^ ε := by linarith
      have hHN : H ≤ N ^ ε := by linarith
      -- the baseline coefficients
      have hnorm' : ∀ t ∈ Icc (0 : ℝ) 1,
          ∀ p ∈ Icc ((L.q q.1 1 : ℝ) * D) ((L.q q.1 1 : ℝ) * D + D),
          ∀ q' ∈ Icc ((L.q q.1 2 : ℝ) * D) ((L.q q.1 2 : ℝ) * D + D),
            |predictor (L.g q.1) t p q'| ≤ H := by
        intro t ht p hp q' hq'
        apply hL.norm q.1 t ht p ⟨hp.1, by linarith [hp.2]⟩ q' ⟨hq'.1, by linarith [hq'.2]⟩
      have hgcoeff := Submission.Lib.K4FullTimeLayers.parameterPredictor_coefficients hD hnorm'
      have hΓ : ∀ e, |L.g q.1 e| ≤ 2 * (H + 2 * H / D * (2 * (H + 1) + 1)) := by
        intro e
        refine (hgcoeff e).trans ?_
        have h2HD : 0 ≤ 2 * H / D := by positivity
        have := mul_le_mul_of_nonneg_left
          (show |(L.q q.1 1 : ℝ) * D| + |(L.q q.1 2 : ℝ) * D| + 1 ≤ 2 * (H + 1) + 1 by
            linarith) h2HD
        linarith
      refine ⟨?_, hcorner', slicePolynomial_degree _ (hL.degree q.1) _ _ _ _ _, ?_, ?_, ?_, ?_⟩
      · intro l' hl'
        obtain ⟨h3, h1, -, -, hH', -, -⟩ := certified_box hL hD hχ q.1 hl'.1
        exact ⟨h3, hl'.2, h1, fun e => (hH' e).trans hHN⟩
      · intro mon
        refine (slicePolynomial_coeff _ _ hA₀.le
          (baselinePolynomial_coeff (by positivity) hΓ)
          (physicalPredictor_coeff (hL.degree q.1) hB (hL.coeff q.1)
            (by linarith) hD hD₁ hpcH hqcH hpaH) mon).trans ?_
        refine le_trans (add_le_add ?_ le_rfl) hcoeff
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      · intro t ht w hw
        change |MvPolynomial.eval ![t, (L.q q.1 2 : ℝ) * D - t * ((q.2 : ℝ) * χ) + D * w]
          (slicePolynomial (L.g q.1) (L.P q.1) ((L.q q.1 1 : ℝ) * D)
            ((L.q q.1 2 : ℝ) * D) ((q.2 : ℝ) * χ) D A₀)| ≤ N ^ ε
        rw [slicePolynomial_eval]
        have hbase : |predictor (L.g q.1) t ((q.2 : ℝ) * χ)
            ((L.q q.1 2 : ℝ) * D - t * ((q.2 : ℝ) * χ) + D * w + t * ((q.2 : ℝ) * χ))| ≤
            H + 4 * H * D / D := by
          have heq : (L.q q.1 2 : ℝ) * D - t * ((q.2 : ℝ) * χ) + D * w +
              t * ((q.2 : ℝ) * χ) = (L.q q.1 2 : ℝ) * D + D * w := by ring
          rw [heq]
          apply Submission.Lib.K4FullTimeLayers.parameterPredictor_extension hD ht hnorm'
            (p₀ := (L.q q.1 1 : ℝ) * D) (q₀ := (L.q q.1 2 : ℝ) * D)
            ⟨le_rfl, by linarith⟩ ⟨le_rfl, by linarith⟩
          · exact hpapc
          · have hw' : |w| ≤ 1 := abs_le.mpr hw
            rw [show (L.q q.1 2 : ℝ) * D + D * w - (L.q q.1 2 : ℝ) * D = D * w by ring,
              abs_mul, abs_of_pos hD]
            nlinarith
        have hphys := physicalPredictor_moving_norm (hL.degree q.1) hB hD (hL.coeff q.1)
          (pc := (L.q q.1 1 : ℝ) * D) (qc := (L.q q.1 2 : ℝ) * D) (pa := (q.2 : ℝ) * χ)
          (by rw [abs_sub_comm]; linarith) ht hw
        have hDD : 4 * H * D / D = 4 * H := by field_simp
        rw [hDD] at hbase
        calc _ ≤ |predictor (L.g q.1) t ((q.2 : ℝ) * χ)
              ((L.q q.1 2 : ℝ) * D - t * ((q.2 : ℝ) * χ) + D * w + t * ((q.2 : ℝ) * χ))| +
              |A₀ * MvPolynomial.eval ![t, (L.q q.1 2 : ℝ) * D - t * ((q.2 : ℝ) * χ) + D * w]
                (physicalPredictor (L.P q.1) ((L.q q.1 1 : ℝ) * D) ((L.q q.1 2 : ℝ) * D)
                  ((q.2 : ℝ) * χ) D)| := abs_add_le _ _
          _ ≤ (H + 4 * H) + A₀ * (150 * B) := by
              rw [abs_mul, abs_of_pos hA₀]
              exact add_le_add hbase (mul_le_mul_of_nonneg_left hphys hA₀.le)
          _ ≤ N ^ ε := by linarith
      · intro l' hl' t ht
        obtain ⟨h3, h1, hp0, hp1, hH', hE', -⟩ := certified_box hL hD hχ q.1 hl'.1
        have hpa' := fine_intercept_error hχ hl'.2
        have ht₁ : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
        have hpc' : |b l' 0 - (L.q q.1 1 : ℝ) * D| ≤ D := by
          rw [abs_le]
          exact ⟨by linarith [hp0.1], by linarith [hp0.2]⟩
        have hcenter : |b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D + t * ((q.2 : ℝ) * χ)| ≤
            D + χ + χ := by
          have heq : b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D + t * ((q.2 : ℝ) * χ) =
              (b l' 1 - (L.q q.1 2 : ℝ) * D) +
                t * ((b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)) := by ring
          rw [heq]
          calc
            _ ≤ |b l' 1 - (L.q q.1 2 : ℝ) * D| + |t| *
                |(b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)| := by
              simpa only [abs_mul] using abs_add_le
                (b l' 1 - (L.q q.1 2 : ℝ) * D)
                (t * ((b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)))
            _ ≤ D + 1 * (χ + χ) := add_le_add hp1
              (mul_le_mul ht₁ ((abs_sub _ _).trans (add_le_add hE' hpa'))
                (abs_nonneg _) zero_le_one)
            _ = _ := by ring
        have hr : |(b l' 1 - (L.q q.1 2 : ℝ) * D) / D -
            2 * t * ((b l' 0 - (L.q q.1 1 : ℝ) * D) / D)| ≤ 3 := by
          have h₁ : |(b l' 1 - (L.q q.1 2 : ℝ) * D) / D| ≤ 1 := by
            rw [abs_div, abs_of_pos hD]; exact (div_le_one hD).mpr hp1
          have h₂ : |(b l' 0 - (L.q q.1 1 : ℝ) * D) / D| ≤ 1 := by
            rw [abs_div, abs_of_pos hD]; exact (div_le_one hD).mpr hpc'
          calc
            _ ≤ |(b l' 1 - (L.q q.1 2 : ℝ) * D) / D| +
                |2 * t * ((b l' 0 - (L.q q.1 1 : ℝ) * D) / D)| := abs_sub _ _
            _ ≤ 3 := by
              rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
              have hm := mul_le_mul ht₁ h₂ (abs_nonneg _) zero_le_one
              nlinarith
        have hr' : |(b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D +
            t * (2 * ((L.q q.1 1 : ℝ) * D) - (q.2 : ℝ) * χ)) / D| ≤ 4 := by
          have he := returned_parameter_error hD ht₁ hE' hpa'
            (pc := (L.q q.1 1 : ℝ) * D) (qc := (L.q q.1 2 : ℝ) * D) (q := b l' 1)
          have hrnd : (χ + χ) / D ≤ 1 := (div_le_one hD).mpr (by linarith)
          have htri := abs_add_le
            ((b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D +
              t * (2 * ((L.q q.1 1 : ℝ) * D) - (q.2 : ℝ) * χ)) / D -
                ((b l' 1 - (L.q q.1 2 : ℝ) * D) / D -
                  2 * t * ((b l' 0 - (L.q q.1 1 : ℝ) * D) / D)))
            ((b l' 1 - (L.q q.1 2 : ℝ) * D) / D -
              2 * t * ((b l' 0 - (L.q q.1 1 : ℝ) * D) / D))
          rw [sub_add_cancel] at htri
          linarith
        refine ⟨hcenter.trans ?_, ?_⟩
        · have hpow : 2 ≤ N ^ ε := by linarith
          nlinarith
        · -- the corrected fit, returned to physical coordinates
          have hsig := hL.fit q.1 l' hl'.1 t ht
          have hX := physicalPredictor_fit (hL.degree q.1) hB (show (1 : ℝ) ≤ 4 by norm_num)
            hD (hL.coeff q.1) ht₁ hE' hpa' (pc := (L.q q.1 1 : ℝ) * D)
            (qc := (L.q q.1 2 : ℝ) * D) (q := b l' 1) (hr.trans (by norm_num)) hr' (by
              simpa only [chartR, chartQ, chartP] using hsig)
          have hfrozen := predictor_frozen_error hD ht hnorm' hE' hpa' (q := b l' 1)
          change |(b l' 2 + t * b l' 5) - MvPolynomial.eval ![t, b l' 1 + t * b l' 4]
            (slicePolynomial (L.g q.1) (L.P q.1) ((L.q q.1 1 : ℝ) * D)
              ((L.q q.1 2 : ℝ) * D) ((q.2 : ℝ) * χ) D A₀)| ≤ N ^ ε * N ^ (-depth)
          rw [slicePolynomial_eval]
          have hsplit : (b l' 2 + t * b l' 5) -
              (predictor (L.g q.1) t ((q.2 : ℝ) * χ) (b l' 1 + t * b l' 4 + t * ((q.2 : ℝ) * χ)) +
                A₀ * MvPolynomial.eval ![t, b l' 1 + t * b l' 4]
                  (physicalPredictor (L.P q.1) ((L.q q.1 1 : ℝ) * D) ((L.q q.1 2 : ℝ) * D)
                    ((q.2 : ℝ) * χ) D)) =
              A₀ * (chartSignal A₀ (L.g q.1) (b l') t -
                MvPolynomial.eval ![t, b l' 1 + t * b l' 4]
                  (physicalPredictor (L.P q.1) ((L.q q.1 1 : ℝ) * D) ((L.q q.1 2 : ℝ) * D)
                    ((q.2 : ℝ) * χ) D)) +
              (predictor (L.g q.1) t (b l' 0) (b l' 1) -
                predictor (L.g q.1) t ((q.2 : ℝ) * χ)
                  (b l' 1 + t * b l' 4 + t * ((q.2 : ℝ) * χ))) := by
            simp only [chartSignal]
            field_simp
            ring
          rw [hsplit]
          calc _ ≤ |A₀ * (chartSignal A₀ (L.g q.1) (b l') t -
                MvPolynomial.eval ![t, b l' 1 + t * b l' 4]
                  (physicalPredictor (L.P q.1) ((L.q q.1 1 : ℝ) * D) ((L.q q.1 2 : ℝ) * D)
                    ((q.2 : ℝ) * χ) D))| +
                |predictor (L.g q.1) t (b l' 0) (b l' 1) -
                  predictor (L.g q.1) t ((q.2 : ℝ) * χ)
                    (b l' 1 + t * b l' 4 + t * ((q.2 : ℝ) * χ))| := abs_add_le _ _
            _ ≤ A₀ * (error + 4 * B * 4 * ((χ + χ) / D)) +
                (2 * H / D * χ + 2 * H / D * (χ + χ)) := by
                rw [abs_mul, abs_of_pos hA₀]
                exact add_le_add (mul_le_mul_of_nonneg_left hX hA₀.le) hfrozen
            _ ≤ _ := hfit
      · apply le_trans ?_ (hζρ _)
        have hf := hfloor q hmem
        have hpal := measure_ne_top π (Ico ((L.q q.1 0 : ℝ) * χ) (((L.q q.1 0 : ℝ) + 1) * χ))
        have hid := sliced_weight_identity hpal hD.ne' χ (N ^ (-depth)) d hχ.le hD.le ha.le
        change ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d / N ^ ε) *
          π (Ico ((L.q q.1 0 : ℝ) * χ) (((L.q q.1 0 : ℝ) + 1) * χ)) ≤ _
        convert hf using 1
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), mul_right_comm]
        rw [hid, ← ENNReal.ofReal_mul]
        · congr 1; dsimp [w, CorrectedLayer.weight]; ring
        · positivity
    · have hsum' : (∑ j, ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d) *
          π (Ico ((L'.q j 0 : ℝ) * χ) (((L'.q j 0 : ℝ) + 1) * χ))) =
          ∑ q ∈ S, ENNReal.ofReal (w q.1 * χ / D) := by
        calc
          _ = ∑ j, ENNReal.ofReal (w (idx j).1 * χ / D) := by
            apply Finset.sum_congr rfl
            intro j _
            exact sliced_weight_identity (measure_ne_top π _) hD.ne' χ (N ^ (-depth)) d
              hχ.le hD.le ha.le
          _ = _ := by
            simpa only [idx] using
              (Equiv.sum_comp e (fun q : S => ENNReal.ofReal (w q.val.1 * χ / D))).trans
                (Finset.sum_coe_sort S (fun q => ENNReal.ofReal (w q.1 * χ / D)))
      rw [hsum']
      exact hsum.trans (ENNReal.ofReal_le_ofReal hbudget)
  · have hlost' : ζ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p ∉ L'.covered} ≤
        ENNReal.ofReal ((N ^ ε)⁻¹ * (4 * ∑ i, w i)) := by
      simpa only [hcover, Set.mem_ofPred_eq] using hlost
    have hsub : {p : α × ℝ | ∃ i, p.1 ∈ L.A i} ⊆
        (L'.covered ∪ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p ∉ L'.covered}) ∪
          (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
      intro p hp
      by_cases ht : p.2 ∈ Icc (0 : ℝ) 1
      · by_cases hc : p ∈ L'.covered
        · exact Or.inl (Or.inl hc)
        · exact Or.inl (Or.inr ⟨hp, ht, hc⟩)
      · exact Or.inr (by simpa using ht)
    calc
      _ ≤ ζ ((L'.covered ∪ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
          p ∉ L'.covered}) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := measure_mono hsub
      _ ≤ (ζ L'.covered + ζ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
          p ∉ L'.covered}) + ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ζ' univ + ENNReal.ofReal ((N ^ ε)⁻¹ * (4 * ∑ i, w i)) := by
        rw [hsupp, add_zero, show ζ' univ = ζ L'.covered from Measure.restrict_apply_univ _]
        exact add_le_add le_rfl hlost'

end

end Submission.Obl.k4_subcritical_chart_projection
