import Submission.Obl.k4_horizontal_supercritical_three_projections.Layers
import Submission.Obl.k4_horizontal_supercritical_three_projections.Slicing
import Submission.Obl.k4_horizontal_supercritical_three_projections.PhysicalReturn

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Scalar predictions before the first intercept is sliced to the common fine mesh.
The three coarse tags are direction, first intercept, and second intercept. -/
structure CoarseProjectionLayer (α : Type) where
  n : ℕ
  A : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  P : Fin n → MvPolynomial (Fin 2) ℝ

namespace CoarseProjectionLayer

variable {α : Type} [MeasurableSpace α]

structure Certified (L : CoarseProjectionLayer α) (b : α → Fin 6 → ℝ)
    (χ D H E B error : ℝ) : Prop where
  measurable : ∀ i, MeasurableSet (L.A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (L.A i) (L.A j)
  corner : ∀ i,
    |(L.q i 0 : ℝ) * χ| + |(L.q i 1 : ℝ) * D| + |(L.q i 2 : ℝ) * D| ≤ H
  degree : ∀ i, (L.P i).totalDegree ≤ 2
  coeff : ∀ i e, |(L.P i).coeff e| ≤ B
  coordinates : ∀ i l, l ∈ L.A i →
    ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 1 / D⌋ = L.q i 2 ∧
    b l 0 ∈ Ico ((L.q i 1 : ℝ) * D) ((L.q i 1 : ℝ) * D + D) ∧
    |b l 1 - (L.q i 2 : ℝ) * D| ≤ D ∧
    (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ E
  fit : ∀ i l, l ∈ L.A i → ∀ t ∈ Icc (0 : ℝ) 1,
    |b l 2 + t * b l 5 - MvPolynomial.eval
      ![t, (b l 1 - (L.q i 2 : ℝ) * D) / D -
        2 * t * ((b l 0 - (L.q i 1 : ℝ) * D) / D)] (L.P i)| ≤ error

noncomputable def weight (L : CoarseProjectionLayer α) (π : Measure ℝ)
    (χ D a d : ℝ) (i : Fin L.n) : ℝ :=
  (π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ))).toReal * D ^ 2 * a ^ d

end CoarseProjectionLayer

/-- Closed bounds on the rounding error of the left endpoint of a mesh bin. -/
theorem fine_intercept_error {x χ : ℝ} {j : ℤ} (hχ : 0 < χ) (hj : ⌊x / χ⌋ = j) :
    |x - (j : ℝ) * χ| ≤ χ := by
  have hlo := Int.floor_le (x / χ)
  have hhi := Int.lt_floor_add_one (x / χ)
  rw [hj] at hlo hhi
  have hlo' := (le_div_iff₀ hχ).mp hlo
  have hhi' := (div_lt_iff₀ hχ).mp hhi
  rw [abs_le]
  constructor <;> nlinarith

/-- Return a coarse scalar family after the common fine intercept slicing.
The only loss of current mass is the explicit light-slice reference budget. -/
theorem refine_coarse_layer {α : Type} [MeasurableSpace α]
    {N d depth ε R χ D H E B error : ℝ} (hN : 1 ≤ N) (hD : 0 < D) (hD₁ : D ≤ 1)
    (hχ : 0 < χ) (hχD : χ ≤ D) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hround : E + χ ≤ D)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (π : Measure ℝ) [IsFiniteMeasure π]
    (ζ ρ : Measure (α × ℝ)) (hζρ : ζ ≤ ρ)
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (L : CoarseProjectionLayer α) (hL : L.Certified b χ D H E B error)
    (hpalette : ∀ i, 0 < π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ)))
    (hcorner : H + 2 ≤ N ^ ε) (hnorm : 150 * B ≤ N ^ ε)
    (hfit : error + 16 * B * ((E + χ) / D) ≤ N ^ ε * N ^ (-depth))
    (hcoeff : 9 * B * ((1 + 4 * (H + 2)) / D) ^ 2 ≤ N ^ R)
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
  let w := L.weight π χ D (N ^ (-depth)) d
  have hw (i) : 0 ≤ w i := by unfold w CoarseProjectionLayer.weight; positivity
  have hwpos (i) : 0 < w i := by
    have hp : 0 < (π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ))).toReal :=
      ENNReal.toReal_pos (hpalette i).ne' (measure_ne_top _ _)
    unfold w CoarseProjectionLayer.weight
    exact mul_pos (mul_pos hp (sq_pos_of_pos hD)) (Real.rpow_pos_of_pos ha _)
  have hfinite (i) := finite_intercept_bins (L.A i) (fun l => b l 0) hD.le hχ (by
    intro l hl l' hl'
    have hl₀ := (hL.coordinates i l hl).2.2.1
    have hl₀' := (hL.coordinates i l' hl').2.2.1
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
    heavy_intercept_slices ζ L.A (fun l => b l 0) bins w hD hχ hχD
      (inv_nonneg.mpr (Real.rpow_pos_of_pos hN₀ ε).le) hw hbins hcovbins
  let e := (Fintype.equivFin S).symm
  let idx : Fin (Fintype.card S) → Fin L.n × ℤ := fun j => (e j).val
  have hidx (j) : idx j ∈ S := (e j).property
  let L' : ProjectionLayer α := {
    n := Fintype.card S
    C := fun j => interceptSlice L.A (fun l => b l 0) χ (idx j)
    q := fun j => ![L.q (idx j).1 0, (idx j).2, L.q (idx j).1 2]
    G := fun j => physicalPredictor (L.P (idx j).1) ((L.q (idx j).1 1 : ℝ) * D)
      ((L.q (idx j).1 2 : ℝ) * D) ((idx j).2 * χ) D }
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
      have hc := hL.coordinates q.1 l hlA
      have hpc : |b l 0 - (L.q q.1 1 : ℝ) * D| ≤ D := by
        rw [abs_le]
        exact ⟨by linarith [hc.2.2.1.1], by linarith [hc.2.2.1.2]⟩
      have hpapc : |(q.2 : ℝ) * χ - (L.q q.1 1 : ℝ) * D| ≤ D + χ := by
        calc
          _ ≤ |(q.2 : ℝ) * χ - b l 0| + |b l 0 - (L.q q.1 1 : ℝ) * D| := abs_sub_le _ _ _
          _ ≤ χ + D := add_le_add (by simpa only [abs_sub_comm] using hpa) hpc
          _ = _ := add_comm _ _
      have hfine : |(q.2 : ℝ) * χ| ≤ |(L.q q.1 1 : ℝ) * D| + D + χ := by
        have htri := abs_add_le ((q.2 : ℝ) * χ - (L.q q.1 1 : ℝ) * D)
          ((L.q q.1 1 : ℝ) * D)
        rw [sub_add_cancel] at htri
        linarith
      have hcorner' : |(L.q q.1 0 : ℝ) * χ| + |(q.2 : ℝ) * χ| +
          |(L.q q.1 2 : ℝ) * D| ≤ N ^ ε := by
        have := hL.corner q.1
        linarith [hχD, hD₁]
      have hpcH : |(L.q q.1 1 : ℝ) * D| ≤ H + 2 := by
        linarith [hL.corner q.1, abs_nonneg ((L.q q.1 0 : ℝ) * χ),
          abs_nonneg ((L.q q.1 2 : ℝ) * D)]
      have hqcH : |(L.q q.1 2 : ℝ) * D| ≤ H + 2 := by
        linarith [hL.corner q.1, abs_nonneg ((L.q q.1 0 : ℝ) * χ),
          abs_nonneg ((L.q q.1 1 : ℝ) * D)]
      have hpaH : |(q.2 : ℝ) * χ| ≤ H + 2 := by
        linarith [hL.corner q.1, abs_nonneg ((L.q q.1 0 : ℝ) * χ),
          abs_nonneg ((L.q q.1 2 : ℝ) * D)]
      refine ⟨?_, hcorner', physicalPredictor_degree (hL.degree q.1) _ _ _ _, ?_, ?_, ?_, ?_⟩
      · intro l' hl'
        have hh := hL.coordinates q.1 l' hl'.1
        exact ⟨hh.1, hl'.2, hh.2.1, fun e => (hh.2.2.2.2.1 e).trans (by linarith)⟩
      · intro mon
        exact (physicalPredictor_coeff (hL.degree q.1) hB (hL.coeff q.1)
          (by linarith) hD hD₁ hpcH hqcH hpaH mon).trans hcoeff
      · intro t ht w hw
        exact (physicalPredictor_moving_norm (hL.degree q.1) hB hD (hL.coeff q.1)
          (by
            change |(L.q q.1 1 : ℝ) * D - (q.2 : ℝ) * χ| ≤ 2 * D
            rw [abs_sub_comm]
            linarith) ht hw).trans hnorm
      · intro l' hl' t ht
        have hh := hL.coordinates q.1 l' hl'.1
        have hpa' := fine_intercept_error hχ hl'.2
        have ht₁ : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
        have hpc' : |b l' 0 - (L.q q.1 1 : ℝ) * D| ≤ D := by
          rw [abs_le]
          exact ⟨by linarith [hh.2.2.1.1], by linarith [hh.2.2.1.2]⟩
        have hcenter : |b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D + t * ((q.2 : ℝ) * χ)| ≤
            D + E + χ := by
          have heq : b l' 1 + t * b l' 4 - (L.q q.1 2 : ℝ) * D + t * ((q.2 : ℝ) * χ) =
              (b l' 1 - (L.q q.1 2 : ℝ) * D) + t * ((b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)) := by ring
          rw [heq]
          calc
            _ ≤ |b l' 1 - (L.q q.1 2 : ℝ) * D| + |t| *
                |(b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)| := by
              simpa only [abs_mul] using abs_add_le
                (b l' 1 - (L.q q.1 2 : ℝ) * D)
                (t * ((b l' 4 + b l' 0) - (b l' 0 - (q.2 : ℝ) * χ)))
            _ ≤ D + 1 * (E + χ) := add_le_add hh.2.2.2.1
              (mul_le_mul ht₁ ((abs_sub _ _).trans (add_le_add hh.2.2.2.2.2 hpa'))
                (abs_nonneg _) zero_le_one)
            _ = _ := by ring
        have hr : |(b l' 1 - (L.q q.1 2 : ℝ) * D) / D -
            2 * t * ((b l' 0 - (L.q q.1 1 : ℝ) * D) / D)| ≤ 3 := by
          have h₁ : |(b l' 1 - (L.q q.1 2 : ℝ) * D) / D| ≤ 1 := by
            rw [abs_div, abs_of_pos hD]; exact (div_le_one hD).mpr hh.2.2.2.1
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
          have he := returned_parameter_error hD ht₁ hh.2.2.2.2.2 hpa'
            (pc := (L.q q.1 1 : ℝ) * D) (qc := (L.q q.1 2 : ℝ) * D) (q := b l' 1)
          have hrnd : (E + χ) / D ≤ 1 := (div_le_one hD).mpr hround
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
        · apply (physicalPredictor_fit (hL.degree q.1) hB (show (1 : ℝ) ≤ 4 by norm_num)
            hD (hL.coeff q.1) ht₁ hh.2.2.2.2.2 hpa' (hr.trans (by norm_num)) hr'
            (hL.fit q.1 l' hl'.1 t ht)).trans
          convert hfit using 1; ring
      · apply le_trans ?_ (hζρ _)
        have hf := hfloor q hmem
        have hpal := measure_ne_top π (Ico ((L.q q.1 0 : ℝ) * χ) (((L.q q.1 0 : ℝ) + 1) * χ))
        have hid := sliced_weight_identity hpal hD.ne' χ (N ^ (-depth)) d hχ.le hD.le ha.le
        change ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d / N ^ ε) *
          π (Ico ((L.q q.1 0 : ℝ) * χ) (((L.q q.1 0 : ℝ) + 1) * χ)) ≤ _
        convert hf using 1
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), mul_right_comm]
        rw [hid, ← ENNReal.ofReal_mul]
        · congr 1; dsimp [w, CoarseProjectionLayer.weight]; ring
        · positivity
    · have hsum' : (∑ j, ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d) *
          π (Ico ((L'.q j 0 : ℝ) * χ) (((L'.q j 0 : ℝ) + 1) * χ))) =
          ∑ q ∈ S, ENNReal.ofReal (w q.1 * χ / D) := by
        calc
          _ = ∑ j, ENNReal.ofReal (w (idx j).1 * χ / D) := by
            apply Finset.sum_congr rfl
            intro j _
            exact sliced_weight_identity (measure_ne_top π _) hD.ne' χ (N ^ (-depth)) d hχ.le hD.le ha.le
          _ = _ := by
            simpa only [idx] using
              (Equiv.sum_comp e (fun q : S => ENNReal.ofReal (w q.val.1 * χ / D))).trans
                (Finset.sum_coe_sort S (fun q => ENNReal.ofReal (w q.1 * χ / D)))
      rw [hsum']
      exact hsum.trans (ENNReal.ofReal_le_ofReal hbudget)
  · have hlost' : ζ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p ∉ L'.covered} ≤
        ENNReal.ofReal ((N ^ ε)⁻¹ * (4 * ∑ i, w i)) := by simpa only [hcover, Set.mem_ofPred_eq] using hlost
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
      _ ≤ ζ ((L'.covered ∪ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p ∉ L'.covered}) ∪
          (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := measure_mono hsub
      _ ≤ (ζ L'.covered + ζ {p | (∃ i, p.1 ∈ L.A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p ∉ L'.covered}) +
          ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ζ' univ + ENNReal.ofReal ((N ^ ε)⁻¹ * (4 * ∑ i, w i)) := by
        rw [hsupp, add_zero, show ζ' univ = ζ L'.covered from Measure.restrict_apply_univ _]
        exact add_le_add le_rfl hlost'

end Submission.Obl.k4_horizontal_supercritical_three_projections
