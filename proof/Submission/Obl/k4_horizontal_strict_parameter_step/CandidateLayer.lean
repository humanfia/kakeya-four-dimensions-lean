import Submission.Obl.k4_horizontal_strict_parameter_step.RawChartReturn

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/CandidateLayer.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- A full-time candidate layer before restoring the individual current mass floors. -/
structure CandidateLayer (α : Type) [MeasurableSpace α] (ρ : Measure (α × ℝ))
    (π : Measure ℝ) (b : α → Fin 6 → ℝ) (d χ D a M m Q : ℝ) where
  n : ℕ
  A : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  h : Fin n → Fin 6 → ℝ
  measurable : ∀ i, MeasurableSet (A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  grid : ∀ i l, l ∈ A i → ⌊b l 3 / χ⌋ = q i 0 ∧ ⌊b l 0 / D⌋ = q i 1 ∧ ⌊b l 1 / D⌋ = q i 2
  norm : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((q i 1 : ℝ) * D) (((q i 1 : ℝ) + 1) * D),
    ∀ q' ∈ Icc ((q i 2 : ℝ) * D) (((q i 2 : ℝ) + 1) * D), |predictor (h i) t p q'| ≤ M
  fit : ∀ i l, l ∈ A i → ∀ t ∈ Icc (0 : ℝ) 1,
    |b l 2 + t * b l 5 - predictor (h i) t (b l 0) (b l 1)| ≤ 2 * a
  mass : ENNReal.ofReal m ≤ ρ ((⋃ i, A i) ×ˢ Icc (0 : ℝ) 1)
  budget : (∑ i, ENNReal.ofReal (D ^ 2 * a ^ d) *
    π (Ico ((q i 0 : ℝ) * χ) (((q i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal Q

/-- The first-jet calls on disjoint raw charts combine into one candidate layer.
The new numerator budget cancels the `w^-d` menu count against the thickness gain. -/
theorem candidateLayer_of_raw_charts {α : Type} [MeasurableSpace α]
    {ν : Measure α} {ρ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {d N ξ χ D a ζ ε w : ℝ}
    (H : RawChartFamily α ν ρ π b d N ξ χ D a ζ)
    (hb : Measurable b) (hN : 0 < N) (ha : 0 < a) (hD : 0 < D) (hw : 0 < w)
    (hcover : ∀ i, FirstJet.Cover ((H.chart i).prior ν) ((H.chart i).y b a D)
      ((H.chart i).β b a D) ((H.chart i).γ b a D) (H.chart i).E (H.chart i).F d N ε w) :
    Nonempty (CandidateLayer α ρ π b d χ D (a * w)
      (N ^ ξ + 18 * a * (2 * N ^ ξ + N ^ ε + w + 1))
      (N ^ (-(2 * ξ + ε))) (N ^ (ξ + ε))) := by
  classical
  choose n B h' hBm hBd hBA hcard hmass hfit hnorm using
    fun i => (H.chart i).return_cover (H.valid i) hb hN ha hD hw (hcover i)
  let Idx := (i : Fin H.n) × Fin (n i)
  let e : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  let A' : Fin (Fintype.card Idx) → Set α := fun k => B (e k).1 (e k).2
  let q' : Fin (Fintype.card Idx) → Fin 3 → ℤ := fun k => (H.chart (e k).1).q
  let h'' : Fin (Fintype.card Idx) → Fin 6 → ℝ := fun k => h' (e k).1 (e k).2
  let U : Fin H.n → Set α := fun i => ⋃ j, B i j
  have hU (i : Fin H.n) : MeasurableSet (U i) := MeasurableSet.iUnion (hBm i)
  have hUA (i : Fin H.n) : U i ⊆ (H.chart i).A := by
    intro l hl
    obtain ⟨j, hj⟩ := mem_iUnion.mp hl
    exact hBA i j hj
  have hUd : Pairwise (fun i i' => Disjoint (U i) (U i')) := by
    intro i i' hne
    exact (H.disjoint i i' hne).mono (hUA i) (hUA i')
  have hds : Pairwise (fun z z' : Idx => Disjoint (B z.1 z.2) (B z'.1 z'.2)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    by_cases hi : i = i'
    · subst i'
      apply hBd i j j'
      intro hj
      apply hne
      cases hj
      rfl
    · exact (H.disjoint i i' hi).mono (hBA i j) (hBA i' j')
  have hAd : Pairwise (fun i i' => Disjoint (A' i) (A' i')) := by
    intro k k' hne
    exact hds (by intro he; exact hne (e.injective he))
  have hAU : (⋃ k, A' k) = ⋃ i, U i := by
    ext l
    simp only [mem_iUnion, U]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(e k).1, (e k).2, hk⟩
    · rintro ⟨i, j, hl⟩
      refine ⟨e.symm ⟨i, j⟩, ?_⟩
      change l ∈ B (e (e.symm ⟨i, j⟩)).1 (e (e.symm ⟨i, j⟩)).2
      rw [e.apply_symm_apply]
      exact hl
  have hrect : (⋃ k, A' k) ×ˢ Icc (0 : ℝ) 1 = ⋃ i, U i ×ˢ Icc (0 : ℝ) 1 := by
    rw [hAU]
    ext p
    simp
  have hrectd : Pairwise (fun i i' => Disjoint (U i ×ˢ Icc (0 : ℝ) 1) (U i' ×ˢ Icc (0 : ℝ) 1)) := by
    intro i i' hne
    apply disjoint_left.mpr
    intro p hp hp'
    exact disjoint_left.mp (hUd hne) hp.1 hp'.1
  have hρsum : ρ ((⋃ k, A' k) ×ˢ Icc (0 : ℝ) 1) =
      ∑ i, ρ (U i ×ˢ Icc (0 : ℝ) 1) := by
    rw [hrect, measure_iUnion hrectd (fun i => (hU i).prod measurableSet_Icc), tsum_fintype]
  have hlower : ENNReal.ofReal (N ^ (-(2 * ξ + ε))) ≤
      ρ ((⋃ k, A' k) ×ˢ Icc (0 : ℝ) 1) := by
    calc
      _ = ENNReal.ofReal (N ^ (-(ξ + ε))) * ENNReal.ofReal (N ^ (-ξ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN]
        congr 1
        congr 1
        ring
      _ ≤ ENNReal.ofReal (N ^ (-(ξ + ε))) * ∑ i, ν (H.chart i).A :=
        mul_le_mul_of_nonneg_left H.dense_prior zero_le
      _ = ∑ i, ENNReal.ofReal (N ^ (-(ξ + ε))) * ν (H.chart i).A := Finset.mul_sum _ _ _
      _ ≤ ∑ i, ρ (U i ×ˢ Icc (0 : ℝ) 1) := Finset.sum_le_sum (fun i _ => hmass i)
      _ = _ := hρsum.symm
  have hweight (i : Fin H.n) : (n i : ENNReal) * ENNReal.ofReal (D ^ 2 * (a * w) ^ d) ≤
      ENNReal.ofReal (N ^ ε) * ENNReal.ofReal (D ^ 2 * a ^ d) := by
    have hr := jet_floor_budget ha.le hw (sq_nonneg D) (hcard i)
    have hr' : (n i : ℝ) * (D ^ 2 * (a * w) ^ d) ≤ N ^ ε * (D ^ 2 * a ^ d) := by
      convert hr using 1 <;> ring
    have hh := ENNReal.ofReal_le_ofReal hr'
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)] at hh
    exact hh
  have hbud : (∑ k, ENNReal.ofReal (D ^ 2 * (a * w) ^ d) *
      π (Ico ((q' k 0 : ℝ) * χ) (((q' k 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N ^ (ξ + ε)) := by
    let W : Idx → ENNReal := fun z => ENNReal.ofReal (D ^ 2 * (a * w) ^ d) *
      π (Ico (((H.chart z.1).q 0 : ℝ) * χ) ((((H.chart z.1).q 0 : ℝ) + 1) * χ))
    change (∑ k, W (e k)) ≤ _
    rw [Equiv.sum_comp e, Fintype.sum_sigma]
    calc
      _ = ∑ i, ((n i : ENNReal) * ENNReal.ofReal (D ^ 2 * (a * w) ^ d)) *
          π (Ico (((H.chart i).q 0 : ℝ) * χ) ((((H.chart i).q 0 : ℝ) + 1) * χ)) := by
        simp only [W, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i, (ENNReal.ofReal (N ^ ε) * ENNReal.ofReal (D ^ 2 * a ^ d)) *
          π (Ico (((H.chart i).q 0 : ℝ) * χ) ((((H.chart i).q 0 : ℝ) + 1) * χ)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hweight i) zero_le)
      _ = ENNReal.ofReal (N ^ ε) * ∑ i, ENNReal.ofReal (D ^ 2 * a ^ d) *
          π (Ico (((H.chart i).q 0 : ℝ) * χ) ((((H.chart i).q 0 : ℝ) + 1) * χ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ENNReal.ofReal (N ^ ε) * ENNReal.ofReal (N ^ ξ) :=
        mul_le_mul_of_nonneg_left H.numerator_budget zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
        congr 1
        congr 1
        ring
  refine ⟨{
    n := Fintype.card Idx
    A := A'
    q := q'
    h := h''
    measurable := fun k => hBm _ _
    disjoint := hAd
    grid := fun k l hl => (H.valid (e k).1).grid l (hBA _ _ hl)
    norm := fun k => hnorm (e k).1 (e k).2
    fit := ?_
    mass := hlower
    budget := hbud }⟩
  intro k l hl t ht
  exact (hfit (e k).1 (e k).2 l hl t ht).trans_eq (by ring)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
