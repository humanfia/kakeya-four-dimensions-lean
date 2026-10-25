import Submission.Obl.k4_horizontal_strict_parameter_step.RawCharts
import Submission.Obl.k4_horizontal_strict_parameter_step.JetReturn

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RawChartReturn.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- One raw chart and its first-jet cover give disjoint, finer full-time predictors,
with dense success measured in the original current law. -/
theorem RawChart.return_cover {α : Type} [MeasurableSpace α]
    (C : RawChart α) {ν : Measure α} {ρ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ}
    {d N ξ χ D a ζ ε w : ℝ} (H : C.Valid ν ρ b d N ξ χ D a ζ)
    (hb : Measurable b) (hN : 0 < N) (ha : 0 < a) (hD : 0 < D) (hw : 0 < w)
    (hcover : FirstJet.Cover (C.prior ν) (C.y b a D) (C.β b a D) (C.γ b a D)
      C.E C.F d N ε w) :
    ∃ (n : ℕ) (B : Fin n → Set α) (h' : Fin n → Fin 6 → ℝ),
      (∀ i, MeasurableSet (B i)) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ C.A) ∧ (n : ℝ) ≤ N ^ ε * w ^ (-d) ∧
      ENNReal.ofReal (N ^ (-(ξ + ε))) * ν C.A ≤ ρ ((⋃ i, B i) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ i l, l ∈ B i → ∀ t ∈ Icc (0 : ℝ) 1,
        |b l 2 + t * b l 5 - predictor (h' i) t (b l 0) (b l 1)| ≤ 2 * a * w) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ p ∈ Icc ((C.q 1 : ℝ) * D) (((C.q 1 : ℝ) + 1) * D),
        ∀ q ∈ Icc ((C.q 2 : ℝ) * D) (((C.q 2 : ℝ) + 1) * D),
          |predictor (h' i) t p q| ≤ N ^ ξ + 18 * a * (2 * N ^ ξ + N ^ ε + w + 1)) := by
  let p₀ := (C.q 1 : ℝ) * D
  let q₀ := (C.q 2 : ℝ) * D
  let r : α → Fin 2 → ℝ := fun l => normalizedAffine C.h a (b l 2) (b l 5) (b l 0) (b l 1)
  have hr : Measurable r := by dsimp [r, normalizedAffine]; fun_prop
  have hp₀ : p₀ + D = ((C.q 1 : ℝ) + 1) * D := by dsimp [p₀]; ring
  have hq₀ : q₀ + D = ((C.q 2 : ℝ) + 1) * D := by dsimp [q₀]; ring
  have hbox (l : α) (hl : l ∈ C.A) :
      b l 0 ∈ Icc p₀ (p₀ + D) ∧ b l 1 ∈ Icc q₀ (q₀ + D) := by
    have h0 := Int.floor_eq_iff.mp (H.grid l hl).2.1
    have h1 := Int.floor_eq_iff.mp (H.grid l hl).2.2
    rw [le_div_iff₀ hD, div_lt_iff₀ hD] at h0 h1
    rw [hp₀, hq₀]
    exact ⟨⟨h0.1, h0.2.le⟩, h1.1, h1.2.le⟩
  have hcoords (l : α) (hl : l ∈ C.A) :
      C.y b a D l 0 = (b l 0 - p₀) / D ∧ C.y b a D l 1 = (b l 1 - q₀) / D ∧
        C.β b a D l = r l 0 ∧ C.γ b a D l = r l 1 := by
    classical
    simp [RawChart.y, RawChart.β, RawChart.γ, RawChart.coordinates, chartCoordinates,
      Set.piecewise_eq_of_mem _ _ _ hl, p₀, q₀, r, hl]
  have hy (l : α) (hl : l ∈ C.A) :
      |(b l 0 - p₀) / D| ≤ 1 ∧ |(b l 1 - q₀) / D| ≤ 1 := by
    have h := hbox l hl
    constructor
    · rw [abs_of_nonneg (div_nonneg (by linarith [h.1.1]) hD.le), div_le_one hD]
      linarith [h.1.2]
    · rw [abs_of_nonneg (div_nonneg (by linarith [h.2.1]) hD.le), div_le_one hD]
      linarith [h.2.2]
  have hrbound (l : α) (hl : l ∈ C.A) :
      (∀ t ∈ Icc (0 : ℝ) 1, |r l 0 + t * r l 1| ≤ N ^ ξ) ∧ |r l 1| ≤ 2 * N ^ ξ := by
    have hh := normalizedAffine_bounds ha (H.fit l hl)
    exact ⟨hh.1, hh.2.2⟩
  obtain ⟨n, B, h', hBm, hBd, hBA, hcount, hmass, hfit, hnorm⟩ :=
    firstJet_cover_to_chart_family (C.prior ν) H.measurable_A (fun p hp => (H.labeled hp).1)
      hr ((measurable_pi_apply 0).comp hb) ((measurable_pi_apply 1).comp hb)
      (C.y b a D) (C.β b a D) (C.γ b a D) C.F C.h ha.le hD
      (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _) hN hw hcoords hy hrbound
      H.data.bound_F (by simpa only [hp₀, hq₀] using H.norm) hcover
  let U : Set α := ⋃ i, B i
  have hU : MeasurableSet U := MeasurableSet.iUnion hBm
  let V : Set (α × ℝ) := U ×ˢ Icc (0 : ℝ) 1
  have hV : MeasurableSet V := hU.prod measurableSet_Icc
  have heq : V ∩ C.E = C.E ∩ U ×ˢ univ := by
    ext p
    constructor
    · rintro ⟨⟨hpU, hpt⟩, hpE⟩
      exact ⟨hpE, hpU, mem_univ _⟩
    · rintro ⟨hpE, hpU, -⟩
      exact ⟨⟨hpU, (H.labeled hpE).2⟩, hpE⟩
  have hmassρ : ENNReal.ofReal (N ^ (-(ξ + ε))) * ν C.A ≤ ρ V := by
    calc
      _ = (ENNReal.ofReal (N ^ (-ξ)) * ν C.A) * ENNReal.ofReal (N ^ (-ε)) := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN]
        congr 2
        ring
      _ ≤ (ENNReal.ofReal (N ^ (-ξ)) * ν C.A) *
          ((C.prior ν).prod volume) (C.E ∩ U ×ˢ univ) := mul_le_mul_of_nonneg_left hmass zero_le
      _ = ((ENNReal.ofReal (N ^ (-ξ)) * ν C.A) •
          (((C.prior ν).prod volume).restrict C.E)) V := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hV, heq]
      _ ≤ (ρ.restrict (C.A ×ˢ Icc (0 : ℝ) 1)) V := H.lower V
      _ ≤ ρ V := Measure.restrict_le_self _
  refine ⟨n, B, h', hBm, hBd, hBA, hcount, hmassρ, ?_, ?_⟩
  · intro i l hl t ht
    rw [normalizedAffine_evolution C.h ha.ne' (b l 2) (b l 5) (b l 0) (b l 1) t]
    exact hfit i l hl t ht
  · intro i t ht p hp q hq
    have hh := hnorm i t ht p (by simpa only [hp₀] using hp) q (by simpa only [hq₀] using hq)
    convert hh using 1
    ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
