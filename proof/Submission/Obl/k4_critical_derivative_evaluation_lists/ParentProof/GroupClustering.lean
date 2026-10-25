/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupClustering.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ScalarWeightedCover

/-! Scalar clustering inside one initial-position/velocity group, stated in the
original unnormalized residual units: the group law is divided by its
reference weight `W` only to apply the normalized clustering theorem. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

/-- One group with reference weight `W`: heavy full-time coefficient bins carry
all but `W N^(-ηc)` of the group's residual mass, each with mass at least
`W N^(-s d - ε)`. -/
theorem group_heavy_cover_original {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (d s ε N ηc W : ℝ) (hW : 0 < W) (hN : 0 < N)
    (hcl : ∀ (ν' : Measure α) (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
        (a : α → EuclideanSpace ℝ (Fin 3)) (D : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
        Measurable a → MeasurableSet D → D ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → μ Dᶜ = 0 →
        μ ≤ ENNReal.ofReal (N ^ ηc) • (ν'.prod volume) →
        (∀ l, ‖a l‖ ≤ N ^ ηc) → ν' Set.univ ≤ ENNReal.ofReal (N ^ ηc) →
        (F.card : ℝ) ≤ N ^ ηc * (N ^ (-s)) ^ (-1 - d) →
        (∀ l t, (l, t) ∈ D →
          (⌊t / (N ^ (-s))⌋, ⌊quadratic (a l) t / (N ^ (-s))⌋) ∈ F) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-s) ≤ r →
          (∃ l, a l ∈ Metric.ball b r) →
          μ {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
            ENNReal.ofReal (N ^ ηc * r ^ d)) →
        ∃ G : Finset (Fin 3 → ℤ),
          (∀ q ∈ G, ENNReal.ofReal (N ^ (-s * d - ε)) ≤
            μ {p | coefficientCode (N ^ (-s)) (a p.1) = q}) ∧
          (G.card : ℝ) ≤ μ.real Set.univ / N ^ (-s * d - ε) ∧
          μ {p | coefficientCode (N ^ (-s)) (a p.1) ∉ G} < ENNReal.ofReal (N ^ (-ηc)))
    (X : Set α) (hX : MeasurableSet X) (D : Set (α × ℝ)) (hD : MeasurableSet D)
    (hDunit : D ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (coeff : α → Coeff) (hcm : Measurable coeff) (hnorm : ∀ l, ‖coeff l‖ ≤ N ^ ηc)
    (hdom : ρ.restrict D ≤ ENNReal.ofReal (N ^ ηc) • ((ν.restrict X).prod volume))
    (hνX : ν X ≤ ENNReal.ofReal (N ^ ηc * W))
    (F : Finset (ℤ × ℤ)) (hF : (F.card : ℝ) ≤ N ^ ηc * (N ^ (-s)) ^ (-1 - d))
    (hsupp : ∀ l t, (l, t) ∈ D →
      (⌊t / (N ^ (-s))⌋, ⌊quadratic (coeff l) t / (N ^ (-s))⌋) ∈ F)
    (hband : ∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-s) ≤ r →
      (∃ l, coeff l ∈ Metric.ball b r) →
      ρ (D ∩ {p | |quadratic (coeff p.1) p.2 - quadratic b p.2| ≤ 3 * r}) ≤
        ENNReal.ofReal (W * (N ^ ηc * r ^ d))) :
    ∃ G : Finset (Fin 3 → ℤ),
      (∀ q ∈ G, ENNReal.ofReal (W * N ^ (-s * d - ε)) ≤
        ρ (D ∩ {p | coefficientCode (N ^ (-s)) (coeff p.1) = q})) ∧
      (G.card : ℝ) ≤ ρ.real D / (W * N ^ (-s * d - ε)) ∧
      ρ (D ∩ {p | coefficientCode (N ^ (-s)) (coeff p.1) ∉ G}) ≤
        ENNReal.ofReal (W * N ^ (-ηc)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal W⁻¹
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hW)
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcW : c * ENNReal.ofReal W = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hW.le), inv_mul_cancel₀ hW.ne', ENNReal.ofReal_one]
  have hWc : ENNReal.ofReal W * c = 1 := by rw [mul_comm]; exact hcW
  let μ : Measure (α × ℝ) := c • ρ.restrict D
  let ν' : Measure α := c • ν.restrict X
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp only [μ, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hμset (U : Set (α × ℝ)) : μ U = c * ρ (U ∩ D) := by
    simp only [μ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hD]
  have hDnull : μ Dᶜ = 0 := by
    rw [hμset]
    simp
  have hdomμ : μ ≤ ENNReal.ofReal (N ^ ηc) • (ν'.prod volume) := by
    intro U
    simp only [μ, ν', Measure.smul_apply, smul_eq_mul, Measure.prod_smul_left]
    calc
      c * (ρ.restrict D) U ≤ c * (ENNReal.ofReal (N ^ ηc) * ((ν.restrict X).prod volume) U) := by
        gcongr
        exact hdom U
      _ = _ := by ring
  have hν' : ν' Set.univ ≤ ENNReal.ofReal (N ^ ηc) := by
    simp only [ν', Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    calc
      c * ν X ≤ c * ENNReal.ofReal (N ^ ηc * W) := by gcongr
      _ = ENNReal.ofReal (N ^ ηc) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), mul_comm, mul_assoc, hWc, mul_one]
  have hbandμ : ∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-s) ≤ r →
      (∃ l, coeff l ∈ Metric.ball b r) →
      μ {p | |quadratic (coeff p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
        ENNReal.ofReal (N ^ ηc * r ^ d) := by
    intro b r hr hex
    rw [hμset, Set.inter_comm]
    have hr0 : 0 ≤ r := (Real.rpow_nonneg hN.le _).trans hr
    calc
      c * ρ (D ∩ {p | |quadratic (coeff p.1) p.2 - quadratic b p.2| ≤ 3 * r}) ≤
          c * ENNReal.ofReal (W * (N ^ ηc * r ^ d)) := by gcongr; exact hband b r hr hex
      _ = _ := by
        rw [ENNReal.ofReal_mul hW.le, ← mul_assoc, hcW, one_mul]
  obtain ⟨G, hfloor, hcount, hexcl⟩ := hcl ν' μ coeff D F hcm hD hDunit hDnull hdomμ hnorm hν'
    hF hsupp hbandμ
  refine ⟨G, ?_, ?_, ?_⟩
  · intro q hq
    have hh := hfloor q hq
    rw [hμset, Set.inter_comm] at hh
    calc
      ENNReal.ofReal (W * N ^ (-s * d - ε)) =
          ENNReal.ofReal W * ENNReal.ofReal (N ^ (-s * d - ε)) :=
        ENNReal.ofReal_mul hW.le
      _ ≤ ENNReal.ofReal W * (c * ρ (D ∩ {p | coefficientCode (N ^ (-s)) (coeff p.1) = q})) := by
        gcongr
      _ = _ := by rw [← mul_assoc, hWc, one_mul]
  · have hμreal : μ.real Set.univ = W⁻¹ * ρ.real D := by
      rw [measureReal_def, hμset, Set.univ_inter, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hW.le), measureReal_def]
    rw [hμreal] at hcount
    calc
      (G.card : ℝ) ≤ W⁻¹ * ρ.real D / N ^ (-s * d - ε) := hcount
      _ = ρ.real D / (W * N ^ (-s * d - ε)) := by
        field_simp
  · have hh := hexcl.le
    rw [hμset, Set.inter_comm] at hh
    calc
      ρ (D ∩ {p | coefficientCode (N ^ (-s)) (coeff p.1) ∉ G}) =
          ENNReal.ofReal W * (c * ρ (D ∩ {p | coefficientCode (N ^ (-s)) (coeff p.1) ∉ G})) := by
        rw [← mul_assoc, hWc, one_mul]
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal (N ^ (-ηc)) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hW.le).symm

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
