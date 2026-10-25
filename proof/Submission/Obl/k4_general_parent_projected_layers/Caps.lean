import Submission.Obl.k4_general_parent_projected_layers.Signal
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_general_parent_projected_layers

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- Moving-box integration preserves an arbitrary original palette factor. -/
theorem projected_cap_with_palette {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (condition : α × ℝ → Prop)
    {delta sigma g chi L C y₀ y₁ z₀ z₁ : ℝ} {W : ℝ≥0∞}
    (hW : W ≠ ⊤)
    (hd : 0 < delta) (hs : 0 < sigma) (hg : 0 < g) (hc : 0 ≤ chi)
    (hdr : delta ≤ sigma) (hdz : delta ≤ 2 * chi) (hdy : delta ≤ g * sigma)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hz₁ : |z₁| ≤ L) (hy₁ : |y₁| ≤ L)
    (hmz : L * delta ≤ 2 * chi) (hmy : L * delta ≤ g * sigma)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (basePoint (b p.1) p.2) = q ∧ condition p} ≤
        ENNReal.ofReal (C * delta ^ 3) * W)
    (q : Fin 2 → ℤ) :
    μ {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ b p.1 ∈ majorGroup chi z₀ z₁ ∧
      projectedCell sigma g y₀ y₁ (b p.1) p.2 = q ∧ condition p} ≤
      ENNReal.ofReal (1200 * C * sigma ^ 2 * chi * g) * W := by
  have hcap' (w : Fin 3 → ℤ) :
      μ {p | baseMesh delta (basePoint (b p.1) p.2) = w ∧ condition p} ≤
        ENNReal.ofReal ((C * W.toReal) * delta ^ 3) := by
    apply (hcap w).trans_eq
    rw [show (C * W.toReal) * delta ^ 3 = (C * delta ^ 3) * W.toReal by ring]
    symm
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * delta ^ 3),
      ENNReal.ofReal_toReal hW]
  have H := projected_cell_cap μ b condition (y₀ := y₀) (y₁ := y₁)
    (z₀ := z₀) (z₁ := z₁) hd hs hg hc hdr hdz hdy hL
    (mul_nonneg hC ENNReal.toReal_nonneg) hz₁ hy₁ hmz hmy hcap' q
  apply H.trans_eq
  rw [show 1200 * (C * W.toReal) * sigma ^ 2 * chi * g =
      (1200 * C * sigma ^ 2 * chi * g) * W.toReal by ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hW]

/-- Four coefficient bins define the original projected group. -/
def group (b : Fin 6 → ℝ) (chi g : ℝ) (tag gamma : Fin 2 → ℤ) : Prop :=
  ⌊b 3 / chi⌋ = tag 0 ∧ ⌊b 0 / chi⌋ = tag 1 ∧
    ⌊b 1 / g⌋ = gamma 0 ∧ ⌊b 4 / g⌋ = gamma 1

theorem measurableSet_group {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (chi g : ℝ)
    (tag gamma : Fin 2 → ℤ) : MeasurableSet {l | group (b l) chi g tag gamma} := by
  have he (i : Fin 6) (h : ℝ) : Measurable (fun l => ⌊b l i / h⌋ : α → ℤ) :=
    Int.measurable_floor.comp (((measurable_pi_apply i).comp hb).div_const h)
  exact (he 3 chi (measurableSet_singleton (tag 0))).inter
    ((he 0 chi (measurableSet_singleton (tag 1))).inter
      ((he 1 g (measurableSet_singleton (gamma 0))).inter
        (he 4 g (measurableSet_singleton (gamma 1)))))

theorem group_major {b : Fin 6 → ℝ} {chi g : ℝ} {tag gamma : Fin 2 → ℤ}
    (hc : 0 < chi) (hb : group b chi g tag gamma) :
    b ∈ majorGroup chi ((tag 1 : ℝ) * chi) ((tag 0 : ℝ) * chi) := by
  have he := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hc
  have h₀ := he (b 0)
  have h₁ := he (b 3)
  rw [hb.2.1, mul_comm chi] at h₀
  rw [hb.1, mul_comm chi] at h₁
  exact ⟨h₀, h₁⟩

/-- The exact scalar mesh cell of the five interpolation coefficients. -/
theorem scalarCoeff_cell (P : MvPolynomial (Fin 4) ℝ) (sigma g y₀ y₁ : ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    (![⌊t / sigma⌋,
      ⌊(scalarCoeff P g y₀ y₁ b 0 + t * scalarCoeff P g y₀ y₁ b 1) / sigma⌋] : Fin 2 → ℤ) =
      projectedCell sigma g y₀ y₁ b t := by
  rw [scalarCoeff_y]
  rfl

/-- The projected signal ceiling follows from the original native joint cap.
The original velocity bin and its palette weight are retained throughout. -/
theorem scalar_group_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {delta sigma g chi L C width : ℝ} (tag gamma : Fin 2 → ℤ)
    (W : ℝ≥0∞) (hW : W ≠ ⊤)
    (hd : 0 < delta) (hs : 0 < sigma) (hg : 0 < g) (hc : 0 < chi)
    (hdr : delta ≤ sigma) (hdz : delta ≤ 2 * chi) (hdy : delta ≤ g * sigma)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hz₁ : |(tag 0 : ℝ) * chi| ≤ L) (hy₁ : |(gamma 1 : ℝ) * g| ≤ L)
    (hmz : L * delta ≤ 2 * chi) (hmy : L * delta ≤ g * sigma)
    (hcap : ∀ (w : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh delta (basePoint (b p.1) p.2) = w ∧
        ⌊signal P (b p.1) p.2 / width⌋ = j ∧ ⌊b p.1 3 / chi⌋ = tag 0} ≤
        ENNReal.ofReal (C * delta ^ 3) * W)
    (q : Fin 2 → ℤ) (j : ℤ) :
    μ {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ group (b p.1) chi g tag gamma ∧
      (![⌊p.2 / sigma⌋,
        ⌊(scalarCoeff P g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g) (b p.1) 0 +
          p.2 * scalarCoeff P g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g) (b p.1) 1) /
            sigma⌋] : Fin 2 → ℤ) = q ∧
      ⌊(scalarCoeff P g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g) (b p.1) 2 +
        p.2 * scalarCoeff P g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g) (b p.1) 3 +
        p.2 ^ 2 * scalarCoeff P g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g) (b p.1) 4) /
          width⌋ = j} ≤
      ENNReal.ofReal (1200 * C * sigma ^ 2 * chi * g) * W := by
  have H := projected_cap_with_palette μ b
      (fun p => ⌊signal P (b p.1) p.2 / width⌋ = j ∧ ⌊b p.1 3 / chi⌋ = tag 0)
      (y₀ := (gamma 0 : ℝ) * g) (y₁ := (gamma 1 : ℝ) * g)
      (z₀ := (tag 1 : ℝ) * chi) (z₁ := (tag 0 : ℝ) * chi)
      hW hd hs hg hc.le hdr hdz hdy hL hC hz₁ hy₁ hmz hmy
      (fun w => hcap w j) q
  apply (measure_mono ?_).trans H
  intro p hp
  exact ⟨hp.1, group_major hc hp.2.1,
    (scalarCoeff_cell P sigma g ((gamma 0 : ℝ) * g) ((gamma 1 : ℝ) * g)
      (b p.1) p.2).symm.trans hp.2.2.1,
    by simpa only [scalarCoeff_x P hP] using hp.2.2.2, hp.2.1.1⟩

end

end Submission.Obl.k4_general_parent_projected_layers
