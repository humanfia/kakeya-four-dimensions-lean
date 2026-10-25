-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceFacts

/-!
# The determinant floors of the model labels

The relative frame `(q₀ / q) • (D₀⁻¹ Q)` of a model label has determinant `4^ΔT` times the
ratio of the label and parent determinants; the narrowness profile and the source depth map
bound it below by `(Nk^(uL))^(-ℓ s) / K` as soon as `Nk^(4 δ₀ L) ≤ K`. This is the field
`Inputs.det`, so it is no longer an input of a source stage.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W}

/-- The relative time scale of a later label is a power of two. -/
theorem q₀_div_eq (D : SourceData p) {T : ℕ} (hT : p.T D.i₀ ≤ T) :
    D.q₀ / (((2 : ℝ) ^ T)⁻¹) = (2 : ℝ) ^ (T - p.T D.i₀) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ p.T D.i₀ := by positivity
  rw [q₀, div_inv_eq_mul, inv_mul_eq_div, eq_comm, eq_div_iff h2.ne', ← pow_add,
    Nat.sub_add_cancel hT]

/-- The determinant of the relative frame of a later label. -/
theorem relative_det_eq (D : SourceData p) (Q : Matrix (Fin 2) (Fin 2) ℝ) {T : ℕ}
    (hT : p.T D.i₀ ≤ T) :
    |((D.q₀ / (((2 : ℝ) ^ T)⁻¹)) • (D.D₀⁻¹ * Q)).det| =
      (4 : ℝ) ^ (T - p.T D.i₀) * (|Q.det| / |D.D₀.det|) := by
  rw [D.q₀_div_eq hT, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', Fintype.card_fin, abs_mul, abs_mul, abs_inv, abs_pow, abs_pow,
    abs_two, ← pow_mul, mul_comm (T - p.T D.i₀) 2, pow_mul]
  norm_num
  ring

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The determinant floors of the model labels** (`Inputs.det`). -/
theorem det_field (D : SourceData p) (n : ℕ) {u mesh : ℝ}
    (hdepth : D.depth = sourceDepth m sg D.i₀ u)
    (hframe : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hNk : 1 ≤ Nk) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hu : 0 ≤ u) (hm : 0 < m)
    (hmesh0 : 0 ≤ mesh) (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh)
    (hroom : sg D.i₀ + u ≤ sg (m - 1)) (hKdet : Nk ^ (4 * δ₀ * L) ≤ D.K) :
    ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      (Nk ^ (u * L)) ^ (-ℓ * s) / D.K ≤
        |((D.q₀ / (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹)) •
          (D.D₀⁻¹ * p.frame (D.old s i))).det| := by
  intro s hs1 hs2 i
  have hN0 : 0 < Nk := by linarith
  have hi₀ : D.i₀ < m := hp.label_level D.parent
  have hs0 : 0 ≤ s := le_trans (inv_nonneg.mpr (Nat.cast_nonneg n)) hs1
  have hge : D.i₀ ≤ D.depth s := by rw [hdepth]; exact sourceDepth_ge sg hi₀ hu s
  have hTle := (D.old_bin_div hp hSo s hge i).1
  have hlev : p.lev (D.old s i) = D.depth s := D.old_level s i
  have hj : D.depth s < m := by rw [hdepth]; exact sourceDepth_lt hm sg D.i₀ u s
  have hnom := (sourceDepth_nominal hm hi₀ hu hmesh0 hmesh hroom hs0 hs2).1
  rw [← hdepth] at hnom
  have hnwj := (hp.level_bounds (D.depth s) hj).2.2.2.2.1
  have hnwi := (hp.level_bounds D.i₀ hi₀).2.2.2.2.1
  rw [abs_le] at hnwj hnwi
  have hT' : p.T (p.lev D.parent) ≤ p.T (p.lev (D.old s i)) := by rw [hlev]; exact hTle
  have hratio := (det_ratio_bounds hp hN0 D.parent (D.old s i) hT').1
  have hdet0 : (p.frame D.parent).det ≠ 0 := (hp.chart D.parent).1
  have hD₀ : |D.D₀.det| = |(p.frame D.parent).det| := by
    rw [hframe]; exact MajorFrame.abs_det hdet0
  have hTle' : p.T D.i₀ ≤ p.T (p.lev (D.old s i)) := by rw [hlev]; exact hTle
  rw [D.relative_det_eq (p.frame (D.old s i)) hTle', hD₀]
  -- the narrowness exponent
  set X := Nk ^ (-(p.nw (p.lev (D.old s i)) - p.nw (p.lev D.parent)) - 2 * δ₀ * L) with hX
  have h4 : (4 : ℝ) ^ (p.T (p.lev (D.old s i)) - p.T D.i₀) *
      ((4 : ℝ)⁻¹ ^ (p.T (p.lev (D.old s i)) - p.T (p.lev D.parent)) * X) = X := by
    have hi : p.T D.i₀ = p.T (p.lev D.parent) := rfl
    rw [hi, ← mul_assoc, ← mul_pow]
    norm_num
  have hXle : X ≤ (4 : ℝ) ^ (p.T (p.lev (D.old s i)) - p.T D.i₀) *
      (|(p.frame (D.old s i)).det| / |(p.frame D.parent).det|) := by
    rw [← h4]
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  refine le_trans ?_ hXle
  have hexp : -(ℓ * u * s * L) - 4 * δ₀ * L ≤
      -(p.nw (p.lev (D.old s i)) - p.nw (p.lev D.parent)) - 2 * δ₀ * L := by
    have h := mul_le_mul_of_nonneg_left hnom (mul_nonneg hℓ hL)
    rw [hlev]
    simp only [i₀] at hnwi h
    nlinarith
  calc (Nk ^ (u * L)) ^ (-ℓ * s) / D.K
      = Nk ^ (-(ℓ * u * s * L)) / D.K := by
        rw [← Real.rpow_mul hN0.le]; congr 2; ring
    _ ≤ Nk ^ (-(ℓ * u * s * L)) / Nk ^ (4 * δ₀ * L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hKdet
    _ = Nk ^ (-(ℓ * u * s * L) - 4 * δ₀ * L) := by
        rw [Real.rpow_sub hN0]
    _ ≤ X := Real.rpow_le_rpow_of_exponent_le hNk hexp

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
