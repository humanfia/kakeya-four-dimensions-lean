import Submission.Obl.k4_conditional_common_affine_field.AxisGeometry
import Submission.Obl.k4_conditional_common_affine_field.GridCeiling
import Submission.Lib.K4HorizontalCoercivity.HorizontalInterpolation

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarCoreTools.Finalization

/-- The two axis-intercept coordinates inherit an area ceiling from the actual
fine position cells, with a polynomial separation loss. -/
theorem axis_grid_cell_ceiling {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (W : Set (α × ℝ)) (b v : α → ℝ)
    (v₀ w₁ w₂ δ ω H K : ℝ) (hδ : 0 < δ) (hδω : δ ≤ ω)
    (hH : 1 ≤ H) (hK : 0 ≤ K) (haxis : |w₁-v₀| ≤ H)
    (hsep : 1/H ≤ |w₂-w₁|)
    (hcap : ∀ q : Fin 2 → ℤ,
      μ {p | (fun j => ⌊base b v v₀ p j/δ⌋)=q} ≤ ENNReal.ofReal (K*δ^2)) :
    ∀ i j : ℤ, μ (W ∩ {p | ⌊axisIntercept b v w₁ p/ω⌋=j ∧
      ⌊axisIntercept b v w₂ p/ω⌋=i}) ≤
        ENNReal.ofReal ((12*H^2+11)^2*K*ω^2) := by
  classical
  have hHpos : 0 < H := by linarith
  have hω : 0 < ω := hδ.trans_le hδω
  have hden : w₂-w₁ ≠ 0 := by
    have h := (one_div_pos.mpr hHpos).trans_le hsep
    exact abs_pos.mp h
  let obs : α × ℝ → ℤ × ℤ := fun p =>
    (⌊axisIntercept b v w₁ p/ω⌋,⌊axisIntercept b v w₂ p/ω⌋)
  let time : ℤ × ℤ → ℝ := fun c => (ω*(c.1 : ℝ)-ω*(c.2 : ℝ))/(w₂-w₁)
  let center : ℤ × ℤ → Fin 2 → ℝ := fun c =>
    ![time c, ω*(c.1 : ℝ)+time c*(w₁-v₀)]
  have hnear (p : α × ℝ) (_hp : p ∈ W) (k : Fin 2) :
      |base b v v₀ p k-center (obs p) k| ≤ (3*H^2)*ω := by
    have hfirst := floor_scaled_error hω (axisIntercept b v w₁ p)
    have hsecond := floor_scaled_error hω (axisIntercept b v w₂ p)
    change |axisIntercept b v w₁ p-ω*((obs p).1 : ℝ)| ≤ ω at hfirst
    change |axisIntercept b v w₂ p-ω*((obs p).2 : ℝ)| ≤ ω at hsecond
    have hid : (w₂-w₁)*(p.2-time (obs p)) =
        (axisIntercept b v w₁ p-ω*((obs p).1 : ℝ))-
          (axisIntercept b v w₂ p-ω*((obs p).2 : ℝ)) := by
      dsimp only [time]
      field_simp
      dsimp only [axisIntercept]
      ring
    have ht : |p.2-time (obs p)| ≤ 2*H*ω :=
      Submission.Lib.K4HorizontalCoercivity.separated_product_bound
        H ω w₂ w₁ _ _ _ hH (by simpa only [one_div] using hsep) hfirst hsecond hid
    have hHsq : 1 ≤ H^2 := one_le_pow₀ hH
    have hHH : H ≤ H^2 := by nlinarith
    fin_cases k
    · exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hHH hω.le])
    · have heq : base b v v₀ p 1-center (obs p) 1 =
          (axisIntercept b v w₁ p-ω*((obs p).1 : ℝ))+
            (p.2-time (obs p))*(w₁-v₀) := by
        change b p.1+p.2*(v p.1-v₀)-(ω*((obs p).1 : ℝ)+time (obs p)*(w₁-v₀)) =
          (b p.1+p.2*(v p.1-w₁)-ω*((obs p).1 : ℝ))+(p.2-time (obs p))*(w₁-v₀)
        ring
      change |base b v v₀ p 1-center (obs p) 1| ≤ (3*H^2)*ω
      rw [heq]
      have hmul : |(p.2-time (obs p))*(w₁-v₀)| ≤ (2*H*ω)*H := by
        rw [abs_mul]
        exact mul_le_mul ht haxis (abs_nonneg _) (by positivity)
      have h := (abs_add_le _ _).trans (add_le_add hfirst hmul)
      nlinarith [mul_le_mul_of_nonneg_right hHsq hω.le]
  have hbound := grid_cell_ceiling μ W obs (base b v v₀) center δ ω (3*H^2) K
    hδ hδω (by positivity) hK hcap hnear
  intro i j
  convert hbound (j,i) using 1
  · congr 1
    ext p
    simp only [obs,mem_inter_iff,mem_setOf_eq,Prod.mk.injEq]
  · congr 1
    ring

end Submission.Obl.k4_conditional_common_affine_field
