-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeDesignMeshLower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4TargetLower

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The actual original MK4 retention epsilon has a uniform lower
power before the path coefficient is supplied. -/
theorem mk4_original_epsilon_lower_power {N κ a : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) (hκN : κ ≤ N^(a/2)) (hconstant : 512 ≤ N^(a/2)) :
    N^(-a) ≤ κ⁻¹/512 := by
  have hprod : κ*512 ≤ N^a := by
    calc
      _ ≤ N^(a/2)*N^(a/2) := mul_le_mul hκN hconstant (by norm_num) (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [←Real.rpow_add hN]; congr 1; ring
  calc
    _ = (N^a)⁻¹ := Real.rpow_neg hN.le a
    _ ≤ (κ*512)⁻¹ := inv_anti₀ (by positivity) hprod
    _ = _ := by rw [mul_inv_rev,div_eq_mul_inv]; ring

/-- The literal internal MK4 target has the graph lower power chosen
by NativeDesign, including curvature and integer-rounding constants. -/
theorem native_design_graph_mesh_lower
    {N κ κ₁ d precision a Kg : ℝ} (Ep : ℕ)
    (hN : 1 ≤ N) (hκ : 0 < κ) (hκ₁ : 0 < κ₁) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hprecision : 1 ≤ precision) (ha : 0 < a) (hKg : 1 ≤ Kg) (hKgN : Kg ≤ N^a)
    (hκN : κ ≤ N^(a/2)) (h512 : 512 ≤ N^(a/2))
    (hconstant : mk4MeshFloorConstant ≤ N^a) :
    N^(-(NativeDesign.graphLowerCoeff κ₁ d Ep precision*a)) ≤
      Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf
        (mk4MeshTarget (N^(-(NativeDesign.graphTargetCoeff κ₁ d Ep precision*a))) Kg (κ⁻¹/512)) d) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let T := NativeDesign.graphTargetCoeff κ₁ d Ep precision
  have hclock := NativeDesign.clockCoeff_pos (Ep:=Ep) hprecision
  have hend := NativeDesign.floorEndCoeff_pos κ₁ d (Ep:=Ep) hprecision
  have hT : 0 < T := by dsimp only [T,NativeDesign.graphTargetCoeff]; positivity
  have hdpos : 0 < 1-d := by linarith only [hd1]
  have hcoef : 24*(T+21)/(1-d)+1 ≤ 1000*(T+1)/(1-d) := by
    rw [le_div_iff₀ hdpos]
    have heq : (24*(T+21)/(1-d)+1)*(1-d)=24*(T+21)+(1-d) := by field_simp
    rw [heq]
    linarith only [hT,hd0]
  have hexponent : 24*(T*a+4*a+16*a+a)/(1-d)+a ≤ NativeDesign.graphLowerCoeff κ₁ d Ep precision*a := by
    have hh := mul_le_mul_of_nonneg_right hcoef ha.le
    change _ ≤ (1000*(T+1)/(1-d))*a
    calc
      _ = (24*(T+21)/(1-d)+1)*a := by ring
      _ ≤ _ := hh
  have hfloor := mk4_parameters_mesh_lower_power hN hKg hKgN
    (le_refl (N^(-(T*a)))) (mk4_original_epsilon_lower_power hNp hκ hκN h512)
    ha.le (mul_pos hT ha).le ha.le hd1 hconstant
  exact (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hexponent)).trans hfloor

/-- A displayed MK4 row bound already supplies the envelope bound
needed by the concrete native graph-mesh floor. -/
theorem native_design_graph_mesh_lower_of_row_bound
    {N κ κ₁ d precision loss a Kg : ℝ} (Ep : ℕ)
    (hN : 1 ≤ N) (hκ : 0 < κ) (hκ₁ : 0 < κ₁) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hprecision : 1 ≤ precision) (hloss : loss ≤ 1) (ha : 0 < a) (hKg : 1 ≤ Kg)
    (hrow : 28*Kg^6 ≤ N^(loss*a/((Ep:ℝ)+1)))
    (hκN : κ ≤ N^(a/2)) (h512 : 512 ≤ N^(a/2))
    (hconstant : mk4MeshFloorConstant ≤ N^a) :
    N^(-(NativeDesign.graphLowerCoeff κ₁ d Ep precision*a)) ≤
      Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf
        (mk4MeshTarget (N^(-(NativeDesign.graphTargetCoeff κ₁ d Ep precision*a))) Kg (κ⁻¹/512)) d) := by
  have hKg6 : Kg ≤ Kg^6 := le_self_pow₀ hKg (by norm_num)
  have hKgrow : Kg ≤ 28*Kg^6 := by linarith only [hKg6,hKg]
  have hE : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) Ep]
  have hdisplay : loss*a/((Ep:ℝ)+1) ≤ a := by
    rw [div_le_iff₀ (zero_lt_one.trans_le hE)]
    nlinarith only [mul_le_mul_of_nonneg_right hloss ha.le,
      mul_le_mul_of_nonneg_left hE ha.le]
  have hKgN : Kg ≤ N^a := (hKgrow.trans hrow).trans
    (Real.rpow_le_rpow_of_exponent_le hN hdisplay)
  exact native_design_graph_mesh_lower Ep hN hκ hκ₁ hd0 hd1 hprecision ha hKg hKgN hκN h512 hconstant

/-- Choose the concrete graph-mesh tail before all actual MK4 path
coefficients and row envelopes. -/
theorem eventually_native_design_graph_mesh_lower
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {κ₁ d precision a : ℝ} (Ep : ℕ)
    (hκ₁ : 0 < κ₁) (hd0 : 0 ≤ d) (hd1 : d < 1) (hprecision : 1 ≤ precision) (ha : 0 < a) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ Kg : ℝ, 1 ≤ κ → κ ≤ N k^sigma → 1 ≤ Kg → Kg ≤ N k^a →
        N k^(-(NativeDesign.graphLowerCoeff κ₁ d Ep precision*a)) ≤
          Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf
            (mk4MeshTarget (N k^(-(NativeDesign.graphTargetCoeff κ₁ d Ep precision*a))) Kg (κ⁻¹/512)) d) := by
  let sigma := min 1 (a/4)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hlarge512 := ((tendsto_rpow_atTop (by positivity : 0 < a/2)).comp hN).eventually_ge_atTop 512
  have hlarge := ((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop mk4MeshFloorConstant
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge512,hlarge] with k hk h512 hc
  intro κ Kg hκ hκN hKg hKgN
  have hκN' : κ ≤ N k^(a/2) := hκN.trans
    (Real.rpow_le_rpow_of_exponent_le hk (by
      have hh := min_le_right 1 (a/4)
      dsimp only [sigma]
      linarith only [hh,ha]))
  exact native_design_graph_mesh_lower Ep hk (zero_lt_one.trans_le hκ) hκ₁ hd0 hd1 hprecision ha
    hKg hKgN hκN' h512 hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
