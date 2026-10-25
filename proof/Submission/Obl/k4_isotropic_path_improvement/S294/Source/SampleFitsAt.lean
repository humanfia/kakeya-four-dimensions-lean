-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFitsAt, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The fits of `sample_at` at one sample (session x1088).

From the sample-level facts (each an instance of an eventual lemma: the geometry envelope
`Kgeom ≤ N^(3δ₀L)`, the row bound `28 Kg^6 ≤ K`, the native graph-mesh floor constants and
`4 ≤ N^(gain L)`) and the pre-sample window inequalities (`Source.SampleWindow`):
* `graphMesh_lower_at`: `mesh (nmeshAt …) ≥ N^(-(graphLowerCoeff gain L))` (x1095's
  `native_design_graph_mesh_lower_of_row_bound` at the capped target, `TmAt_eq_target`);
* `listA_at`, `listB_at`, `band_at`: the premises `hlistA`, `hlistB`, `hband` of
  `Source.SampleAt.sample_at` for one `κ, K_d`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleWindow
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignMeshLower

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

theorem one_le_KgAt {κ Kd N δ₀ L τ ub d₁ : ℝ} {m : ℕ} (hκ : 0 ≤ κ) (hKd : 0 ≤ Kd) :
    1 ≤ KgAt κ Kd N δ₀ L τ ub d₁ m := by
  unfold KgAt mk4Kg
  refine le_trans ?_ (le_max_left _ _)
  nlinarith

/-- **The graph mesh of the MK4 rows**, from below. -/
theorem graphMesh_lower_at {κ Kd N δ₀ L τ ub d₁ κ₁ precision loss gain : ℝ} {Ep m : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 1 ≤ κ) (hKd : 0 ≤ Kd) (hκ₁ : 0 < κ₁) (hd₀ : 0 ≤ d₁)
    (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hrow : 28 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 6 ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1)))
    (hκa : κ ≤ N ^ (gain * L / 2)) (h512 : 512 ≤ N ^ (gain * L / 2))
    (hconst : mk4MeshFloorConstant ≤ N ^ (gain * L)) :
    N ^ (-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * (gain * L))) ≤
      Submission.Lib.K4DyadicRowScales.mesh (nmeshAt κ Kd N δ₀ L τ ub d₁
        (thetaNAt κ₁ d₁ Ep precision gain N L) m) := by
  have hNp : 0 < N := by linarith
  have hKg1 : 1 ≤ KgAt κ Kd N δ₀ L τ ub d₁ m := one_le_KgAt (by linarith) hKd
  have hgt : 0 ≤ NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff
    have := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep := Ep) hprec
    have := NativeDesign.clockCoeff_pos (Ep := Ep) hprec
    positivity
  have e : thetaNAt κ₁ d₁ Ep precision gain N L =
      N ^ (-(NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * (gain * L))) := by
    unfold thetaNAt; ring_nf
  have hθ1 : thetaNAt κ₁ d₁ Ep precision gain N L ≤ 1 := by
    rw [e]
    apply Real.rpow_le_one_of_one_le_of_nonpos hN.le
    have : 0 ≤ NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * (gain * L) := by positivity
    linarith
  have hθle : thetaNAt κ₁ d₁ Ep precision gain N L / (80 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 7) ≤ 1 := by
    have hK7 : 1 ≤ KgAt κ Kd N δ₀ L τ ub d₁ m ^ 7 := one_le_pow₀ hKg1
    have hθ0 : 0 ≤ thetaNAt κ₁ d₁ Ep precision gain N L := by
      rw [e]; exact (Real.rpow_pos_of_pos hNp _).le
    rw [div_le_one (by positivity)]
    nlinarith
  unfold nmeshAt
  rw [TmAt_eq_target hθle, e]
  have hrow' : 28 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 6 ≤ N ^ (loss * (gain * L) / ((Ep : ℝ) + 1)) := by
    rw [show loss * (gain * L) = loss * gain * L by ring]; exact hrow
  exact native_design_graph_mesh_lower_of_row_bound Ep hN.le (by linarith) hκ₁ hd₀ hd₁ hprec hloss1
    (by positivity) hKg1 hrow' hκa h512 hconst

/-- **`hlistA` of `sample_at` at one `κ, K_d`.** -/
theorem listA_at {κ Kd N δ₀ L τ ub d₁ κ₁ precision loss gain : ℝ} {Ep m nfam : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 1 ≤ κ) (hKd : 0 ≤ Kd) (hκ₁ : 0 < κ₁) (hd₀ : 0 ≤ d₁)
    (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub)
    (hKgeom : KgeomAt κ Kd N δ₀ L τ ≤ N ^ (3 * δ₀ * L))
    (hrow : 28 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 6 ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1)))
    (hκa : κ ≤ N ^ (gain * L / 2)) (h512 : 512 ≤ N ^ (gain * L / 2))
    (hconst : mk4MeshFloorConstant ≤ N ^ (gain * L)) (h4 : 4 ≤ N ^ (gain * L))
    (hwin : (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub +
        100 * (3 * δ₀ * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
          ub + 1 / (m : ℝ)) +
        NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gain) + gain) + 1 < nfam) :
    listLenOf m δ₀ L N (2 * KgeomAt κ Kd N δ₀ L τ ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf (KgeomAt κ Kd N δ₀ L τ) κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) /
      fineAt κ Kd N δ₀ L τ ub d₁ (thetaNAt κ₁ d₁ Ep precision gain N L) m) < nfam := by
  have hNp : 0 < N := by linarith
  obtain ⟨hK24, hκK, hNK⟩ := KgeomAt_facts (Kd := Kd) (δ₀ := δ₀) (L := L) hκ hN.le hτ
  have hm1 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hKc : KcenAt κ Kd N δ₀ L τ ub m ≤ N ^ ((3 * δ₀ *
      (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub +
      1 / (m : ℝ)) * L) := by
    unfold KcenAt
    exact censusK_le_rpow hK24 hκ hκK hN.le hNK (by positivity) hL.le (by positivity) hKgeom
  have hmesh := graphMesh_lower_at (Ep := Ep) (m := m) (τ := τ) (ub := ub) (δ₀ := δ₀) (κ₁ := κ₁)
    hN hL hκ hKd hκ₁ hd₀ hd₁ hprec hloss1 hgain hrow hκa h512 hconst
  have hF : (0 : ℝ) ≤ (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) :=
    Nat.cast_nonneg _
  have hgl : 0 ≤ NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision := by
    have := graphLower_ge (Ep := Ep) hκ₁ hd₀ hd₁ hprec; linarith
  exact listA_fit hN hL hκ hτ hδ hub (by positivity) hgl hgain hKgeom hmesh hKc h4 hwin

/-- **`hlistB` of `sample_at` at one `κ, K_d, εv`.** -/
theorem listB_at {κ Kd N δ₀ L τ ub εv X₀ κ₁ gain : ℝ} {m nfam c : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 1 ≤ κ) (hκ₁ : 0 < κ₁) (hX₀ : 0 ≤ X₀) (hgain : 0 < gain)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub)
    (hKgeom : KgeomAt κ Kd N δ₀ L τ ≤ N ^ (3 * δ₀ * L))
    (hεv : N ^ (-(3 * X₀ * gain * L / κ₁)) / 2 ≤ εv) (h4 : 4 ≤ N ^ (gain * L))
    (hwin : (c : ℝ) + (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub +
        3 * X₀ * gain / κ₁) + gain) + 1 < nfam) :
    c + listLenOf m δ₀ L N (2 * KgeomAt κ Kd N δ₀ L τ ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf (KgeomAt κ Kd N δ₀ L τ) κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) / εv) < nfam := by
  have hεv' : N ^ (-(3 * X₀ * gain / κ₁ * L)) / 2 ≤ εv := by
    rw [show 3 * X₀ * gain / κ₁ * L = 3 * X₀ * gain * L / κ₁ by ring]; exact hεv
  exact listB_fit hN hL hκ hτ hδ hub (by positivity) hgain hKgeom hεv' h4 hwin

/-- **`hband` of `sample_at` at one `κ, K_d`.** -/
theorem band_at {κ Kd N δ₀ L τ ub d₁ κ₁ precision loss gain : ℝ} {Ep m : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 1 ≤ κ) (hKd : 0 ≤ Kd) (hκ₁ : 0 < κ₁) (hd₀ : 0 ≤ d₁)
    (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hrow : 28 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 6 ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1)))
    (hκa : κ ≤ N ^ (gain * L / 2)) (h512 : 512 ≤ N ^ (gain * L / 2))
    (hconst : mk4MeshFloorConstant ≤ N ^ (gain * L))
    (hrate : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gain ≤ 1 / 4) :
    N ^ (-(L / 4)) ≤ 4 * Submission.Lib.K4DyadicRowScales.coarse (nmeshAt κ Kd N δ₀ L τ ub d₁
      (thetaNAt κ₁ d₁ Ep precision gain N L) m) := by
  have hmesh := graphMesh_lower_at (Ep := Ep) (m := m) (τ := τ) (ub := ub) (δ₀ := δ₀) (κ₁ := κ₁)
    hN hL hκ hKd hκ₁ hd₀ hd₁ hprec hloss1 hgain hrow hκa h512 hconst
  have hle : N ^ (-(L / 4)) ≤ N ^ (-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * (gain * L))) := by
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    have := mul_le_mul_of_nonneg_right hrate hL.le
    have e : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * (gain * L) =
        NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gain * L := by ring
    rw [e]; linarith
  have hmc := Submission.Lib.K4DyadicRowScales.mesh_le_coarse (nmeshAt κ Kd N δ₀ L τ ub d₁
      (thetaNAt κ₁ d₁ Ep precision gain N L) m)
  have hc0 := Submission.Lib.K4DyadicRowScales.coarse_pos (nmeshAt κ Kd N δ₀ L τ ub d₁
      (thetaNAt κ₁ d₁ Ep precision gain N L) m)
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
