-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MK4MeshBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeAuxiliaryScaleBounds

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- The actual MK4 coarse mesh resolves the original height band at
any sample in the first half of the prepared grid. Its only mesh
input is the already uniform native graph lower power. -/
theorem sample_mk4_band_resolved
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ delta sigma : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s delta Mp Dp sigma)
    {d₁ precision loss e0 : ℝ} {Ep i nmesh : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hdepth : tune.depth κ₁ d₁ Ep precision loss=NativeDesign.depth κ₁ d₁ Ep precision loss)
    (hN : 1 ≤ d.N k) (he0 : 0 < e0) (hL : 0 < d.L) (hi : i < m) (hhalf : s i ≤ 1/2)
    (hdelta : delta ≤ gainOf tune κ₁ d₁ Ep precision loss e0/100)
    (hgraph : d.N k^(-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*
      (gainOf tune κ₁ d₁ Ep precision loss e0*d.L))) ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh) :
    d.N k^(-(d.L-p.r i)) ≤ 4*Submission.Lib.K4DyadicRowScales.coarse nmesh := by
  let gain := gainOf tune κ₁ d₁ Ep precision loss e0
  have hgain := gainOf_pos (tune:=tune) (Ep:=Ep) hv.2.2.1 hv.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2.1 he0
  have hdepthRoom := native_sample_auxiliary_depth_room tune hp hv hdepth he0 hL hi hhalf hdelta
  have hAux := (native_auxiliary_exponent_bounds (Ep:=Ep) hv).1
  have hcoefficient := NativeDesign.coefficientCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hv.2.2.2.2.2.1
  have hGraphAux : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤
      NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) := by
    linarith only [hAux,hcoefficient]
  have hGraphAuxL := mul_le_mul_of_nonneg_right hGraphAux (mul_nonneg hgain.le hL.le)
  have hroom : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*(gain*d.L) ≤ d.L-p.r i := by
    dsimp only at hdepthRoom
    dsimp only [gain]
    nlinarith only [hGraphAuxL,hdepthRoom]
  have hresolved := (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hroom)).trans hgraph
  have hcoarse := hresolved.trans (Submission.Lib.K4DyadicRowScales.mesh_le_coarse nmesh)
  have hpositive := Submission.Lib.K4DyadicRowScales.coarse_pos nmesh
  linarith only [hcoarse,hpositive]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
