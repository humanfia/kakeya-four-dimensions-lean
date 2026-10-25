import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.VelocityReadouts
import Submission.Obl.k4_scalar_guarded_entropic_path.VelocityAmbiguity

/-! The actual prefix world and the one master original-velocity bin
give the constant local ambiguity used by the entropy-window theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ} {root : Code}

theorem exists_four_canonical_velocity_bins (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : TrueLiftChains.Chain root (source.problem i)) (k : ℕ) (j : Fin targets.length)
    (ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × State))
    {N H U : ℝ} (hN : 0 < N) (hH : 0 < H) (m : ℕ) (Mb : ℤ)
    (hscale : H * N ^ (-U) ≤ N ^ (-(m : ℝ)))
    (hwidth : ∀ᵐ z ∂ρ,
      (H * (2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ ≤
        (path.rootGeometry i certs k j).width (path.rootRow i certs k j z.1))
    (hdecode : ∀ᵐ z ∂ρ, Info.canonZ m Mb
      (Info.canonX N m Mb ((path.viewAt i certs hl before (j.val + 1)).suffixChain.pullback k z).2) =
      velocityBin N (m : ℝ)
        (((path.viewAt i certs hl before (j.val + 1)).suffixChain.pullback k z).2.1.2 1))
    (g : Fin (W (path.viewAt i certs hl before (j.val + 1)).parent
      ((path.viewAt i certs hl before (j.val + 1)).suffixChain.sample k))) (z₀ : ℤ) :
    ∃ S : Finset ℤ, S.card ≤ 4 ∧ ∀ᵐ z ∂ρ,
      (path.viewAt i certs hl before (j.val + 1)).suffixChain.world k z.1 = g →
      velocityBin N U (path.velocityAt i certs k 0 z) = z₀ →
      Info.canonZ m Mb
        (Info.canonX N m Mb ((path.viewAt i certs hl before (j.val + 1)).suffixChain.pullback k z).2) ∈ S := by
  let E := {z : Fin (W (path.forget.finalFamily.problem i) k) × State |
    (H * (2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ ≤
      (path.rootGeometry i certs k j).width (path.rootRow i certs k j z.1)}
  apply exists_four_velocity_bins_ae ρ E hwidth
    (fun z => (path.viewAt i certs hl before (j.val + 1)).suffixChain.world k z.1)
    (path.velocityAt i certs k 0) (path.velocityAt i certs k (j.val + 1))
    (fun z => Info.canonZ m Mb
      (Info.canonX N m Mb ((path.viewAt i certs hl before (j.val + 1)).suffixChain.pullback k z).2))
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) hH.le hscale
  · intro x hx y hy hworld
    exact path.root_velocity_lipschitz i certs k j x y
      (path.rootRow_eq_of_viewAt_world_eq i certs hl before k j x.1 y.1 hworld) hH hx
  · filter_upwards [hdecode] with z hz
    simpa only [velocityBin, path.viewAt_velocity i certs hl before k (j.val + 1)] using hz

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
