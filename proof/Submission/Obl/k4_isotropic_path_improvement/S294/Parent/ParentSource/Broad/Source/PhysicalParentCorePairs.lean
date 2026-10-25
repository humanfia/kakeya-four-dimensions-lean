-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PhysicalParentCorePairs, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PhysicalParentCorePairs.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PhysicalParentCorePairs.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentCaptureFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedBaseComparison

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open k4_stable_native_signal_oscillation

noncomputable section

/-- Whole-core bounds supplied by the original gradient source imply sharp
physical parent pairs in ANY earlier packet's unsheared coordinates.
The parent jets and core incidences are derived from the actual problem. -/
theorem ValueBranchData.physical_parent_pairs_of_core_gradients
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w) (hK : 2304 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) (hκK : 3*p.κ ≤ K)
    {coreFloor : ENNReal} (cores : V.CoreFamilies coreFloor)
    (hr : 0 ≤ p.r mid) (old : Fin p.C)
    (source : Set Event) (hsourceF : source⊆p.F old)
    (hgood : source⊆Prod.fst ⁻¹' ParentSignal.goodLines
      (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    {G : ℝ} (hG : 0 ≤ G)
    (hgrad : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      (source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)).Nonempty →
      ∀ x∈closedBall (0 : Base) 2,
        ‖fderiv ℝ (parentCorePrediction (d.N k) (d.B k) p v.1.1 (d.P k (p.γ v.1.1)) K R
          ((cores v).center ci.1.1) ((cores v).sheet ci)) x‖ ≤
          G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p v.1.1 K R)) :
    let oldWidth := δ (d.N k) (p.r (p.lev old))
    let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/oldWidth))
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
    let slope := 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
    ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      ∀ z∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
      ∀ z'∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
        |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
          physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z'| ≤
            additive+(slope*(((2:ℝ)^p.T (p.lev old))⁻¹)/oldWidth)*
              ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖ := by
  intro oldWidth additive comparison slope v ci hγ z hz z' hz'
  let U := source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)
  let P := d.P k (p.γ old)
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hKtwo : 2 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hDK : d.K k ≤ K := (le_max_right _ _).trans hmax
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have ha : 0 < oldWidth := by dsimp [oldWidth,δ]; positivity
  have hB : 0 < d.B k (p.γ v.1.1) := (hd.parent_signal_data k _).1
  have hE : U⊆d.E k (p.γ old) := by
    intro x hx
    rw [←hγ]
    exact hHE _ ((V.subset v.1.1 v.1.2).2
      (((cores v).subset ci).2 (((cores v).subset ci).1 hx.2.2))).1
  obtain ⟨hP,_,_,hjets,_⟩ := original_parent_source_inputs hd k (p.γ old) hDK U hE
  have hU (x) (hx : x∈U) :
      CoreIncidence (d.N k) (d.B k) p old v.1.1 K (K^6)⁻¹ R
        (V.center v.1.2) ((cores v).center ci.1.1) ((cores v).sheet ci) x := by
    have hraw := ((cores v).subset ci).1 hx.2.2
    have hxV := ((cores v).subset ci).2 hraw
    have hc := (cores v).points ci x hraw
    exact ⟨((V.subset v.1.1 v.1.2).2 hxV).2,hsourceF hx.1,
      V.value v.1.1 v.1.2 x hxV,hc.1,hc.2.2⟩
  have hjets' (x) (hx : x∈U) :
      |MvPolynomial.eval (xp x.1 x.2) (MvPolynomial.pderiv 3 P)| ≤ K*d.B k (p.γ v.1.1) ∧
      |MvPolynomial.eval (xp x.1 x.2) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
        K*d.B k (p.γ v.1.1)^2 := by
    simpa only [hγ] using hjets x hx (hgood hx.1)
  have hgradient := hgrad v ci hγ ⟨z,hz⟩
  have hh := parent_core_lipschitz hp hN hNp old v.1.1 hB P hP
    (by rw [v.2.1]; exact physical_parent_fine_width_le_one hN hr)
    hKtwo hκK (by positivity) le_rfl (V.center v.1.2) R
    ((cores v).center ci.1.1) (nativeCoreSign ci.2) ((cores v).extension ci) ((cores v).sheet ci)
    ((cores v).branch ci ⟨z,((cores v).subset ci).1 hz.2.2⟩) U hU
    (by positivity : 0 ≤ 24*K) hjets' hG (by simpa only [P,hγ,v.2.1,show 24*K/2=12*K by ring] using hgradient) z hz z' hz'
  rw [v.2.1] at hh
  have hcomp := hp.native_base_le_unsheared hN old z z'
  calc
    _ = oldWidth⁻¹*|MvPolynomial.eval (xp z.1 z.2) P-MvPolynomial.eval (xp z'.1 z'.2) P| := by
      change |oldWidth⁻¹*_-oldWidth⁻¹*_|=_
      rw [←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr ha)]
    _ ≤ oldWidth⁻¹*((2+G/2)*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid))+
        (24*K)/2*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
          (((2:ℝ)^p.T (p.lev old))⁻¹)*‖packetBase p old z-packetBase p old z'‖) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)
    _ ≤ oldWidth⁻¹*((2+G/2)*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid))+
        (24*K)/2*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
          (((2:ℝ)^p.T (p.lev old))⁻¹)*
            (comparison*‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖)) := by
      gcongr
    _ = _ := by dsimp [additive,slope]; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
