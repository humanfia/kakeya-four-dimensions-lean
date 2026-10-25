-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.CapturedParentPairs, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/CapturedParentPairs.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorFrames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentLipschitz
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalParentInputs
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueBranchData

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Metric ParentSource ParentSource.Native ParentSource.Analytic
open k4_stable_native_signal_oscillation

noncomputable section

/-- A genuine whole-core parent gradient controls physical-parent pairs
in every literal unsheared packet frame. Clock and core-radius factors
cancel; the tested core need not descend from an active broad parent. -/
theorem ParentSource.CoreEntryData.parent_pairs_of_gradient
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Ev} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (hK : 2 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid) (hr : 0 ≤ p.r mid)
    (a : Fin V.count) {coreFloor : ENNReal}
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) coreFloor)
    (ii : ↥C.codes × Bool) {G : ℝ} (hG : 0 ≤ G)
    (hgrad : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ (parentCorePrediction (d.N k) (d.B k) p b (d.P k (p.γ b)) K R
        (C.center ii.1.1) (C.sheet ii)) x‖ ≤
        G * (K ^ 14 * (K ^ 6)⁻¹ * ParentSource.δ (d.N k) (p.r mid) +
          12 * K * coreRowStep p b K R)) (target : Fin p.C) :
    let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
    let Cf := 1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)
    let comparison := 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) *
      (1 + (d.K k + 2 * p.κ ^ 2))
    ∀ z ∈ C.raw ii ∩ Prod.fst ⁻¹' good, ∀ z' ∈ C.raw ii ∩ Prod.fst ⁻¹' good,
      |MvPolynomial.eval (ParentSource.xp z.1 z.2) (d.P k (p.γ b)) -
        MvPolynomial.eval (ParentSource.xp z'.1 z'.2) (d.P k (p.γ b))| ≤
        (2 + G / 2) * (K ^ 14 * (K ^ 6)⁻¹ * ParentSource.δ (d.N k) (p.r mid)) +
          (12 * K * G * Cf * comparison) * (((2 : ℝ) ^ p.T (p.lev target))⁻¹) *
            ‖unshearedPacketBase p target z - unshearedPacketBase p target z'‖ := by
  dsimp only
  let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
  let U := C.raw ii ∩ Prod.fst ⁻¹' good
  have hUsub : U ⊆ d.E k (p.γ b) := fun z hz =>
    hHE _ ((V.subset b a).2 ((C.subset ii).2 hz.1)).1
  obtain ⟨hP, _, _, hjets, _⟩ := original_parent_source_inputs hd k (p.γ b)
    ((le_max_right _ _).trans hmax) U hUsub
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hB : 0 < d.B k (p.γ b) := (hd.parent_signal_data k _).1
  have hwidth : ParentSource.δ (d.N k) (p.r (p.lev b)) ≤ 1 := by
    rw [hb]
    exact physical_parent_fine_width_le_one hN hr
  have hU (z : Ev) (hz : z ∈ U) :
      CoreIncidence (d.N k) (d.B k) p b b K (K ^ 6)⁻¹ R
        (V.center a) (C.center ii.1.1) (C.sheet ii) z := by
    have hzV := (C.subset ii).2 hz.1
    have hzF := ((V.subset b a).2 hzV).2
    have hc := C.points ii z hz.1
    exact ⟨hzF, hzF, V.value b a z hzV, hc.1, hc.2.2⟩
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  intro z hz z' hz'
  have hii : (C.raw ii).Nonempty := ⟨z, hz.1⟩
  have hpairs := parent_core_lipschitz hp hN hNp b b hB (d.P k (p.γ b)) hP hwidth
    hK hκK (by positivity) le_rfl (V.center a) R (C.center ii.1.1) (nativeCoreSign ii.2)
    (C.extension ii) (C.sheet ii) (C.branch ii hii) U hU
    (M := 24 * K) (by positivity) (fun z hz => hjets z hz hz.2) hG (by
      simpa only [hb, show (24 * K) / 2 = 12 * K by ring] using hgrad) z hz z' hz'
  have hcomp : 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u b‖) ≤
      1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2)) := by
    have hu := original_packet_center_velocity hd hp b
    have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
    gcongr
  have hh := AncestorFrames.pair_estimate_in_frame hp hN b target
    (fun z => MvPolynomial.eval (ParentSource.xp z.1 z.2) (d.P k (p.γ b))) z z'
    (by positivity : 0 ≤ 12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)))
    hcomp (by simpa only [hb, show (24 * K) / 2 = 12 * K by ring] using hpairs)
  simpa only [mul_assoc] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
