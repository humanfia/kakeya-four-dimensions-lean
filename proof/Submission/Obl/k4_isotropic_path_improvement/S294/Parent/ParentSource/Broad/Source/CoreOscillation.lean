-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreOscillation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreOscillation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreOscillation.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreSourceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceCoreValueVariation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Earlier raw core mass and the original pure cap control the old signal on
any later subset with a controlled core-coordinate diameter. -/
theorem CoreEntryData.actual_core_signal_oscillation
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count)
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a)
      (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (i : ↥C.codes × Bool) (hi : (C.kept i).Nonempty)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (old : Fin p.C) (hγ : p.γ b = p.γ old)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev old)))
    (hFineOld : p.F b ⊆ p.F old)
    (diameter : ℝ) (U : Set Event) (hUcore : U ⊆ C.raw i)
    (hdiam : ∀ z ∈ U, ∀ z' ∈ U,
      ‖packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center i.1.1) z -
        packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center i.1.1) z'‖ ≤ diameter) :
    ∀ z ∈ U, ∀ z' ∈ U,
      |MvPolynomial.eval (xp z.1 z.2) (p.R old) / δ (d.N k) (p.r (p.lev old)) -
        MvPolynomial.eval (xp z'.1 z'.2) (p.R old) / δ (d.N k) (p.r (p.lev old))| ≤
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) * diameter := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hKtwo : 2 ≤ K := by linarith
  have hKone : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hAnorm : 2 ≤ K ^ (qcore + 7) := by
    apply hKtwo.trans
    simpa only [pow_one] using pow_le_pow_right₀ hKone (show 1 ≤ qcore + 7 by omega)
  let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center i.1.1)
  let μ := (V.entryLaw b a).restrict (C.raw i)
  have hZ : Measurable Z :=
    (((measurable_nativeBase.comp (measurable_packetNativeCubePoint (d.N k) (d.B k) p b)).sub_const
      (C.center i.1.1)).const_smul (K ^ R))
  have hratio : K ^ 7 / K ^ (qcore + 7) = (K ^ qcore)⁻¹ := by
    rw [pow_add]
    field_simp [pow_ne_zero _ hKpos.ne']
  have hmass : ENNReal.ofReal (K ^ 7 / K ^ (qcore + 7)) ≤ μ univ := by
    rw [hratio]
    simpa only [μ, Measure.restrict_apply_univ] using C.original_floor i hi
  have hmap : μ.map Z ≤ ENNReal.ofReal (K ^ 7) • volume :=
    V.entryLaw_core_cap Q hpure hd hp hHE hHbase hK hmax hpower b hb hr hrL a
      (C.raw i) (C.center i.1.1)
  have hcap (E : Set Base) (hE : MeasurableSet E) :
      μ (Z ⁻¹' E) ≤ ENNReal.ofReal (K ^ 7) * volume E := by
    rw [← Measure.map_apply hZ hE]
    simpa only [Measure.smul_apply, smul_eq_mul] using (Measure.le_iff.mp hmap E hE)
  have hpoint (z : Event) (hz : z ∈ C.raw i) :
      z ∈ p.F b ∧ z ∈ p.F old ∧ |packetSignal (d.N k) p b z - V.center a| ≤ (K ^ 6)⁻¹ ∧
        Z z ∈ closedBall (0 : Base) 1 ∧
        rootLift (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
          (packetNativeCubePoint (d.N k) (d.B k) p b z) 3 = C.sheet i (Z z) := by
    have hzV := (C.subset i).2 hz
    have hzF := ((V.subset b a).2 hzV).2
    have hc := C.points i z hz
    refine ⟨hzF, hFineOld hzF, V.value b a z hzV, ?_, hc.2.2⟩
    rw [mem_closedBall, dist_zero_right]
    exact hc.1.trans (by norm_num)
  have hsource : ∀ᵐ z ∂μ,
      z ∈ p.F b ∧ z ∈ p.F old ∧ |packetSignal (d.N k) p b z - V.center a| ≤ (K ^ 6)⁻¹ ∧
        Z z ∈ closedBall (0 : Base) 1 ∧
        rootLift (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
          (packetNativeCubePoint (d.N k) (d.B k) p b z) 3 = C.sheet i (Z z) :=
    (ae_restrict_mem (C.measurable i).1).mono hpoint
  have hbranch := C.branch i (hi.mono (C.subset i).1)
  exact path_old_signal_deep_entry_oscillation hp hD hjets hNpos old b hB hγ hwidth
    hKtwo hκK (show 0 < (K ^ 6)⁻¹ by positivity) le_rfl (V.center a)
    R (C.center i.1.1) (nativeCoreSign i.2) (C.extension i) (C.sheet i) hbranch μ
    hAnorm (show 0 < K ^ 7 by positivity) hmass hcap hsource U
    (fun z hz => hpoint z (hUcore hz)) hdiam

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
