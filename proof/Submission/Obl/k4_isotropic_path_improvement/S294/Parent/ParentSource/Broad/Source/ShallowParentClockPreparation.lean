-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ShallowParentClockPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ShallowParentClockPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ShallowParentClockPreparation.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockAtSteps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentClockRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentPrior
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ShallowParentStateBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic Metric
open k4_stable_native_signal_oscillation
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Obl.k4_scalar_grid_cartesian_field
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ εPure : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Stage original clock floors, original durations and renewed physical
state breadth on a SHALLOW ancestor. Whole-core gradients come from the
actual all-depth source and survive the clock cuts. Every deletion uses
the same full original old reference; no quarter-level old is required. -/
theorem ValueBranchData.prepare_shallow_parent_clock_velocity_source
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hio : i ≤ stop) (old : Fin p.C) (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) {G : ℝ} (hG : 0 ≤ G) (hfraction : 0 ≤ fraction)
    {fineMesh radius Kcensus dimension cellRate durationRate coarse : ℝ}
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep=stop → p.unshearedDeepRadius old deep ≤ fineMesh)
    (hheightSmall : ∀ deep : Fin p.C, p.lev deep=stop →
      let aOld := δ (d.N k) (p.r (p.lev old))
      let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
      let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
        (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
      (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld))+
        Lip*(6*p.unshearedDeepRadius old deep) ≤ fineMesh)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (hradius : 0 ≤ radius) (hradiusScale : radius*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (stateRef : ENNReal) (hstate0 : stateRef≠0) (hstateTop : stateRef≠∞)
    (hKcensus : 1 ≤ Kcensus)
    (hθK : δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ Kcensus)
    (steps : ℕ) (hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : fineMesh*(2:ℝ)^steps ≤
      δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))
    (hcellRate : 0 ≤ cellRate) (hdurationRate : 0 ≤ durationRate)
    (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source⊆V.coreRetained cores (p.γ old)∩(broad.residual (p.γ old)∩p.F old))
    (hgrad : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      (source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)).Nonempty →
      ∀ x∈closedBall (0 : Base) 2,
        ‖fderiv ℝ (parentCorePrediction (d.N k) (d.B k) p v.1.1 (d.P k (p.γ v.1.1)) K R
          ((cores v).center ci.1.1) ((cores v).sheet ci)) x‖ ≤
          G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p v.1.1 K R))
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus^(100:ℕ)*b ≤
        (δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*w →
      (occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).ncard:ℝ) ≤
          Kcensus/(b^3*w^dimension)) :
    let raw := (d.ν k (p.γ old)).prod volume
    let reference := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)
    let heightRatio := δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
    let mesh := fineMesh*(2:ℝ)^steps
    let code := clockParentCode p old (d.P k (p.γ old)) mesh
    ∃ earlier current : Set Event, MeasurableSet earlier ∧ MeasurableSet current ∧
      current⊆earlier ∧ earlier⊆source ∧
      current⊆Prod.fst ⁻¹' ParentSignal.clockJetGood
        (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      raw source ≤ raw current+
        (ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*cellRate)+
          ENNReal.ofReal (durationRate*(3*K^4+3)*(7:ℝ)^4)+
          stateRef*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (p.κ^2))*reference ∧
      (activeCodes (raw.restrict earlier) code).Finite ∧
      (∀ q, (raw.restrict earlier) (code ⁻¹' {q})=0 ∨
        ENNReal.ofReal (cellRate*heightRatio^(-dimension)*mesh^((3:ℝ)+dimension))*reference ≤
          (raw.restrict earlier) (code ⁻¹' {q})) ∧
      (∀ z∈(hp.frozenPacket old).assignedSelectedEvent current,
        ENNReal.ofReal (durationRate*coarse) ≤ incidenceDuration
          (hp.assignedClockCellSource old (d.P k (p.γ old)) earlier coarse
            (hp.assignedClockCode old (d.P k (p.γ old)) coarse z)) z.1) ∧
      ∀ label (n center : P2), ‖n‖=1 →
        (raw.restrict current) {z | code z=label ∧
          |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity old z-center)| ≤ radius} ≤
          (stateRef⁻¹*ENNReal.ofReal (8*fraction))*(raw.restrict current) (code ⁻¹' {label}) := by
  classical
  let raw : Measure Event := (d.ν k (p.γ old)).prod volume
  let reference := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)
  let sourceGood := source∩Prod.fst ⁻¹' ParentSignal.clockJetGood
    (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))
  have hgoodMeas : MeasurableSet sourceGood := hsource.inter
    ((ParentSignal.measurableSet_clockJetGood _ _ _).preimage measurable_fst)
  have hgoodLaw : raw.restrict sourceGood=raw.restrict source :=
    ParentSignal.original_restrict_clockJetGood hd k (p.γ old) source
  have hgoodMass : raw sourceGood=raw source := by
    simpa only [Measure.restrict_apply_univ] using congrArg (fun μ : Measure Event => μ univ) hgoodLaw
  have hcensusGood (b w : ℝ) (hb : fineMesh ≤ b) (hb1 : b ≤ 1)
      (hw : fineMesh ≤ w) (hw1 : w ≤ 1)
      (hshape : Kcensus^(100:ℕ)*b ≤
        (δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*w) :
      (occupied sourceGood (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).Finite ∧
      ((occupied sourceGood (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).ncard:ℝ) ≤
          Kcensus/(b^3*w^dimension) := by
    obtain ⟨hfin,hnum⟩ := hcensus b w hb hb1 hw hw1 hshape
    have hs : occupied sourceGood (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w ⊆
        occupied source (fun z j => unshearedPacketBase p old z j)
          (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w := by
      rintro q ⟨z,hz,heq⟩
      exact ⟨z,hz.1,heq⟩
    have hcard : ((occupied sourceGood (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).ncard:ℝ) ≤
        ((occupied source (fun z j => unshearedPacketBase p old z j)
          (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) b w).ncard:ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hs hfin
    exact ⟨hfin.subset hs,hcard.trans hnum⟩
  obtain ⟨earlier,hearlier,hearlierSub,hlossFloor,hfinite,hfloor,hwhole⟩ :=
    original_parent_clock_grid_source_at_steps (d.N k) p old (d.P k (p.γ old))
      (d.ν k (p.γ old)) sourceGood hgoodMeas hFine hFine1 hKcensus hθK hcensusGood
      steps hsteps hresolved hcellRate
  have hN : 0 < d.N k := by linarith [hd.1 k]
  letI : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have href0 : reference≠0 := mul_ne_zero (hp.assignment_mass_pos hN old).ne' (by positivity)
  have hrefTop : reference≠∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hearlierSource : earlier⊆source := hearlierSub.trans inter_subset_left
  have hearlierF : earlier⊆p.F old := fun z hz => (hsub (hearlierSource hz)).2.2
  have hgoodEarlier (z) (hz : z∈earlier) : z.1∈ParentSignal.clockJetGood
      (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := (hearlierSub hz).2
  obtain ⟨middle,hmiddle,hmiddleSub,hlossDuration,hlong,hprior⟩ :=
    hp.prune_original_clock_durations hd old (by linarith : 24 ≤ K) hmax earlier hearlier hearlierF
      (fun z hz => (hgoodEarlier z hz).1) (fun z hz => (hgoodEarlier z hz).2)
      hcoarse hcoarse1 hdurationRate
  have hlossDuration' : raw (earlier\middle) ≤
      ENNReal.ofReal (durationRate*(3*K^4+3)*(7:ℝ)^4)*reference := by
    rw [mul_comm (ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))
      (d.ν k (p.γ old) (p.A old))] at hlossDuration
    calc
      _ = reference*(reference⁻¹*raw (earlier\middle)) := by
        rw [←mul_assoc,ENNReal.mul_inv_cancel href0 hrefTop,one_mul]
      _ ≤ reference*ENNReal.ofReal (durationRate*(3*K^4+3)*(7:ℝ)^4) := mul_le_mul' le_rfl hlossDuration
      _ = _ := mul_comm _ _
  have hmiddleSupport : middle⊆V.coreRetained cores (p.γ old)∩
      (broad.residual (p.γ old)∩p.F old) := fun z hz => hsub (hearlierSource (hmiddleSub hz))
  obtain ⟨current,hcurrent,hcurrentSub,hparentBudget,hparentCaps⟩ :=
    V.exists_shallow_parent_state_breadth_of_core_gradients Q hd hp hHE hHbase hHterminal hK hmax hκK
      cores broad hio old hmid hstop hr hG hFine hFine hbaseSmall hheightSmall hcoreSmall
      hfraction hradius hradiusScale stateRef hstate0 hstateTop middle hmiddle hmiddleSupport
      (fun z hz => (hgoodEarlier z (hmiddleSub hz)).1)
      (fun v ci hγ hne => hgrad v ci hγ
        (hne.mono (fun z hz => ⟨hearlierSource (hmiddleSub hz.1),hz.2⟩)))
  have hmassFloor : raw source ≤ raw earlier+
      ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*cellRate)*reference := by
    rw [←hgoodMass]
    apply (measure_mono (show sourceGood⊆earlier∪(sourceGood\earlier) from fun z hz => by
      by_cases h : z∈earlier
      · exact Or.inl h
      · exact Or.inr ⟨hz,h⟩)).trans
    apply (measure_union_le _ _).trans
    apply add_le_add le_rfl
    simpa only [mul_comm (ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))
      (d.ν k (p.γ old) (p.A old))] using hlossFloor
  have hmassDuration : raw earlier ≤ raw middle+
      ENNReal.ofReal (durationRate*(3*K^4+3)*(7:ℝ)^4)*reference := by
    apply (measure_mono (show earlier⊆middle∪(earlier\middle) from fun z hz => by
      by_cases h : z∈middle
      · exact Or.inl h
      · exact Or.inr ⟨hz,h⟩)).trans
    exact (measure_union_le _ _).trans (add_le_add le_rfl hlossDuration')
  have hKpow : Kcensus ≤ Kcensus^(100:ℕ) := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hKcensus (by norm_num : (1:ℕ) ≤ 100)
  have hθD : δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ (2:ℝ)^steps :=
    hθK.trans (hKpow.trans hsteps)
  refine ⟨earlier,current,hearlier,hcurrent,hcurrentSub.trans hmiddleSub,hearlierSource,
    (fun z hz => hgoodEarlier z (hmiddleSub (hcurrentSub hz))),?_,hfinite,?_,?_,?_⟩
  · apply hmassFloor.trans
    apply (add_le_add hmassDuration le_rfl).trans
    apply (add_le_add (add_le_add hparentBudget le_rfl) le_rfl).trans
    apply le_of_eq
    ring
  · intro q
    simpa only [mul_comm (ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))
      (d.ν k (p.γ old) (p.A old))] using hfloor q
  · intro z hz
    apply hlong z
    rw [(hp.frozenPacket old).assignedSelectedEvent_originalIncidence] at hz ⊢
    exact hcurrentSub hz
  · intro label n center hn
    let band := {z : Event | |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity old z-center)| ≤ radius}
    have hband : MeasurableSet band := measurableSet_le
      ((measurable_const.inner (((p.measurable_normalizedVelocity old).const_smul ((6*p.κ)⁻¹)).sub_const center)).abs)
      measurable_const
    have hh := parent_clock_band_ratio_of_joint_state (d.N k) p old (d.P k (p.γ old))
      (raw.restrict current) hFine steps hθD band hband (stateRef⁻¹*ENNReal.ofReal (8*fraction))
      (fun q => hparentCaps q n center hn) label
    exact hh

end Prepared
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
