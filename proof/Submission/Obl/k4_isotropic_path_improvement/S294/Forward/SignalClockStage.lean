-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.SignalClockStage, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Generalizes, from the physical parent `d.P` to an arbitrary signal polynomial `X`, the
-- duration pruning (Parent/ParentSource/Broad/Source/ClockCurveDuration.lean, x0943 of o265) and the
-- shallow clock stage preparation (ShallowParentClockPreparation.lean, x1046 of o265) of this
-- obligation's port of o287; adapted by x1082 for the relative row packet.
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.SignalStageRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockCurveDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockAtSteps

/-!
# A clock stage for an arbitrary signal

`prune_signal_clock_durations`: the duration pruning of `prune_original_clock_durations` for the
clock curve of any signal `X`, from a bound `Kc` on the NON-constant clock coefficients of `X`
along the lines of the source (the constant `2^T X` is unrestricted).

`exists_signal_clock_stage`: a `SignalClockStage` of an old packet for `X` from
* a census of `X / a_old` (with the unsheared old base) at all meshes from `fineMesh` on
  (earlier floors at the stage mesh, `original_parent_clock_grid_source_at_steps`);
* the coefficient bound `Kc` (coarse clock durations);
* a breadth renewal: every measurable part of the source contains a part carrying the
  per-code normalized-velocity strip ratio `ratio`, at a stated cost.
The cost is measured against the full old reference `ν(A_old) 2^-T`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native ParentSource.Broad.Source ParentSource.Broad.Velocity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

/-- **Floors for a signal clock code.** The clock signal of `X` is `θ` times a measurable
signal `Y` with a census at all meshes from `ε` (shape `K^100 b ≤ θ w`); then the source keeps
whole clock cells of floor `lossRate θ^-d mesh^(3+d)` at a cost `K (2^steps)^3 lossRate`
(`pointwise_floors_at_steps`; `original_parent_clock_grid_source_at_steps` is the case
`Y = X/a_old`, `θ = a_old/h_old`). -/
theorem signal_clock_grid_source_at_steps {W : ℕ}
    (p : PathData W) (old : Fin p.C) (X : Po) (Y : Ev → ℝ) (hY : Measurable Y)
    (ν : Measure Ln) (source : Set Ev) (hsource : MeasurableSet source)
    {ε θ K dimension lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ) (hK : 1 ≤ K)
    (hθK : θ ≤ K) (hclock : ∀ z, θ * Y z = clockParentSignal p old X z)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * b ≤ θ * w →
      (occupied source (fun z j => unshearedPacketBase p old z j) Y b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j) Y b w).ncard : ℝ) ≤
        K / (b ^ 3 * w ^ dimension))
    (steps : ℕ) (hsteps : K ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : ε * (2 : ℝ) ^ steps ≤ θ) (hRate : 0 ≤ lossRate) :
    let reference := ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) * ν (p.A old)
    let raw := ν.prod (volume : Measure ℝ)
    let mesh := ε * (2 : ℝ) ^ steps
    let code := clockParentCode p old X mesh
    ∃ current : Set Ev, MeasurableSet current ∧ current ⊆ source ∧
      raw (source \ current) ≤ ENNReal.ofReal ((K * ((2 : ℝ) ^ steps) ^ 3) * lossRate) * reference ∧
      (activeCodes (raw.restrict current) code).Finite ∧
      ∀ q, (raw.restrict current) (code ⁻¹' {q}) = 0 ∨
        ENNReal.ofReal (lossRate * θ ^ (-dimension) * mesh ^ ((3 : ℝ) + dimension)) * reference ≤
          (raw.restrict current) (code ⁻¹' {q}) := by
  classical
  let raw := ν.prod (volume : Measure ℝ)
  let μ := raw.restrict source
  let base := fun z j => unshearedPacketBase p old z j
  have hbase : Measurable base := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_unshearedPacketBase p old)
  have hclock' : (fun z => θ * Y z) = clockParentSignal p old X := funext hclock
  obtain ⟨S, keep, hcover, hkeep, hloss, hfloor, -, -⟩ :=
    ClockCalibration.pointwise_floors_at_steps μ source (ae_restrict_mem hsource)
      base hbase Y hY hε hε1 hθ hK hθK hcensus steps hsteps hresolved hRate
      (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) * ν (p.A old))
  rw [hclock'] at hcover hfloor
  let mesh := ε * (2 : ℝ) ^ steps
  let code := clockParentCode p old X mesh
  let current := source ∩ keep
  have hcurrent : MeasurableSet current := hsource.inter hkeep
  have hlaw : μ.restrict keep = raw.restrict current := by
    rw [Measure.restrict_restrict hkeep, inter_comm]
  let S₄ := S.image flattenClockCode
  have hfinite : (activeCodes (raw.restrict current) code).Finite := by
    apply (active_codes_finite_of_finite_support (raw.restrict current) code S₄ ?_).1
    filter_upwards [ae_restrict_mem hcurrent] with z hz
    change clockParentCode p old X mesh z ∈ S₄
    rw [clockParentCode_eq_product]
    exact Finset.mem_image_of_mem _ (hcover z hz.1)
  refine ⟨current, hcurrent, inter_subset_left, ?_, hfinite, ?_⟩
  · have heq : source \ current = keepᶜ ∩ source := by
      ext z
      simp only [current, mem_sdiff, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    simpa only [μ, Measure.restrict_apply hkeep.compl] using hloss
  · intro q
    rw [clockParentCode_fibre]
    have hh := hfloor (splitClockCode q)
    rwa [hlaw] at hh


section Problem

variable {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- **Duration pruning for any signal.** Prune short earlier clock-cell durations of the clock
curve of `X` on the original assignment, from a bound on the non-constant clock coefficients. -/
theorem prune_signal_clock_durations
    (old : Fin p.C) (X : Po) {Kc coarse lossRate : ℝ} (hKc : 1 ≤ Kc)
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old)
    (hnc : ∀ q ∈ J, ∀ e : Fin 7, e ≠ 0 →
      |ParentSignal.clockPacketCoefficients X p old q.1 e| ≤ Kc)
    (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1) (hRate : 0 ≤ lossRate) :
    ∃ J' : Set Ev, MeasurableSet J' ∧ J' ⊆ J ∧
      (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) * d.ν k (p.γ old) (p.A old))⁻¹ *
          ((d.ν k (p.γ old)).prod volume) (J \ J') ≤
        ENNReal.ofReal (lossRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) ∧
      (∀ z ∈ (hp.frozenPacket old).assignedSelectedEvent J',
        ENNReal.ofReal (lossRate * coarse) ≤ incidenceDuration
          (hp.assignedClockCellSource old X J coarse
            (hp.assignedClockCode old X coarse z)) z.1) := by
  let packet := hp.frozenPacket old
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hA : d.ν k (p.γ old) packet.assigned ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  haveI : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  letI : IsProbabilityMeasure (packet.assignedPrior (d.ν k (p.γ old))) :=
    packet.assignedPrior_probability (d.ν k (p.γ old)) hA
  have hLip : ∀ z ∈ packet.assignedSelectedEvent J, ∀ s ∈ Icc (0:ℝ) 1,
      ∀ t ∈ Icc (0:ℝ) 1, ∀ j,
      |hp.assignedClockCurve old X z.1 s j - hp.assignedClockCurve old X z.1 t j| ≤
        3 * Kc * |s - t| := by
    intro z hz s hs t ht j
    have hq : packet.originalIncidence z ∈ J := by
      rwa [packet.assignedSelectedEvent_originalIncidence] at hz
    have hc := hnc _ hq
    rw [packet.originalIncidence_fst] at hc
    exact scalarPhysicalPoint_lipschitz_of_nonconstant_bound hKc hc hs ht j
  obtain ⟨keep, hkeep, hkeepE, hloss, hlong, -⟩ := exists_lipschitz_coarse_duration_source
    (packet.assignedPrior (d.ν k (p.γ old)))
    (hp.assignedClockCurve old X)
    (by positivity : 0 ≤ 3 * Kc) hcoarse hcoarse1 hRate
    (hp.measurable_assignedClockCurve old X)
    (packet.assignedSelectedEvent J) (packet.measurable_assignedSelectedEvent hJ)
    (packet.assignedSelectedEvent_unit_time hJF) hLip
  let J' := packet.originalCut J keep
  refine ⟨J', packet.measurable_originalCut hJ hkeep, packet.originalCut_subset J keep, ?_, ?_⟩
  · change (ENNReal.ofReal packet.unitFrame.q * d.ν k (p.γ old) packet.assigned)⁻¹ *
      ((d.ν k (p.γ old)).prod volume) (J \ packet.originalCut J keep) ≤ _
    rw [← packet.originalCut_loss (d.ν k (p.γ old)) hA hJ hJF hkeep,
      Broad.Source.FrozenPacket.assignedSelectedLaw, Measure.restrict_apply hkeep.compl]
    simpa only [measure_univ, mul_one, Set.sdiff_eq, inter_comm] using hloss
  · intro z hz
    rw [packet.assignedSelectedEvent_originalCut] at hz
    exact hlong z hz.2

/-- **A clock stage for a signal.** Earlier floors from the census of a signal `Y` with
`θ Y = 2^T X`, coarse clock durations from the non-constant coefficient bound, and per-code
breadth from a renewal applied to what is left; the total cost against the full old reference. -/
theorem exists_signal_clock_stage
    (old : Fin p.C) (X : Po) (good : Set Ln) (Y : Ev → ℝ) (hY : Measurable Y)
    {θ fineMesh Kcensus dimension cellRate durationRate coarse radius ratio Kc : ℝ} (steps : ℕ)
    (hθ : 0 < θ) (hclock : ∀ z, θ * Y z = clockParentSignal p old X z)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hθK : θ ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ θ)
    (hcellRate : 0 ≤ cellRate) (hdurationRate : 0 ≤ durationRate) (hKc : 1 ≤ Kc)
    (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source ⊆ p.F old)
    (hsourceGood : source ⊆ Prod.fst ⁻¹' good)
    (hnc : ∀ q ∈ source, ∀ e : Fin 7, e ≠ 0 →
      |ParentSignal.clockPacketCoefficients X p old q.1 e| ≤ Kc)
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus ^ (100 : ℕ) * b ≤ θ * w →
      (occupied source (fun z j => unshearedPacketBase p old z j) Y b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j) Y b w).ncard : ℝ) ≤
        Kcensus / (b ^ 3 * w ^ dimension))
    {renewCost : ℝ≥0∞}
    (hrenew : ∀ middle : Set Ev, MeasurableSet middle → middle ⊆ source →
      ∃ current : Set Ev, MeasurableSet current ∧ current ⊆ middle ∧
        ((d.ν k (p.γ old)).prod volume) middle ≤
          ((d.ν k (p.γ old)).prod volume) current + renewCost ∧
        ∀ label (n center : P2), ‖n‖ = 1 →
          (((d.ν k (p.γ old)).prod volume).restrict current)
            {z | clockParentCode p old X (fineMesh * (2 : ℝ) ^ steps) z = label ∧
              |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity old z - center)| ≤ radius} ≤
            ENNReal.ofReal ratio *
              (((d.ν k (p.γ old)).prod volume).restrict current)
                (clockParentCode p old X (fineMesh * (2 : ℝ) ^ steps) ⁻¹' {label})) :
    ∃ stage : SignalClockStage hp old X good θ dimension fineMesh coarse radius steps cellRate
        durationRate ratio source,
      ((d.ν k (p.γ old)).prod volume) source ≤ ((d.ν k (p.γ old)).prod volume) stage.current +
        (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
          ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4)) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) +
        renewCost := by
  classical
  let raw : Measure Ev := (d.ν k (p.γ old)).prod volume
  let reference := d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have href0 : reference ≠ 0 := mul_ne_zero (hp.assignment_mass_pos hN old).ne' (by positivity)
  have hrefTop : reference ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  obtain ⟨earlier, hearlier, hearlierSub, hlossFloor, hfinite, hfloor⟩ :=
    signal_clock_grid_source_at_steps p old X Y hY (d.ν k (p.γ old)) source hsource
      hFine hFine1 hθ hKcensus hθK hclock hcensus steps hsteps hresolved hcellRate
  have hearlierF : earlier ⊆ p.F old := hearlierSub.trans hsourceF
  obtain ⟨middle, hmiddle, hmiddleSub, hlossDur, hlong⟩ :=
    prune_signal_clock_durations hd hp old X hKc earlier hearlier hearlierF
      (fun q hq => hnc q (hearlierSub hq)) hcoarse hcoarse1 hdurationRate
  obtain ⟨current, hcurrent, hcurSub, hlossRen, hbreadth⟩ :=
    hrenew middle hmiddle (hmiddleSub.trans hearlierSub)
  refine ⟨⟨earlier, current, hearlier, hcurrent, hcurSub.trans hmiddleSub, hearlierSub,
    fun z hz => hsourceGood (hearlierSub (hmiddleSub (hcurSub hz))), hfinite, ?_, ?_, hbreadth⟩, ?_⟩
  · intro q
    rcases hfloor q with h0 | h1
    · exact Or.inl h0
    · right
      refine le_trans (le_of_eq ?_) h1
      rw [mul_comm (d.ν k (p.γ old) (p.A old))]
  · intro z hz
    apply hlong z
    exact Set.preimage_mono (Set.image_mono hcurSub) hz
  · -- the cost
    have hmassFloor : raw source ≤ raw earlier +
        ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) * reference := by
      apply (measure_mono (show source ⊆ earlier ∪ (source \ earlier) from fun z hz => by
        by_cases h : z ∈ earlier
        · exact Or.inl h
        · exact Or.inr ⟨hz, h⟩)).trans
      apply (measure_union_le _ _).trans
      apply add_le_add le_rfl
      simpa only [mul_comm (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))
        (d.ν k (p.γ old) (p.A old))] using hlossFloor
    have hlossDur' : raw (earlier \ middle) ≤
        ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) * reference := by
      rw [mul_comm (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))
        (d.ν k (p.γ old) (p.A old))] at hlossDur
      calc raw (earlier \ middle) = reference * (reference⁻¹ * raw (earlier \ middle)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel href0 hrefTop, one_mul]
        _ ≤ reference * ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) :=
            mul_le_mul' le_rfl hlossDur
        _ = _ := mul_comm _ _
    have hmassDur : raw earlier ≤ raw middle +
        ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) * reference := by
      apply (measure_mono (show earlier ⊆ middle ∪ (earlier \ middle) from fun z hz => by
        by_cases h : z ∈ middle
        · exact Or.inl h
        · exact Or.inr ⟨hz, h⟩)).trans
      exact (measure_union_le _ _).trans (add_le_add le_rfl hlossDur')
    calc raw source ≤ raw earlier +
          ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) * reference := hmassFloor
      _ ≤ (raw middle + ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) * reference) +
          ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) * reference :=
          add_le_add hmassDur le_rfl
      _ ≤ ((raw current + renewCost) +
            ENNReal.ofReal (durationRate * (3 * Kc + 3) * (7 : ℝ) ^ 4) * reference) +
          ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) * reference :=
          add_le_add (add_le_add hlossRen le_rfl) le_rfl
      _ = _ := by ring

end Problem

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
