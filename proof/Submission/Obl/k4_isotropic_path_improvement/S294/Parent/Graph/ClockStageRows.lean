-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.ClockStageRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/ClockStageRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). The physical velocity graph on the actual safe clock model of
an old packet, from one actual clock stage (`OriginalParentClockStage`, this
LOT tree, o265, session x1046, ported in
`ParentSource/Broad/Source/DenseRootClockStages.lean`).

* `clockModel`: the `Qualification.PhysicalModel` of an old packet over an
  original source: the literal clock coefficients (`safeClockCoefficients`:
  signal `2^T P = P/h`, unsheared old base, original planar velocity, jets
  `≤ 24 K_k`), assignment the full old assignment, events the time-changed
  source incidences on clock-good lines; `clockModel_prior` is the exact full
  old prior; `clockModel_code_eq` reads the stage's clock parent codes.
* `stage_model_durations`, `stage_model_count`, `stage_model_breadth`: the
  duration, hereditary count and per-cell breadth inputs of
  `model_velocity_rows` from the stage's coarse clock durations, earlier
  floors (with a clock-unit band cap) and normalized-velocity strip caps
  (through the old frame, `original_strip_normalized`, cost `N^(2δ₀L)`).
* `stage_velocity_rows`: rows on the stage mesh codes with
  `|(signal)'(t) - Σ row_j · (1, V)_j| ≤ 80 Kg⁷ mesh^((1-dim)/24)` on a retained
  part of the selected stage current, loss `ε·earlier + gfraction·current`.
* `clock_band_of_moving_band`, `stage_velocity_rows_of_moving_band`: the band
  cap from x1035's `OriginalPacketCaps.moving_band_cap`.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.ModelBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.ModelCount
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.Numerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.HereditaryClockSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorFullPrior
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPacketCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.DenseRootDyadicClock
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentAssigned
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AffineStripTransfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFrameChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPrior

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native ParentSource.Broad.Source
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

theorem measurable_modelPlanar (pm : Qualification.PhysicalModel) :
    Measurable (modelPlanar pm) := by
  unfold modelPlanar
  apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · change Measurable (fun l => pm.scalarCoefficients l 4)
    exact (measurable_pi_apply 4).comp pm.measurable_scalarCoefficients
  · change Measurable (fun l => pm.scalarCoefficients l 6)
    exact (measurable_pi_apply 6).comp pm.measurable_scalarCoefficients

theorem measurable_modelVelocity (pm : Qualification.PhysicalModel) :
    Measurable (fun l => (WithLp.toLp 2 (pm.velocity l) : EuclideanSpace ℝ (Fin 3))) := by
  apply (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · change Measurable (fun l => pm.scalarCoefficients l 4)
    exact (measurable_pi_apply 4).comp pm.measurable_scalarCoefficients
  · change Measurable (fun l => pm.scalarCoefficients l 6)
    exact (measurable_pi_apply 6).comp pm.measurable_scalarCoefficients

section Clock

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}

/-- The coefficient slack of the clock model of an old packet. -/
def clockSlack (old : Fin p.C) : ℝ :=
  (max 24 (max p.κ (d.K k))) ^ 4 * (2 : ℝ) ^ p.T (p.lev old)

theorem clockSlack_nonneg (old : Fin p.C) : 0 ≤ clockSlack old := by
  unfold clockSlack
  exact mul_nonneg (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 24).trans (le_max_left _ _)) _)
    (by positivity)

/-- The original lines on which the safe clock jets are the literal parent jets. -/
abbrev clockGood (old : Fin p.C) : Set Ln :=
  ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))

/-- The safe clock coefficients of an old packet. -/
abbrev clockCoefficients (old : Fin p.C) : Ln → Fin 7 → ℝ :=
  ParentSignal.safeClockCoefficients (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) p old

variable (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) (old : Fin p.C)

/-- The time change of the old packet is the old packet time. -/
theorem clock_timeChange (x : Ev) :
    (hp.frozenPacket old).timeChange x = (x.1, packetTime p old x) := by
  rw [(hp.frozenPacket old).timeChange_apply]
  have hframe : (hp.frozenPacket old).unitFrame = nativeOldBaseFrame p old := rfl
  rw [hframe]
  simp only [packetTime, div_eq_mul_inv, mul_comm]

/-- The events of the clock model over an original source `J`. -/
def clockEvent (J : Set Ev) : Set Ev :=
  (hp.frozenPacket old).selectedEvent (J ∩ Prod.fst ⁻¹' clockGood old)

theorem measurable_clockEvent {J : Set Ev} (hJ : MeasurableSet J) :
    MeasurableSet (clockEvent hp old J) :=
  (hp.frozenPacket old).measurable_selectedEvent
    (hJ.inter (measurable_fst (ParentSignal.measurableSet_clockJetGood _ _ _)))

theorem clockEvent_coefficients (hd : d.Valid) {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ clockEvent hp old J, ∀ i, |clockCoefficients old z.1 i| ≤ clockSlack old := by
  rintro z ⟨x, ⟨hxJ, hxG⟩, rfl⟩ i
  rw [clock_timeChange hp old x]
  have hxG' : x.1 ∈ ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := hxG
  change |ParentSignal.safeClockCoefficients (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) p old x.1 i| ≤ _
  rw [ParentSignal.safeClockCoefficients_eq _ _ _ _ _ hxG']
  have hP := (ParentSignal.original_parent_bounds (show ParentSource.pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  have hA : x.1 ∈ p.A old := ((hp.frozenPacket old).counted_inside_original (hJF hxJ)).2.1
  exact AncestorSource.assigned_clock_coefficients_bound hp old hP (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    hA hxG'.1 hxG'.2 i


theorem clockEvent_assignment {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ clockEvent hp old J, z.1 ∈ (hp.frozenPacket old).assigned := by
  rintro z ⟨x, ⟨hxJ, -⟩, rfl⟩
  rw [clock_timeChange hp old x]
  exact ((hp.frozenPacket old).counted_inside_original (hJF hxJ)).2.1

theorem clockEvent_time {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ clockEvent hp old J, z.2 ∈ Icc (0 : ℝ) 1 := by
  intro z hz
  exact ((hp.frozenPacket old).event_unit_time
    ((hp.frozenPacket old).selectedEvent_subset (inter_subset_left.trans hJF) hz)).2

/-- **The safe clock model of an old packet** over a measurable original
source `J`: the literal clock coefficients of the old packet (signal
`2^T P`, unsheared base, original planar velocity) with the four jets
erased off the clock-good lines, its assignment the full old assignment
(cut to the coefficient slack, an almost-everywhere cut), and its events
the time-changed incidences of `J` on clock-good lines. -/
def clockModel (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) :
    Qualification.PhysicalModel :=
  Qualification.PhysicalModel.ofCoefficients (clockCoefficients old)
    (ParentSignal.measurable_safeClockCoefficients _ _ _ _ _)
    (hp.frozenPacket old).assigned (hp.frozenPacket old).measurable_assigned
    (clockSlack old) (clockSlack_nonneg old)
    (clockEvent hp old J) (measurable_clockEvent hp old hJ)
    (clockEvent_assignment hp old hJF) (clockEvent_time hp old hJF)
    (clockEvent_coefficients hp old hd hJF)

theorem clockModel_event (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) : (clockModel hp old hd J hJ hJF).event = clockEvent hp old J := rfl

theorem clockModel_coefficients (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) :
    (clockModel hp old hd J hJ hJF).scalarCoefficients = clockCoefficients old := rfl

/-- Original lines carry almost surely the box bound of the problem. -/
theorem ae_velocity_le (hd : d.Valid) (w : Fin (d.W k)) :
    ∀ᵐ l ∂d.ν k w, ‖v l‖ ≤ d.K k := by
  have hpb : ParentSource.pb d.N d.K d.L d.d d.S d.η d.W d.ω d.ν d.E d.P d.B d.f d.g d.G := hd
  rcases hpb with ⟨_, _, _, _, _, _, _, _, hrest⟩
  obtain ⟨M, D, hdata⟩ := hrest.1
  rcases (hdata k).2.2.2.1 w with ⟨_, _, _, _, _, _, _, _, _, _, _, hline, _⟩
  filter_upwards [hline] with l hl
  exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hl 0 ⟨le_rfl, zero_le_one⟩).1

include hp in
/-- A clock-good assigned line satisfies the coefficient slack. -/
theorem clock_coefficients_le (hd : d.Valid) {l : Ln} (hl : l ∈ p.A old)
    (hG : l ∈ clockGood old) : ∀ i, |clockCoefficients old l i| ≤ clockSlack old := by
  intro i
  have hG' : l ∈ ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := hG
  change |ParentSignal.safeClockCoefficients (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) p old l i| ≤ _
  rw [ParentSignal.safeClockCoefficients_eq _ _ _ _ _ hG']
  have hP := (ParentSignal.original_parent_bounds (show ParentSource.pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  exact AncestorSource.assigned_clock_coefficients_bound hp old hP (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    hl hG'.1 hG'.2 i

/-- The clock model keeps the exact full original assignment prior of the old packet. -/
theorem clockModel_prior (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) :
    (clockModel hp old hd J hJ hJF).prior (d.ν k (p.γ old)) =
      (hp.frozenPacket old).prior (d.ν k (p.γ old)) := by
  rw [(hp.frozenPacket old).prior_eq]
  apply Qualification.PhysicalModel.ofCoefficients_prior
  have hparent := ParentSignal.original_parent_bounds (show ParentSource.pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)
  filter_upwards [hparent.2.2.1, ae_velocity_le hd (p.γ old)] with l hgood hvel
  intro hl
  exact clock_coefficients_le hp old hd hl ⟨hgood, hvel⟩

/-- A clock-good assigned line is assigned in the clock model. -/
theorem clockModel_assigned (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {l : Ln} (hl : l ∈ p.A old) (hG : l ∈ clockGood old) :
    l ∈ (clockModel hp old hd J hJ hJF).assigned :=
  ⟨hl, clock_coefficients_le hp old hd hl hG⟩

/-- On a clock-good counted incidence the model code of the time-changed
incidence reads the clock parent coordinates: the unsheared base and the
physical parent in clock units. -/
theorem clockModel_code (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {x : Ev} (hxF : x ∈ p.F old) (hG : x.1 ∈ clockGood old) (b h : ℝ) :
    modelCode (clockModel hp old hd J hJ hJF) b h ((hp.frozenPacket old).timeChange x) =
      fun j => ⌊clockParentCoordinates p old (d.P k (p.γ old)) x j /
        (if j = 3 then h else b)⌋ := by
  have hA : x.1 ∈ p.A old := ((hp.frozenPacket old).counted_inside_original hxF).2.1
  have hl := clockModel_assigned hp old hd J hJ hJF hA hG
  have hG' : x.1 ∈ ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := hG
  have hP := (ParentSignal.original_parent_bounds (show ParentSource.pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  have hpt := ParentSignal.clockPacket_point hP p old x
  rw [← ParentSignal.safeClockCoefficients_eq _ _ _ _ _ hG'] at hpt
  rw [clock_timeChange hp old x]
  funext j
  simp only [modelCode, coefficientGridCode]
  rw [modelCoefficients_of_mem _ hl, clockModel_coefficients]
  change ⌊coefficientPhysical (clockCoefficients old x.1) (packetTime p old x) j / _⌋ = _
  rw [hpt]
  congr 2
  fin_cases j <;> rfl

/-- At equal base and signal mesh the model code is the stage's clock parent code. -/
theorem clockModel_code_eq (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {x : Ev} (hxF : x ∈ p.F old) (hG : x.1 ∈ clockGood old) (b : ℝ) :
    modelCode (clockModel hp old hd J hJ hJF) b b ((hp.frozenPacket old).timeChange x) =
      clockParentCode p old (d.P k (p.γ old)) b x := by
  rw [clockModel_code hp old hd J hJ hJF hxF hG b b]
  funext j
  simp only [ite_self]
  rfl

/-- On a clock-good line the planar velocity of the model is the original one. -/
theorem clockModel_planar (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {l : Ln} (hG : l ∈ clockGood old) :
    modelPlanar (clockModel hp old hd J hJ hJF) l = v l := by
  have hG' : l ∈ ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := hG
  have hv := ParentSignal.clockPacket_velocity (d.P k (p.γ old)) p old l
  rw [← ParentSignal.safeClockCoefficients_eq _ _ _ _ _ hG'] at hv
  ext i
  fin_cases i
  · exact congrFun hv 0
  · exact congrFun hv 1

/-- The stage's assigned clock code and the model code agree on every
time of a clock-good assigned line. -/
theorem clockModel_assignedCode (hd : d.Valid) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {l : Ln} (hl : l ∈ (hp.frozenPacket old).assigned)
    (hG : l ∈ clockGood old) (b t : ℝ) :
    hp.assignedClockCode old (d.P k (p.γ old)) b (⟨l, hl⟩, t) =
      modelCode (clockModel hp old hd J hJ hJF) b b (l, t) := by
  have hlm := clockModel_assigned hp old hd J hJ hJF hl hG
  have hG' : l ∈ ParentSignal.clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := hG
  funext j
  simp only [Native.PathData.Valid.assignedClockCode, curveCoarseCode,
    Native.PathData.Valid.assignedClockCurve, Native.PathData.Valid.assignedClockCoefficients,
    modelCode, coefficientGridCode, ite_self]
  rw [modelCoefficients_of_mem _ hlm, clockModel_coefficients]
  change _ = ⌊coefficientPhysical (ParentSignal.safeClockCoefficients (d.P k (p.γ old)) (d.K k)
    (d.B k (p.γ old)) p old l) t j / b⌋
  rw [ParentSignal.safeClockCoefficients_eq _ _ _ _ _ hG']
  congr 2

/-- The model law of selected events is the original law divided by the
full old reference (old block length times full assignment mass). -/
theorem selected_prod_apply (hd : d.Valid) {J : Set Ev} (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {X : Set Ev} (hX : MeasurableSet X) :
    (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
        ((hp.frozenPacket old).selectedEvent J ∩ X) =
      (ENNReal.ofReal (hp.frozenPacket old).unitFrame.q * d.ν k (p.γ old) (p.A old))⁻¹ *
        ((d.ν k (p.γ old)).prod volume) (J ∩ (hp.frozenPacket old).timeChange ⁻¹' X) := by
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hA : d.ν k (p.γ old) (hp.frozenPacket old).assigned ≠ 0 :=
    (hp.assignment_mass_pos hN old).ne'
  have h := congrArg (fun μ : Measure Ev => μ X)
    ((hp.frozenPacket old).selectedLaw_original (d.ν k (p.γ old)) hA hJ hJF)
  simp only [FrozenPacket.selectedLaw, Measure.restrict_apply hX, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (hp.frozenPacket old).timeChange.measurable hX,
    Measure.restrict_apply ((hp.frozenPacket old).timeChange.measurable hX)] at h
  rw [inter_comm, h, inter_comm]
  rfl

/-- The reference of the selected transport is positive and finite. -/
theorem selected_reference (hd : d.Valid) :
    ENNReal.ofReal (hp.frozenPacket old).unitFrame.q * d.ν k (p.γ old) (p.A old) ≠ 0 ∧
      ENNReal.ofReal (hp.frozenPacket old).unitFrame.q * d.ν k (p.γ old) (p.A old) ≠ ⊤ := by
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN : 0 < d.N k := by linarith [hd.1 k]
  exact ⟨mul_ne_zero (ENNReal.ofReal_pos.mpr (hp.frozenPacket old).unitFrame_length_pos).ne'
      (hp.assignment_mass_pos hN old).ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩

include hp in
/-- **Frame transfer.** An original planar-velocity strip of width `w` lies
in one strip of the old packet's normalized velocity `(6κ)⁻¹ Q⁻¹(v - u)/h`
of width `w N^(2δ₀L)/6`: the old frame's condition number is the only cost. -/
theorem original_strip_normalized (hN : 1 ≤ d.N k) {w radius : ℝ} (hw : 0 ≤ w)
    (hscale : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (hn : ‖n‖ = 1) :
    ∃ normal center : EuclideanSpace ℝ (Fin 2), ‖normal‖ = 1 ∧
      ∀ x : Ev, |inner ℝ n (v x.1) - t| ≤ w →
        |inner ℝ normal ((6 * p.κ)⁻¹ • p.normalizedVelocity old x - center)| ≤ radius := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hC : 0 ≤ p.κ * d.N k ^ (2 * δ₀ * d.L) := by positivity
  obtain ⟨normal, offset, hnormal, hsub⟩ := affine_velocity_strip_pullback
    (p.denormalizedFrameOperator old) (p.normalizedFrameOperator old) hC hw
    (hp.normalized_frame_operator_bound hN old) (hp.denormalized_normalized_frame_cancel old)
    le_rfl n (p.u old) (t • n) hn
  refine ⟨normal, ((6 * p.κ)⁻¹ * offset) • normal, hnormal, ?_⟩
  intro x hx
  have hy : p.normalizedVelocity old x = p.normalizedFrameOperator old (v x.1 - p.u old) := rfl
  have hmem := hsub (show p.normalizedVelocity old x ∈ {y | |inner ℝ n
      (p.denormalizedFrameOperator old y + p.u old - t • n)| ≤ w} by
    simp only [mem_ofPred_eq]
    rw [hy, hp.denormalized_normalized_frame_cancel, sub_add_cancel, inner_sub_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn]
    simpa using hx)
  simp only [mem_ofPred_eq] at hmem
  rw [inner_sub_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hnormal]
  have heq : (6 * p.κ)⁻¹ * inner ℝ normal (p.normalizedVelocity old x) -
      (6 * p.κ)⁻¹ * offset * 1 ^ 2 =
      (6 * p.κ)⁻¹ * (inner ℝ (p.normalizedVelocity old x) normal - offset) := by
    rw [real_inner_comm]; ring
  rw [heq, abs_mul, abs_of_pos (by positivity)]
  calc (6 * p.κ)⁻¹ * |inner ℝ (p.normalizedVelocity old x) normal - offset|
      ≤ (6 * p.κ)⁻¹ * (w * (p.κ * d.N k ^ (2 * δ₀ * d.L))) := by gcongr
    _ = w * d.N k ^ (2 * δ₀ * d.L) / 6 := by field_simp
    _ ≤ radius := by linarith

include hp in
/-- **The clock band cap from the original moving band cap.** A clock band
of width `coarse` around a measurable function of the unsheared old base is
a physical band of width `coarse/θ`, `θ = a_old/h_old`; the original moving
band cap (`OriginalPacketCaps.moving_band_cap`) then gives the clock-unit
cap consumed by `stage_velocity_rows`, with constant
`64 max(κ,K)² κ 4^dim N^(2 error + τ + 2δ₀L + ε)`. -/
theorem clock_band_of_moving_band {T : Type*} {H : Fin (d.W k) → Set Ev} {u : T → ℝ}
    {τ ε : ℝ} (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε)
    (hd : d.Valid) (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    (J : Set Ev) (hJ : MeasurableSet J) (hJE : J ⊆ d.E k (p.γ old))
    (hJbase : J ⊆ Q.base (p.γ old)) (hJF : J ⊆ p.F old)
    {dimension f₀ error coarse : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ error)
    (hcoarse : 0 < coarse)
    (hresolved : d.N k ^ (-(d.L - p.r (p.lev old))) ≤
      4 * (coarse / (δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹))) :
    ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ old)).prod volume).restrict J)
        {x | unshearedPacketBase p old x ∈ U ∧
          |clockParentSignal p old (d.P k (p.γ old)) x - c (unshearedPacketBase p old x)| ≤
            coarse} ≤
      ENNReal.ofReal ((64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
          d.N k ^ (2 * error + (τ + 2 * δ₀ * d.L) + ε)) *
          (δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹) ^ (-dimension) *
          coarse ^ dimension) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) *
          volume U := by
  intro U hU c hc
  set θ := δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹ with hθdef
  have hθ : 0 < θ := by
    have : 0 < δ (d.N k) (p.r (p.lev old)) := by unfold δ; positivity
    positivity
  have hN0 : 0 < d.N k := by linarith [hd.1 k]
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hA : d.ν k (p.γ old) (p.A old) ≠ 0 := (hp.assignment_mass_pos hN0 old).ne'
  have hset : {x | unshearedPacketBase p old x ∈ U ∧
        |clockParentSignal p old (d.P k (p.γ old)) x - c (unshearedPacketBase p old x)| ≤
          coarse} =
      {x | unshearedPacketBase p old x ∈ U ∧
        |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) x -
          (fun b => c b / θ) (unshearedPacketBase p old x)| ≤ coarse / θ} := by
    ext x
    simp only [mem_ofPred_eq]
    have key : clockParentSignal p old (d.P k (p.γ old)) x =
        θ * physicalParentSignal (d.N k) p old (d.P k (p.γ old)) x :=
      (physicalParent_clock_relation (d.N k) p old (d.P k (p.γ old)) x).symm
    have hid : θ * physicalParentSignal (d.N k) p old (d.P k (p.γ old)) x -
        c (unshearedPacketBase p old x) =
        θ * (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) x -
          c (unshearedPacketBase p old x) / θ) := by
      field_simp
    rw [key, hid, abs_mul, abs_of_pos hθ, le_div_iff₀ hθ, mul_comm θ]
  rw [hset]
  have h := OriginalPacketCaps.moving_band_cap Q hpure hd hp old hr hrL J hJ hJE hJbase hJF hA
    hdim hprofile (div_pos hcoarse hθ) hresolved U hU (fun b => c b / θ) (hc.div_const θ)
  refine h.trans (le_of_eq ?_)
  rw [Real.div_rpow hcoarse.le hθ.le, mul_comm (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))]
  congr 3
  rw [Real.rpow_neg hθ.le]
  ring

section Stage

variable {K census dimension precision coarse radius fraction : ℝ} {R steps : ℕ}
    {source : Set Ev}

/-- The stage's current incidences in cells of positive earlier original mass
(at the stage mesh); an original null set is removed. -/
def stagePositive
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) : Set Ev :=
  stage.current ∩ clockParentCode p old (d.P k (p.γ old)) (precision * (2 : ℝ) ^ steps) ⁻¹'
    activeCodes (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
      (clockParentCode p old (d.P k (p.γ old)) (precision * (2 : ℝ) ^ steps))

theorem measurable_stagePositive
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) : MeasurableSet (stagePositive hp old stage) :=
  stage.current_measurable.inter
    ((measurable_clockParentCode p old _ _) (Set.to_countable _).measurableSet)

theorem stagePositive_subset
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) : stagePositive hp old stage ⊆ stage.current := inter_subset_left

theorem stagePositive_null
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) :
    ((d.ν k (p.γ old)).prod volume) (stage.current \ stagePositive hp old stage) = 0 := by
  set code := clockParentCode p old (d.P k (p.γ old)) (precision * (2 : ℝ) ^ steps)
  set μE := ((d.ν k (p.γ old)).prod volume).restrict stage.earlier
  have hsub : stage.current \ stagePositive hp old stage ⊆
      ⋃ q : Fin 4 → ℤ, ⋃ (_ : q ∉ activeCodes μE code), (code ⁻¹' {q} ∩ stage.earlier) := by
    rintro x ⟨hx, hxn⟩
    simp only [mem_iUnion]
    exact ⟨code x, fun hact => hxn ⟨hx, hact⟩, rfl, stage.current_subset hx⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro q
  apply measure_iUnion_null
  intro hq
  have h0 : μE {x | code x = q} = 0 := by
    by_contra h
    exact hq h
  rw [Measure.restrict_apply' stage.earlier_measurable] at h0
  exact h0

/-- **Durations** of the clock model on the stage's selected current
events: the stage's own coarse clock durations, read in the model. -/
theorem stage_model_durations (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old) :
    ∀ z ∈ (hp.frozenPacket old).selectedEvent stage.current,
      ENNReal.ofReal (parentClockDurationRate K * coarse) ≤
        incidenceDuration ((clockModel hp old hd stage.earlier stage.earlier_measurable hF).event ∩
          modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF) coarse coarse ⁻¹'
            {modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
              coarse coarse z}) z.1 := by
  rintro z ⟨x, hx, rfl⟩
  have hxF : x ∈ p.F old := hF (stage.current_subset hx)
  have hA : x.1 ∈ (hp.frozenPacket old).assigned :=
    ((hp.frozenPacket old).counted_inside_original hxF).2.1
  have hG : x.1 ∈ clockGood old := stage.clock_good hx
  have hz : (hp.frozenPacket old).timeChange x = (x.1, packetTime p old x) :=
    clock_timeChange hp old x
  let z' : (hp.frozenPacket old).AssignedLine × ℝ := (⟨x.1, hA⟩, packetTime p old x)
  have hz' : z' ∈ (hp.frozenPacket old).assignedSelectedEvent stage.current :=
    ⟨x, hx, hz⟩
  have hdur := stage.durations z' hz'
  rw [hz]
  apply hdur.trans
  apply measure_mono
  intro t ht
  obtain ⟨hsel, hcode⟩ := ht
  obtain ⟨y, hy, hyt⟩ := hsel
  have hy1 : y.1 = x.1 := by
    have h1 := congrArg Prod.fst hyt
    rw [clock_timeChange hp old y] at h1
    exact h1
  refine ⟨⟨y, ⟨hy, ?_⟩, hyt⟩, ?_⟩
  · change y.1 ∈ clockGood old
    rw [hy1]
    exact hG
  · simp only [mem_preimage, mem_singleton_iff]
    rw [← clockModel_assignedCode hp old hd _ _ hF hA hG coarse t,
      ← clockModel_assignedCode hp old hd _ _ hF hA hG coarse (packetTime p old x)]
    exact hcode

/-- Flattened product codes: the first three entries and the last. -/
theorem flattenClockCode_eq_iff (a : (Fin 3 → ℤ) × ℤ) (q : Fin 4 → ℤ) :
    flattenClockCode a = q ↔ a = (Fin.init q, q (Fin.last 3)) := by
  constructor
  · rintro rfl
    ext i
    · simp [flattenClockCode, Fin.init_snoc]
    · change a.2 = Fin.snoc (α := fun _ => ℤ) a.1 a.2 (Fin.last 3)
      rw [Fin.snoc_last]
  · rintro rfl
    exact Fin.snoc_init_self q

/-- **Hereditary count** of the clock model's fine codes inside each coarse
code, from the stage's earlier floors and a clock-unit band cap of the
earlier original law (`HereditaryClockSupport.exists_hereditary_support`). -/
theorem stage_model_count (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old)
    (n : ℕ) (hmesh : precision * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hK : 0 < K) (hcensus : 0 < census) (hdim : 0 ≤ dimension)
    {Cband Kc : ℝ} (hCband : 0 ≤ Cband) (hKc1 : 1 ≤ Kc)
    (hKc : 8 * Cband / parentClockCellRate K census ((2 : ℝ) ^ steps) ≤ Kc)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
        {x | unshearedPacketBase p old x ∈ U ∧
          |clockParentSignal p old (d.P k (p.γ old)) x - c (unshearedPacketBase p old x)| ≤
            coarse} ≤
      ENNReal.ofReal (Cband * (δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹) ^
          (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * volume U)
    (q : Fin 4 → ℤ) :
    ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ Kc * (coarse / Submission.Lib.K4DyadicRowScales.mesh n) ^ 3 *
        (coarse / Submission.Lib.K4DyadicRowScales.mesh n) ^ dimension ∧
      ∀ z ∈ (hp.frozenPacket old).selectedEvent (stagePositive hp old stage),
        modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF) coarse coarse z =
            q →
          modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
            (Submission.Lib.K4DyadicRowScales.mesh n) (Submission.Lib.K4DyadicRowScales.mesh n) z ∈
              S := by
  classical
  set mesh := Submission.Lib.K4DyadicRowScales.mesh n with hmeshdef
  set P := d.P k (p.γ old)
  set θ := δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹
  set rate := parentClockCellRate K census ((2 : ℝ) ^ steps)
  set reference := d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)
  set μ := ((d.ν k (p.γ old)).prod volume).restrict stage.earlier
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hmesh0 : 0 < mesh := Submission.Lib.K4DyadicRowScales.mesh_pos n
  have hcoarse0 : 0 < coarse := hcoarse ▸ Submission.Lib.K4DyadicRowScales.coarse_pos n
  have hθ : 0 < θ := by
    have : 0 < δ (d.N k) (p.r (p.lev old)) := by unfold δ; positivity
    positivity
  have hrate : 0 < rate := parentClockCellRate_pos hK hcensus (by positivity)
  have href : 0 < reference := by
    apply ENNReal.mul_pos (hp.assignment_mass_pos hN old).ne'
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hreftop : reference ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hbox : stage.earlier ⊆ univ ×ˢ Icc (hp.frozenPacket old).unitFrame.t₀
      ((hp.frozenPacket old).unitFrame.t₀ + (hp.frozenPacket old).unitFrame.q) := by
    intro x hx
    exact ⟨mem_univ _, ((hp.frozenPacket old).counted_inside_original (hF hx)).2.2⟩
  have hfin : ((d.ν k (p.γ old)).prod volume) stage.earlier ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hbox)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [Real.volume_Icc])
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfin
  have hRb : coarse = mesh * (2 : ℝ) ^ n := by
    rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_eq_mesh_mul_pow n
  have hgrid (b : ℝ) (x : Ev) : clockParentCode p old P b x =
      flattenClockCode (gridCode (fun z j => unshearedPacketBase p old z j)
        (clockParentSignal p old P) b b x) := clockParentCode_eq_product p old P b x
  let gm := gridCode (fun x j => unshearedPacketBase p old x j) (clockParentSignal p old P)
    mesh mesh
  have hFloor : ∀ x ∈ stagePositive hp old stage,
      ENNReal.ofReal (rate * θ ^ (-dimension) * mesh ^ 3 * mesh ^ dimension) * reference ≤
        μ (gm ⁻¹' {gm x}) := by
    intro x hx
    have hact := hx.2
    have hcell : clockParentCode p old P mesh ⁻¹' {clockParentCode p old P mesh x} =
        gm ⁻¹' {gm x} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, hgrid]
      exact flattenClockCode_injective.eq_iff
    rcases stage.earlier_floor (clockParentCode p old P (precision * (2 : ℝ) ^ steps) x) with h0 | h1
    · exact absurd h0 (by rw [hmesh] at hact ⊢; exact hact)
    · rw [hmesh, hcell] at h1
      have hpow : mesh ^ ((3 : ℝ) + dimension) = mesh ^ 3 * mesh ^ dimension := by
        rw [Real.rpow_add hmesh0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have heq : rate * θ ^ (-dimension) * mesh ^ 3 * mesh ^ dimension =
          rate * θ ^ (-dimension) * mesh ^ ((3 : ℝ) + dimension) := by
        rw [hpow]; ring
      rw [heq]
      exact h1
  obtain ⟨F, hFcard, hFmem, -⟩ := HereditaryClockSupport.exists_hereditary_support μ
    (unshearedPacketBase p old) (measurable_unshearedPacketBase p old)
    (clockParentSignal p old P) (measurable_clockParentSignal (d.N k) p old P)
    (stagePositive hp old stage) reference href hreftop hmesh0 hmesh0 hcoarse0 hθ hrate hCband
    n n hRb hRb hFloor hband (Fin.init q, q (Fin.last 3))
  let S0 : Finset (Fin 4 → ℤ) := F.image flattenClockCode
  have hone : (1 : ℝ) ≤ Kc * (coarse / mesh) ^ 3 * (coarse / mesh) ^ dimension := by
    have h1 : 1 ≤ coarse / mesh := (one_le_div hmesh0).mpr (by
      rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.mesh_le_coarse n)
    have h3 : 1 ≤ (coarse / mesh) ^ 3 := one_le_pow₀ h1
    have h4 : 1 ≤ (coarse / mesh) ^ dimension := Real.one_le_rpow h1 hdim
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ Kc * (coarse / mesh) ^ 3 * (coarse / mesh) ^ dimension := by gcongr
  have hcard : (S0.card : ℝ) ≤ Kc * (coarse / mesh) ^ 3 * (coarse / mesh) ^ dimension := by
    refine (Nat.cast_le.mpr Finset.card_image_le).trans (hFcard.trans ?_)
    gcongr
  have hmem : ∀ z ∈ (hp.frozenPacket old).selectedEvent (stagePositive hp old stage),
      modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF) coarse coarse z =
          q →
        modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
          mesh mesh z ∈ S0 := by
    rintro z ⟨x, hx, rfl⟩ hq
    have hxF : x ∈ p.F old := hF (stage.current_subset hx.1)
    have hG : x.1 ∈ clockGood old := stage.clock_good hx.1
    rw [clockModel_code_eq hp old hd _ _ hF hxF hG, hgrid] at hq ⊢
    exact Finset.mem_image_of_mem _ (hFmem x hx ((flattenClockCode_eq_iff _ _).mp hq))
  by_cases hne : S0.Nonempty
  · exact ⟨S0, hne, hcard, hmem⟩
  · refine ⟨insert 0 S0, Finset.insert_nonempty _ _, ?_, fun z hz hq =>
      Finset.mem_insert_of_mem (hmem z hz hq)⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, insert_empty_eq, Finset.card_singleton, Nat.cast_one]
    exact hone

/-- **Breadth** of the clock model on the positive selected stage events:
the stage's normalized-velocity strip caps, read on original planar
velocity strips of width `w` (`w N^(2δ₀L) ≤ 6 radius`). -/
theorem stage_model_strip (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old)
    {w : ℝ} (hw : 0 ≤ w) (hscale : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (label : Fin 4 → ℤ) (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (hn : ‖n‖ = 1) :
    (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
        ((hp.frozenPacket old).selectedEvent (stagePositive hp old stage) ∩
          modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
            (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar (clockModel hp old hd stage.earlier
            stage.earlier_measurable hF) z.1) - t| ≤ w}) ≤
      ((ENNReal.ofReal (parentRenewalFloor K R))⁻¹ * ENNReal.ofReal (8 * fraction)) *
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
          ((hp.frozenPacket old).selectedEvent (stagePositive hp old stage) ∩
            modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
              (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label}) := by
  set pm := clockModel hp old hd stage.earlier stage.earlier_measurable hF
  set mesh := precision * (2 : ℝ) ^ steps
  set E := stagePositive hp old stage
  set τ := (hp.frozenPacket old).timeChange
  set ν := d.ν k (p.γ old)
  set ratio := (ENNReal.ofReal (parentRenewalFloor K R))⁻¹ * ENNReal.ofReal (8 * fraction)
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  obtain ⟨normal, center, hnormal, hstrip⟩ :=
    original_strip_normalized hp old hN hw hscale n t hn
  have hE : MeasurableSet E := measurable_stagePositive hp old stage
  have hEF : E ⊆ p.F old := fun x hx => hF (stage.current_subset hx.1)
  have hcodem : MeasurableSet (modelCode pm mesh mesh ⁻¹' {label}) :=
    measurable_modelCode pm mesh mesh (measurableSet_singleton label)
  have hstripm : MeasurableSet {z : Ev | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w} := by
    apply measurableSet_le _ measurable_const
    exact ((measurable_const.inner ((measurable_modelPlanar pm).comp measurable_fst)).sub
      measurable_const).abs
  have hpt (x : Ev) (hx : x ∈ E) : modelCode pm mesh mesh (τ x) =
      clockParentCode p old (d.P k (p.γ old)) mesh x ∧ (τ x).1 = x.1 ∧
        modelPlanar pm x.1 = v x.1 :=
    ⟨clockModel_code_eq hp old hd _ _ hF (hEF hx) (stage.clock_good hx.1) mesh,
      by rw [clock_timeChange hp old x],
      clockModel_planar hp old hd _ _ hF (stage.clock_good hx.1)⟩
  rw [inter_assoc, selected_prod_apply hp old hd hE hEF (hcodem.inter hstripm),
    selected_prod_apply hp old hd hE hEF hcodem, mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  have hcur := stage.current_measurable
  calc ((ν.prod volume)) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label} ∩
        {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w}))
      ≤ (ν.prod volume) ({x | clockParentCode p old (d.P k (p.γ old)) mesh x = label ∧
          |inner ℝ normal ((6 * p.κ)⁻¹ • p.normalizedVelocity old x - center)| ≤ radius} ∩
            stage.current) := by
        apply measure_mono
        rintro x ⟨hx, hcode, hst⟩
        obtain ⟨h1, h2, h3⟩ := hpt x hx
        refine ⟨⟨?_, hstrip x ?_⟩, hx.1⟩
        · rw [← h1]; exact hcode
        · have hst' : |inner ℝ n (modelPlanar pm (τ x).1) - t| ≤ w := hst
          rwa [h2, h3] at hst'
    _ = ((ν.prod volume).restrict stage.current)
        {x | clockParentCode p old (d.P k (p.γ old)) mesh x = label ∧
          |inner ℝ normal ((6 * p.κ)⁻¹ • p.normalizedVelocity old x - center)| ≤ radius} :=
        (Measure.restrict_apply' hcur).symm
    _ ≤ ratio * ((ν.prod volume).restrict stage.current)
        (clockParentCode p old (d.P k (p.γ old)) mesh ⁻¹' {label}) :=
        stage.breadth label normal center hnormal
    _ = ratio * (ν.prod volume) (clockParentCode p old (d.P k (p.γ old)) mesh ⁻¹' {label} ∩
        stage.current) := by rw [Measure.restrict_apply' hcur]
    _ ≤ ratio * (ν.prod volume) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label})) := by
        refine mul_le_mul' le_rfl ?_
        calc (ν.prod volume) (clockParentCode p old (d.P k (p.γ old)) mesh ⁻¹' {label} ∩
              stage.current)
            ≤ (ν.prod volume) ((E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label})) ∪
                (stage.current \ E)) := by
              apply measure_mono
              rintro x ⟨hcode, hx⟩
              by_cases hxE : x ∈ E
              · left
                refine ⟨hxE, ?_⟩
                change modelCode pm mesh mesh (τ x) ∈ ({label} : Set (Fin 4 → ℤ))
                rw [(hpt x hxE).1]
                exact hcode
              · right
                exact ⟨hx, hxE⟩
          _ ≤ (ν.prod volume) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label})) +
                (ν.prod volume) (stage.current \ E) := measure_union_le _ _
          _ = (ν.prod volume) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label})) := by
              rw [stagePositive_null hp old stage, add_zero]

/-- The selected positive stage events lie in the unit clock window, so they
have finite mass under the full old prior. -/
theorem selected_stage_finite (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old) {J : Set Ev} (hJ : J ⊆ stage.earlier) :
    (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
      ((hp.frozenPacket old).selectedEvent J) ≠ ⊤ := by
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN0 : 0 < d.N k := by linarith [hd.1 k]
  have : IsProbabilityMeasure ((hp.frozenPacket old).prior (d.ν k (p.γ old))) :=
    hp.frozenPacket_prior_probability hN0 old
  apply ne_top_of_le_ne_top _ (measure_mono ((hp.frozenPacket old).event_unit_time.trans' 
    ((hp.frozenPacket old).selectedEvent_subset (hJ.trans hF))))
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [Real.volume_Icc])

/-- **Per-cell velocity breadth** of the clock model on the positive selected
stage events, in the form consumed by `model_velocity_rows`. -/
theorem stage_model_breadth (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old) (hK : 0 < K) (hfraction : 0 ≤ fraction)
    {w baseRho : ℝ} (hbaseRho : 0 ≤ baseRho) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (d.K k + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius) :
    ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      (1 - 8 * fraction / parentRenewalFloor K R) *
          (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            ((hp.frozenPacket old).selectedEvent (stagePositive hp old stage) ∩
              modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
                (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label}) ≤
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
          ((hp.frozenPacket old).selectedEvent (stagePositive hp old stage) ∩
            modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
              (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label} ∩
            {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 ((clockModel hp old hd stage.earlier
              stage.earlier_measurable hF).velocity z.1) : EuclideanSpace ℝ (Fin 3)) (V : Set _)}) := by
  set pm := clockModel hp old hd stage.earlier stage.earlier_measurable hF
  set mesh := precision * (2 : ℝ) ^ steps
  set E := stagePositive hp old stage
  set cur := (hp.frozenPacket old).selectedEvent E
  set μ0 : Measure Ev := ((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod (volume : Measure ℝ)
  set ratio := (ENNReal.ofReal (parentRenewalFloor K R))⁻¹ * ENNReal.ofReal (8 * fraction)
  have hE : MeasurableSet E := measurable_stagePositive hp old stage
  have hcur : MeasurableSet cur := (hp.frozenPacket old).measurable_selectedEvent hE
  have hcurfin : μ0 cur ≠ ⊤ :=
    selected_stage_finite hp old hd stage hF ((stagePositive_subset hp old stage).trans
      stage.current_subset)
  have : IsFiniteMeasure (μ0.restrict cur) := isFiniteMeasure_restrict.mpr hcurfin
  have hreal (X : Set Ev) (hX : X ⊆ cur) : (μ0.restrict cur).real X = μ0.real X := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply' hcur, inter_eq_left.mpr hX]
  have hfloor := parentRenewalFloor_pos hK R
  have hratio : ratio ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hfloor).ne')
      ENNReal.ofReal_ne_top
  have hratioReal : ratio.toReal = 8 * fraction / parentRenewalFloor K R := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hfloor.le,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hvel : ∀ z ∈ cur, ‖modelPlanar pm z.1‖ ≤ d.K k := by
    rintro z ⟨x, hx, rfl⟩
    have hG : x.1 ∈ clockGood old := stage.clock_good hx.1
    rw [clock_timeChange hp old x, clockModel_planar hp old hd _ _ hF hG]
    exact hG.2
  have hstrip : ∀ label (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      (μ0.restrict cur).real (cur ∩ modelCode pm mesh mesh ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w}) ≤
        8 * fraction / parentRenewalFloor K R *
          (μ0.restrict cur).real (cur ∩ modelCode pm mesh mesh ⁻¹' {label}) := by
    intro label n t hn
    rw [hreal _ (inter_subset_left.trans inter_subset_left), hreal _ inter_subset_left]
    have hw : 0 ≤ w := le_trans (by have := hd.2.2.1.1 k; positivity) hwRho
    have hcap := stage_model_strip hp old hd stage hF hw hwRadius label n t hn
    have hfinA : μ0 (cur ∩ modelCode pm mesh mesh ⁻¹' {label}) ≠ ⊤ :=
      ne_top_of_le_ne_top hcurfin (measure_mono inter_subset_left)
    calc μ0.real (cur ∩ modelCode pm mesh mesh ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w})
        ≤ (ratio * μ0 (cur ∩ modelCode pm mesh mesh ⁻¹' {label})).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hratio hfinA) hcap
      _ = _ := by rw [ENNReal.toReal_mul, hratioReal]; rfl
  have hmeas : ∀ label (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
      MeasurableSet (cur ∩ modelCode pm mesh mesh ⁻¹' {label} ∩
        {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) :
          EuclideanSpace ℝ (Fin 3)) (W : Set _)}) := by
    intro label W
    refine (hcur.inter (measurable_modelCode pm mesh mesh (measurableSet_singleton label))).inter ?_
    exact measurableSet_le measurable_const
      ((Metric.continuous_infDist_pt _).measurable.comp
        ((measurable_modelVelocity pm).comp measurable_fst))
  intro label V hV
  have h := model_breadth_of_strip pm (μ0.restrict cur) cur (modelCode pm mesh mesh)
    (by have := hd.2.2.1.1 k; linarith) hbaseRho hwRho hbaseRho4 hvel hstrip hmeas label V hV
  rwa [hreal _ inter_subset_left, hreal _ (inter_subset_left.trans inter_subset_left)] at h

/-- **Physical velocity rows on the actual safe clock model of an old
packet, from one actual clock stage.**

The model is `clockModel` over the stage's earlier source: the literal
clock coefficients of the old packet (signal `2^T P`, i.e. `P/h`, unsheared
old base, original planar velocity), jets bounded by `24 K_k`, the exact
full old assignment prior (`clockModel_prior`). The rows live on the fine
physical codes at the stage mesh `mesh n = precision 2^steps`, which are
the stage's clock parent codes (`clockModel_code_eq`). All inputs of
`model_velocity_rows` come from the stage: durations from its coarse clock
durations, the hereditary count from its earlier floors and the band cap
`hband`, breadth from its normalized strip caps through the old frame
(`w N^(2δ₀L) ≤ 6 radius`), the coarse code set from its finite active
codes; the scale relations from one smallness condition on `mesh n`. -/
theorem stage_velocity_rows (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old)
    (n : ℕ) (hmesh : precision * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hK : 0 < K) (hcensus : 0 < census) (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    (hfraction : 0 ≤ fraction)
    {Cband : ℝ} (hCband : 0 ≤ Cband)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
        {x | unshearedPacketBase p old x ∈ U ∧
          |clockParentSignal p old (d.P k (p.γ old)) x - c (unshearedPacketBase p old x)| ≤
            coarse} ≤
      ENNReal.ofReal (Cband * (δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹) ^
          (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * volume U)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 144 * d.K k ≤ Kg) (hKgRate : (parentClockDurationRate K)⁻¹ ≤ Kg)
    (hKgCount : 8 * Cband / parentClockCellRate K census ((2 : ℝ) ^ steps) ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (d.K k + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction)
    (hgfrac : gfraction < 1 - 8 * fraction / parentRenewalFloor K R) (hε : 0 < ε)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * ε ^ 4 / (256 * curvatureRowConstant ^ 3 * Kg ^ 9 + 1)))) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set Ev),
      Measurable row ∧ MeasurableSet retained ∧
      retained ⊆ (hp.frozenPacket old).selectedEvent stage.current ∧
      (∀ a j, |row a j| ≤ 28 * Kg ^ 6) ∧
      (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
          ((hp.frozenPacket old).selectedEvent stage.current) ≤
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real retained +
          ε * (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            (clockModel hp old hd stage.earlier stage.earlier_measurable hF).event +
          gfraction * (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            ((hp.frozenPacket old).selectedEvent stage.current) ∧
      ∀ z ∈ retained,
        |((clockModel hp old hd stage.earlier stage.earlier_measurable hF).signal
            z.1).derivative.eval z.2 -
          ∑ j, row (modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
              (Submission.Lib.K4DyadicRowScales.mesh n)
              (Submission.Lib.K4DyadicRowScales.mesh n) z) j *
            (clockModel hp old hd stage.earlier stage.earlier_measurable hF).velocity z.1 j| ≤
          80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  classical
  set pm := clockModel hp old hd stage.earlier stage.earlier_measurable hF with hpm
  set mesh := Submission.Lib.K4DyadicRowScales.mesh n with hmeshdef
  set E := stagePositive hp old stage with hEdef
  set ν' := (hp.frozenPacket old).prior (d.ν k (p.γ old)) with hν'
  set cur := (hp.frozenPacket old).selectedEvent E with hcurdef
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN0 : 0 < d.N k := by linarith [hd.1 k]
  have hK1 : 1 ≤ d.K k := hd.2.2.1.1 k
  have hKg1 : 1 ≤ Kg := by linarith
  have : IsProbabilityMeasure ν' := hp.frozenPacket_prior_probability hN0 old
  have hmesh0 : 0 < mesh := Submission.Lib.K4DyadicRowScales.mesh_pos n
  have hmesh1 : mesh ≤ 1 := (Submission.Lib.K4DyadicRowScales.mesh_le_coarse n).trans
    (Submission.Lib.K4DyadicRowScales.coarse_le_one n)
  have hE : MeasurableSet E := measurable_stagePositive hp old stage
  have hEF : E ⊆ p.F old := fun x hx => hF (stage.current_subset hx.1)
  have hcur : MeasurableSet cur := (hp.frozenPacket old).measurable_selectedEvent hE
  have hcurE : cur ⊆ pm.event := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, ⟨stage.current_subset hx.1, stage.clock_good hx.1⟩, rfl⟩
  have hcurSub : cur ⊆ (hp.frozenPacket old).selectedEvent stage.current :=
    image_mono (stagePositive_subset hp old stage)
  have hcoarseEq : coarse = mesh * (2 : ℝ) ^ n := by
    rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_eq_mesh_mul_pow n
  have hshape : coarse = mesh ^ ((2 : ℝ) / 3) := by
    rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_eq_mesh_rpow n
  have hP := (ParentSignal.original_parent_bounds (show ParentSource.pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  have hjets : ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ 24 * d.K k ∧
      |pm.scalarCoefficients l 2| ≤ 24 * d.K k ∧ |pm.scalarCoefficients l 4| ≤ 24 * d.K k ∧
        |pm.scalarCoefficients l 6| ≤ 24 * d.K k := fun l _ =>
    ParentSignal.safeClockCoefficients_jets hP p old (hp.2.2.2.2.2.2.2 old).2.1
      (by linarith) l
  obtain ⟨hquad, hdir, hsmall', hbudget⟩ := graph_scale_relations (K := Kg) (d := dimension)
    (fraction := gfraction) (ε := ε) (C := curvatureRowConstant) (hidden := mesh) hKg1 hdim0
    hdim1 hgfraction hε curvatureRowConstant_pos hmesh0 hmesh1 hsmall
  rw [← hshape] at hquad hdir
  have hfin := stage.finite
  let C : Finset (Fin 4 → ℤ) := hfin.toFinset.image (coarsenPhysicalCode n n)
  have hC : ∀ z ∈ cur, modelCode pm coarse coarse z ∈ C := by
    rintro z ⟨x, hx, rfl⟩
    have hcc : modelCode pm coarse coarse ((hp.frozenPacket old).timeChange x) =
        coarsenPhysicalCode n n
          (modelCode pm mesh mesh ((hp.frozenPacket old).timeChange x)) :=
      coefficientGridCode_coarse_eq_coarsen (modelCoefficients pm) n n hcoarseEq hcoarseEq _
    rw [hcc, clockModel_code_eq hp old hd _ _ hF (hEF hx) (stage.clock_good hx.1) mesh]
    apply Finset.mem_image_of_mem
    rw [Set.Finite.mem_toFinset, ← hmesh]
    exact hx.2
  have hcount : ∀ q ∈ C, ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ Kg * (coarse / mesh) ^ 3 * (coarse / mesh) ^ dimension ∧
      ∀ z ∈ cur, modelCode pm coarse coarse z = q → modelCode pm mesh mesh z ∈ S :=
    fun q _ => stage_model_count hp old hd stage hF n hmesh hcoarse hK hcensus hdim0 hCband
      hKg1 hKgCount hband q
  have hlong : ∀ z ∈ cur, ENNReal.ofReal (parentClockDurationRate K * coarse) ≤
      incidenceDuration (pm.event ∩ modelCode pm coarse coarse ⁻¹'
        {modelCode pm coarse coarse z}) z.1 :=
    fun z hz => stage_model_durations hp old hd stage hF z (hcurSub hz)
  have hbroad := stage_model_breadth hp old hd stage hF hK hfraction hbaseRho hbaseRho4 hwRho
    hwRadius
  rw [hmesh] at hbroad
  obtain ⟨row, retained, hrow, hret, hsub, hbound, hloss, hfit⟩ :=
    model_velocity_rows pm (H := 24 * d.K k) (by linarith) hjets ν' pm.event cur
      pm.measurable_event subset_rfl hcur hcurE n n hcoarseEq hcoarseEq
      (K := Kg) (lossRate := parentClockDurationRate K)
      (liftRho := mesh ^ ((1 - dimension) / 24)) (baseRho := baseRho)
      (fraction := gfraction) (baseFraction := 1 - 8 * fraction / parentRenewalFloor K R)
      (dimension := dimension) (ε := ε) (by linarith) hmesh0 le_rfl hshape
      (parentClockDurationRate_pos hK) hKgRate (Real.rpow_pos_of_pos hmesh0 _) hbaseRho
      hgfraction hgfrac hε.le hquad hdir hcond hsmall' hbudget C hC hcount hlong hbroad
  -- the removed original null set does not change the selected mass
  have hnull : (ν'.prod volume) ((hp.frozenPacket old).selectedEvent stage.current \ cur) = 0 := by
    have hsubset : (hp.frozenPacket old).selectedEvent stage.current \ cur ⊆
        (hp.frozenPacket old).selectedEvent (stage.current \ E) := by
      rintro z ⟨⟨x, hx, rfl⟩, hzn⟩
      exact ⟨x, ⟨hx, fun hxE => hzn ⟨x, hxE, rfl⟩⟩, rfl⟩
    apply measure_mono_null hsubset
    have h := selected_prod_apply hp old hd (J := stage.current \ E)
      (stage.current_measurable.diff hE) (fun x hx => hF (stage.current_subset hx.1))
      MeasurableSet.univ
    rw [inter_univ] at h
    rw [h, preimage_univ, inter_univ, stagePositive_null hp old stage, mul_zero]
  have hmass : (ν'.prod volume).real ((hp.frozenPacket old).selectedEvent stage.current) =
      (ν'.prod volume).real cur := by
    have hle : (ν'.prod volume) ((hp.frozenPacket old).selectedEvent stage.current) ≤
        (ν'.prod volume) cur := by
      calc (ν'.prod volume) ((hp.frozenPacket old).selectedEvent stage.current)
          ≤ (ν'.prod volume) (cur ∪ ((hp.frozenPacket old).selectedEvent stage.current \ cur)) :=
            measure_mono (fun z hz => by
              by_cases hzc : z ∈ cur
              · exact Or.inl hzc
              · exact Or.inr ⟨hz, hzc⟩)
        _ ≤ (ν'.prod volume) cur +
            (ν'.prod volume) ((hp.frozenPacket old).selectedEvent stage.current \ cur) :=
            measure_union_le _ _
        _ = (ν'.prod volume) cur := by rw [hnull, add_zero]
    rw [measureReal_def, measureReal_def, le_antisymm hle (measure_mono hcurSub)]
  refine ⟨row, retained, hrow, hret, hsub.trans hcurSub, hbound, ?_, hfit⟩
  rw [hmass]
  exact hloss

/-- `stage_velocity_rows` with the band cap supplied by the original moving
band cap of the prepared path (`clock_band_of_moving_band`): the count
constant is `8 · 64 max(κ,K)² κ 4^dim N^(2 error + τ + 2δ₀L + ε) / rate`. -/
theorem stage_velocity_rows_of_moving_band {T : Type*} {H : Fin (d.W k) → Set Ev} {u : T → ℝ}
    {τ εpure : ℝ} (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling εpure)
    (hd : d.Valid)
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source) (hF : stage.earlier ⊆ p.F old)
    (hEE : stage.earlier ⊆ d.E k (p.γ old)) (hEbase : stage.earlier ⊆ Q.base (p.γ old))
    (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    {f₀ error : ℝ} (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ error)
    (hresolved : d.N k ^ (-(d.L - p.r (p.lev old))) ≤
      4 * (coarse / (δ (d.N k) (p.r (p.lev old)) / ((2 : ℝ) ^ p.T (p.lev old))⁻¹)))
    (n : ℕ) (hmesh : precision * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hK : 0 < K) (hcensus : 0 < census) (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    (hfraction : 0 ≤ fraction)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 144 * d.K k ≤ Kg) (hKgRate : (parentClockDurationRate K)⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
        d.N k ^ (2 * error + (τ + 2 * δ₀ * d.L) + εpure)) /
          parentClockCellRate K census ((2 : ℝ) ^ steps) ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (d.K k + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction)
    (hgfrac : gfraction < 1 - 8 * fraction / parentRenewalFloor K R) (hε : 0 < ε)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * ε ^ 4 / (256 * curvatureRowConstant ^ 3 * Kg ^ 9 + 1)))) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set Ev),
      Measurable row ∧ MeasurableSet retained ∧
      retained ⊆ (hp.frozenPacket old).selectedEvent stage.current ∧
      (∀ a j, |row a j| ≤ 28 * Kg ^ 6) ∧
      (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
          ((hp.frozenPacket old).selectedEvent stage.current) ≤
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real retained +
          ε * (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            (clockModel hp old hd stage.earlier stage.earlier_measurable hF).event +
          gfraction * (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            ((hp.frozenPacket old).selectedEvent stage.current) ∧
      ∀ z ∈ retained,
        |((clockModel hp old hd stage.earlier stage.earlier_measurable hF).signal
            z.1).derivative.eval z.2 -
          ∑ j, row (modelCode (clockModel hp old hd stage.earlier stage.earlier_measurable hF)
              (Submission.Lib.K4DyadicRowScales.mesh n)
              (Submission.Lib.K4DyadicRowScales.mesh n) z) j *
            (clockModel hp old hd stage.earlier stage.earlier_measurable hF).velocity z.1 j| ≤
          80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  have hcoarse0 : 0 < coarse := hcoarse ▸ Submission.Lib.K4DyadicRowScales.coarse_pos n
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hN0 : 0 < d.N k := by linarith [hd.1 k]
  exact stage_velocity_rows hp old hd stage hF n hmesh hcoarse hK hcensus hdim0 hdim1 hfraction
    (by positivity)
    (clock_band_of_moving_band hp old Q hpure hd hr hrL stage.earlier stage.earlier_measurable
      hEE hEbase hF hdim0 hprofile hcoarse0 hresolved)
    hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction hgfrac hε hsmall

end Stage

end Clock

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
