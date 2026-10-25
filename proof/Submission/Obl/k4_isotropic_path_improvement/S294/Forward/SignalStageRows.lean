-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.SignalStageRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Generalizes, from the physical parent `d.P` to an arbitrary signal polynomial `X` on a set of
-- good lines, the clock stages and rows of this obligation's port of o287
-- (Parent/ParentSource/Broad/Source/DenseRootClockStages.lean: x1046 of o265; Parent/Graph/
-- ClockStageRows.lean: x1037 of o287); adapted by x1082 for the relative row packet.
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.SignalModel

/-!
# Physical velocity rows for an arbitrary signal

`SignalClockStage`: the data of an `OriginalParentClockStage` (earlier and current sources,
earlier floors on the clock code at the stage mesh, coarse clock durations, per-code breadth of
the normalized velocity) for an arbitrary signal polynomial `X` on good lines, with the floor
rate, duration rate and breadth ratio as parameters. `signal_stage_velocity_rows` is
`Graph.stage_velocity_rows` for such a stage: rows on the clock codes of `X` at the stage mesh with
`|(signal)'(t) - Σ row_j (1, V)_j| ≤ 80 Kg⁷ mesh^((1-dim)/24)` on a retained part of the current
events, where the signal of the model is `2^T X` (so its derivative is the original rate of `X`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native ParentSource.Broad.Source
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

/-- A clock stage of an old packet for the signal `X` on the good lines `good`. -/
structure SignalClockStage
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) (X : Po) (good : Set Ln) (θ dimension precision coarse radius : ℝ)
    (steps : ℕ) (cellRate durationRate ratio : ℝ) (source : Set Ev) where
  earlier : Set Ev
  current : Set Ev
  earlier_measurable : MeasurableSet earlier
  current_measurable : MeasurableSet current
  current_subset : current ⊆ earlier
  earlier_subset : earlier ⊆ source
  good_lines : current ⊆ Prod.fst ⁻¹' good
  finite : (activeCodes (((d.ν k (p.γ old)).prod volume).restrict earlier)
    (clockParentCode p old X (precision * (2 : ℝ) ^ steps))).Finite
  earlier_floor : ∀ q,
    (((d.ν k (p.γ old)).prod volume).restrict earlier)
      (clockParentCode p old X (precision * (2 : ℝ) ^ steps) ⁻¹' {q}) = 0 ∨
    ENNReal.ofReal (cellRate * θ ^ (-dimension) *
      (precision * (2 : ℝ) ^ steps) ^ ((3 : ℝ) + dimension)) *
      (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) ≤
    (((d.ν k (p.γ old)).prod volume).restrict earlier)
      (clockParentCode p old X (precision * (2 : ℝ) ^ steps) ⁻¹' {q})
  durations : ∀ z ∈ (hp.frozenPacket old).assignedSelectedEvent current,
    ENNReal.ofReal (durationRate * coarse) ≤ incidenceDuration
      (hp.assignedClockCellSource old X earlier coarse
        (hp.assignedClockCode old X coarse z)) z.1
  breadth : ∀ label (n center : P2), ‖n‖ = 1 →
    (((d.ν k (p.γ old)).prod volume).restrict current)
      {z | clockParentCode p old X (precision * (2 : ℝ) ^ steps) z = label ∧
        |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity old z - center)| ≤ radius} ≤
      ENNReal.ofReal ratio *
        (((d.ν k (p.γ old)).prod volume).restrict current)
          (clockParentCode p old X (precision * (2 : ℝ) ^ steps) ⁻¹' {label})

section Stage

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) (X : Po) (good : Set Ln) {B : ℝ}
    (hgood : MeasurableSet good) (hB : 0 ≤ B)
    (hcoef : ∀ l ∈ good, l ∈ p.A old → ∀ i, |ParentSignal.clockPacketCoefficients X p old l i| ≤ B)
variable {θ dimension precision coarse radius : ℝ} {steps : ℕ} {cellRate durationRate ratio : ℝ}
    {source : Set Ev}

/-- The stage's current incidences in cells of positive earlier original mass
(at the stage mesh); an original null set is removed. -/
def stagePositive
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) : Set Ev :=
  stage.current ∩ clockParentCode p old X (precision * (2 : ℝ) ^ steps) ⁻¹'
    activeCodes (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
      (clockParentCode p old X (precision * (2 : ℝ) ^ steps))

theorem measurable_stagePositive
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) : MeasurableSet (stagePositive hp old X good stage) :=
  stage.current_measurable.inter
    ((measurable_clockParentCode p old _ _) (Set.to_countable _).measurableSet)

theorem stagePositive_subset
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) : stagePositive hp old X good stage ⊆ stage.current := inter_subset_left

theorem stagePositive_null
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) :
    ((d.ν k (p.γ old)).prod volume) (stage.current \ stagePositive hp old X good stage) = 0 := by
  set code := clockParentCode p old X (precision * (2 : ℝ) ^ steps)
  set μE := ((d.ν k (p.γ old)).prod volume).restrict stage.earlier
  have hsub : stage.current \ stagePositive hp old X good stage ⊆
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
theorem stage_model_durations (_hd : d.Valid)
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old) :
    ∀ z ∈ (hp.frozenPacket old).selectedEvent stage.current,
      ENNReal.ofReal (durationRate * coarse) ≤
        incidenceDuration ((signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF).event ∩
          modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF) coarse coarse ⁻¹'
            {modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
              coarse coarse z}) z.1 := by
  rintro z ⟨x, hx, rfl⟩
  have hxF : x ∈ p.F old := hF (stage.current_subset hx)
  have hA : x.1 ∈ (hp.frozenPacket old).assigned :=
    ((hp.frozenPacket old).counted_inside_original hxF).2.1
  have hG : x.1 ∈ good := stage.good_lines hx
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
  · change y.1 ∈ good
    rw [hy1]
    exact hG
  · simp only [mem_preimage, mem_singleton_iff]
    rw [← signalModel_assignedCode hp old X good hgood hB hcoef _ _ hF hA hG coarse t,
      ← signalModel_assignedCode hp old X good hgood hB hcoef _ _ hF hA hG coarse (packetTime p old x)]
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
theorem stage_model_count (hd : d.Valid) (hX : X.totalDegree ≤ 2)
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old)
    (n : ℕ) (hmesh : precision * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hθ : 0 < θ) (hcell : 0 < cellRate) (hdim : 0 ≤ dimension)
    {Cband Kc : ℝ} (hCband : 0 ≤ Cband) (hKc1 : 1 ≤ Kc)
    (hKc : 8 * Cband / cellRate ≤ Kc)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
        {x | unshearedPacketBase p old x ∈ U ∧
          |clockParentSignal p old X x - c (unshearedPacketBase p old x)| ≤
            coarse} ≤
      ENNReal.ofReal (Cband * θ ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * volume U)
    (q : Fin 4 → ℤ) :
    ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ Kc * (coarse / Submission.Lib.K4DyadicRowScales.mesh n) ^ 3 *
        (coarse / Submission.Lib.K4DyadicRowScales.mesh n) ^ dimension ∧
      ∀ z ∈ (hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage),
        modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF) coarse coarse z =
            q →
          modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
            (Submission.Lib.K4DyadicRowScales.mesh n) (Submission.Lib.K4DyadicRowScales.mesh n) z ∈
              S := by
  classical
  set mesh := Submission.Lib.K4DyadicRowScales.mesh n with hmeshdef


  set reference := d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)
  set μ := ((d.ν k (p.γ old)).prod volume).restrict stage.earlier
  have : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hmesh0 : 0 < mesh := Submission.Lib.K4DyadicRowScales.mesh_pos n
  have hcoarse0 : 0 < coarse := hcoarse ▸ Submission.Lib.K4DyadicRowScales.coarse_pos n
  have hrate : 0 < cellRate := hcell
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
  have hgrid (b : ℝ) (x : Ev) : clockParentCode p old X b x =
      flattenClockCode (gridCode (fun z j => unshearedPacketBase p old z j)
        (clockParentSignal p old X) b b x) := clockParentCode_eq_product p old X b x
  let gm := gridCode (fun x j => unshearedPacketBase p old x j) (clockParentSignal p old X)
    mesh mesh
  have hFloor : ∀ x ∈ stagePositive hp old X good stage,
      ENNReal.ofReal (cellRate * θ ^ (-dimension) * mesh ^ 3 * mesh ^ dimension) * reference ≤
        μ (gm ⁻¹' {gm x}) := by
    intro x hx
    have hact := hx.2
    have hcell : clockParentCode p old X mesh ⁻¹' {clockParentCode p old X mesh x} =
        gm ⁻¹' {gm x} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, hgrid]
      exact flattenClockCode_injective.eq_iff
    rcases stage.earlier_floor (clockParentCode p old X (precision * (2 : ℝ) ^ steps) x) with h0 | h1
    · exact absurd h0 (by rw [hmesh] at hact ⊢; exact hact)
    · rw [hmesh, hcell] at h1
      have hpow : mesh ^ ((3 : ℝ) + dimension) = mesh ^ 3 * mesh ^ dimension := by
        rw [Real.rpow_add hmesh0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have heq : cellRate * θ ^ (-dimension) * mesh ^ 3 * mesh ^ dimension =
          cellRate * θ ^ (-dimension) * mesh ^ ((3 : ℝ) + dimension) := by
        rw [hpow]; ring
      rw [heq]
      exact h1
  obtain ⟨F, hFcard, hFmem, -⟩ := HereditaryClockSupport.exists_hereditary_support μ
    (unshearedPacketBase p old) (measurable_unshearedPacketBase p old)
    (clockParentSignal p old X) (measurable_clockParentSignal (d.N k) p old X)
    (stagePositive hp old X good stage) reference href hreftop hmesh0 hmesh0 hcoarse0 hθ hrate hCband
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
  have hmem : ∀ z ∈ (hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage),
      modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF) coarse coarse z =
          q →
        modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
          mesh mesh z ∈ S0 := by
    rintro z ⟨x, hx, rfl⟩ hq
    have hxF : x ∈ p.F old := hF (stage.current_subset hx.1)
    have hG : x.1 ∈ good := stage.good_lines hx.1
    rw [signalModel_code_eq hp old X good hgood hB hcoef hX _ _ hF hxF hG, hgrid] at hq ⊢
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
theorem stage_model_strip (hd : d.Valid) (hX : X.totalDegree ≤ 2)
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old)
    {w : ℝ} (hw : 0 ≤ w) (hscale : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (label : Fin 4 → ℤ) (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (hn : ‖n‖ = 1) :
    (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
        ((hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage) ∩
          modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
            (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF) z.1) - t| ≤ w}) ≤
      (ENNReal.ofReal ratio) *
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume)
          ((hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage) ∩
            modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
              (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label}) := by
  set pm := signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF
  set mesh := precision * (2 : ℝ) ^ steps
  set E := stagePositive hp old X good stage
  set τ := (hp.frozenPacket old).timeChange
  set ν := d.ν k (p.γ old)
  set ratioE := ENNReal.ofReal ratio
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  obtain ⟨normal, center, hnormal, hstrip⟩ :=
    original_strip_normalized hp old hN hw hscale n t hn
  have hE : MeasurableSet E := measurable_stagePositive hp old X good stage
  have hEF : E ⊆ p.F old := fun x hx => hF (stage.current_subset hx.1)
  have hcodem : MeasurableSet (modelCode pm mesh mesh ⁻¹' {label}) :=
    measurable_modelCode pm mesh mesh (measurableSet_singleton label)
  have hstripm : MeasurableSet {z : Ev | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w} := by
    apply measurableSet_le _ measurable_const
    exact ((measurable_const.inner ((measurable_modelPlanar pm).comp measurable_fst)).sub
      measurable_const).abs
  have hpt (x : Ev) (hx : x ∈ E) : modelCode pm mesh mesh (τ x) =
      clockParentCode p old X mesh x ∧ (τ x).1 = x.1 ∧
        modelPlanar pm x.1 = v x.1 :=
    ⟨signalModel_code_eq hp old X good hgood hB hcoef hX _ _ hF (hEF hx) (stage.good_lines hx.1) mesh,
      by rw [clock_timeChange hp old x],
      signalModel_planar hp old X good hgood hB hcoef _ _ hF (stage.good_lines hx.1)⟩
  rw [inter_assoc, selected_prod_apply hp old hd hE hEF (hcodem.inter hstripm),
    selected_prod_apply hp old hd hE hEF hcodem, mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  have hcur := stage.current_measurable
  calc ((ν.prod volume)) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label} ∩
        {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w}))
      ≤ (ν.prod volume) ({x | clockParentCode p old X mesh x = label ∧
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
        {x | clockParentCode p old X mesh x = label ∧
          |inner ℝ normal ((6 * p.κ)⁻¹ • p.normalizedVelocity old x - center)| ≤ radius} :=
        (Measure.restrict_apply' hcur).symm
    _ ≤ ratioE * ((ν.prod volume).restrict stage.current)
        (clockParentCode p old X mesh ⁻¹' {label}) :=
        stage.breadth label normal center hnormal
    _ = ratioE * (ν.prod volume) (clockParentCode p old X mesh ⁻¹' {label} ∩
        stage.current) := by rw [Measure.restrict_apply' hcur]
    _ ≤ ratioE * (ν.prod volume) (E ∩ τ ⁻¹' (modelCode pm mesh mesh ⁻¹' {label})) := by
        refine mul_le_mul' le_rfl ?_
        calc (ν.prod volume) (clockParentCode p old X mesh ⁻¹' {label} ∩
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
              rw [stagePositive_null hp old X good stage, add_zero]

/-- The selected positive stage events lie in the unit clock window, so they
have finite mass under the full old prior. -/
theorem selected_stage_finite (hd : d.Valid)
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old) {J : Set Ev} (hJ : J ⊆ stage.earlier) :
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
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old) (hX : X.totalDegree ≤ 2) (hratio0 : 0 ≤ ratio)
    {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (hvelGood : ∀ l ∈ good, ‖v l‖ ≤ Vmax)
    {w baseRho : ℝ} (hbaseRho : 0 ≤ baseRho) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius) :
    ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      (1 - ratio) *
          (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            ((hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage) ∩
              modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
                (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label}) ≤
        (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
          ((hp.frozenPacket old).selectedEvent (stagePositive hp old X good stage) ∩
            modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
              (precision * (2 : ℝ) ^ steps) (precision * (2 : ℝ) ^ steps) ⁻¹' {label} ∩
            {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 ((signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF).velocity z.1) : EuclideanSpace ℝ (Fin 3)) (V : Set _)}) := by
  set pm := signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF
  set mesh := precision * (2 : ℝ) ^ steps
  set E := stagePositive hp old X good stage
  set cur := (hp.frozenPacket old).selectedEvent E
  set μ0 : Measure Ev := ((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod (volume : Measure ℝ)
  set ratioE := ENNReal.ofReal ratio
  have hE : MeasurableSet E := measurable_stagePositive hp old X good stage
  have hcur : MeasurableSet cur := (hp.frozenPacket old).measurable_selectedEvent hE
  have hcurfin : μ0 cur ≠ ⊤ :=
    selected_stage_finite hp old X good hd stage hF ((stagePositive_subset hp old X good stage).trans
      stage.current_subset)
  have : IsFiniteMeasure (μ0.restrict cur) := isFiniteMeasure_restrict.mpr hcurfin
  have hreal (X : Set Ev) (hX : X ⊆ cur) : (μ0.restrict cur).real X = μ0.real X := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply' hcur, inter_eq_left.mpr hX]
  have hratio : ratioE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hratioReal : ratioE.toReal = ratio := ENNReal.toReal_ofReal hratio0
  have hvel : ∀ z ∈ cur, ‖modelPlanar pm z.1‖ ≤ Vmax := by
    rintro z ⟨x, hx, rfl⟩
    have hG : x.1 ∈ good := stage.good_lines hx.1
    rw [clock_timeChange hp old x, signalModel_planar hp old X good hgood hB hcoef _ _ hF hG]
    exact hvelGood x.1 hG
  have hstrip : ∀ label (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      (μ0.restrict cur).real (cur ∩ modelCode pm mesh mesh ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w}) ≤
        ratio *
          (μ0.restrict cur).real (cur ∩ modelCode pm mesh mesh ⁻¹' {label}) := by
    intro label n t hn
    rw [hreal _ (inter_subset_left.trans inter_subset_left), hreal _ inter_subset_left]
    have hw : 0 ≤ w := le_trans (by positivity) hwRho
    have hcap := stage_model_strip hp old X good hgood hB hcoef hd hX stage hF hw hwRadius label n t hn
    have hfinA : μ0 (cur ∩ modelCode pm mesh mesh ⁻¹' {label}) ≠ ⊤ :=
      ne_top_of_le_ne_top hcurfin (measure_mono inter_subset_left)
    calc μ0.real (cur ∩ modelCode pm mesh mesh ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w})
        ≤ (ratioE * μ0 (cur ∩ modelCode pm mesh mesh ⁻¹' {label})).toReal :=
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
    hV0 hbaseRho hwRho hbaseRho4 hvel hstrip hmeas label V hV
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
theorem signal_stage_velocity_rows (hd : d.Valid)
    (stage : SignalClockStage hp old X good θ dimension precision coarse radius steps cellRate durationRate ratio source) (hF : stage.earlier ⊆ p.F old)
    (n : ℕ) (hmesh : precision * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hX : X.totalDegree ≤ 2) (hθ : 0 < θ) (hcell : 0 < cellRate) (hdur : 0 < durationRate)
    (hratio0 : 0 ≤ ratio)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Hj Vmax : ℝ} (hHj : 1 ≤ Hj) (hV0 : 0 ≤ Vmax) (hvelGood : ∀ l ∈ good, ‖v l‖ ≤ Vmax)
    (hjetsGood : ∀ l ∈ good, |ParentSignal.clockPacketCoefficients X p old l 1| ≤ Hj ∧
      |ParentSignal.clockPacketCoefficients X p old l 2| ≤ Hj ∧
      |ParentSignal.clockPacketCoefficients X p old l 4| ≤ Hj ∧
      |ParentSignal.clockPacketCoefficients X p old l 6| ≤ Hj)
    {Cband : ℝ} (hCband : 0 ≤ Cband)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ old)).prod volume).restrict stage.earlier)
        {x | unshearedPacketBase p old x ∈ U ∧
          |clockParentSignal p old X x - c (unshearedPacketBase p old x)| ≤
            coarse} ≤
      ENNReal.ofReal (Cband * θ ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * volume U)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 6 * Hj ≤ Kg) (hKgRate : (durationRate)⁻¹ ≤ Kg)
    (hKgCount : 8 * Cband / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction)
    (hgfrac : gfraction < 1 - ratio) (hε : 0 < ε)
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
            (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF).event +
          gfraction * (((hp.frozenPacket old).prior (d.ν k (p.γ old))).prod volume).real
            ((hp.frozenPacket old).selectedEvent stage.current) ∧
      ∀ z ∈ retained,
        |((signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF).signal
            z.1).derivative.eval z.2 -
          ∑ j, row (modelCode (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF)
              (Submission.Lib.K4DyadicRowScales.mesh n)
              (Submission.Lib.K4DyadicRowScales.mesh n) z) j *
            (signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF).velocity z.1 j| ≤
          80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  classical
  set pm := signalModel hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF with hpm
  set mesh := Submission.Lib.K4DyadicRowScales.mesh n with hmeshdef
  set E := stagePositive hp old X good stage with hEdef
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
  have hE : MeasurableSet E := measurable_stagePositive hp old X good stage
  have hEF : E ⊆ p.F old := fun x hx => hF (stage.current_subset hx.1)
  have hcur : MeasurableSet cur := (hp.frozenPacket old).measurable_selectedEvent hE
  have hcurE : cur ⊆ pm.event := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, ⟨stage.current_subset hx.1, stage.good_lines hx.1⟩, rfl⟩
  have hcurSub : cur ⊆ (hp.frozenPacket old).selectedEvent stage.current :=
    image_mono (stagePositive_subset hp old X good stage)
  have hcoarseEq : coarse = mesh * (2 : ℝ) ^ n := by
    rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_eq_mesh_mul_pow n
  have hshape : coarse = mesh ^ ((2 : ℝ) / 3) := by
    rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_eq_mesh_rpow n
  have hjets : ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ Hj ∧
      |pm.scalarCoefficients l 2| ≤ Hj ∧ |pm.scalarCoefficients l 4| ≤ Hj ∧
        |pm.scalarCoefficients l 6| ≤ Hj :=
    signalModel_jets hp old X good hgood hB hcoef stage.earlier stage.earlier_measurable hF
      (by linarith) hjetsGood
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
    rw [hcc, signalModel_code_eq hp old X good hgood hB hcoef hX _ _ hF (hEF hx) (stage.good_lines hx.1) mesh]
    apply Finset.mem_image_of_mem
    rw [Set.Finite.mem_toFinset, ← hmesh]
    exact hx.2
  have hcount : ∀ q ∈ C, ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ Kg * (coarse / mesh) ^ 3 * (coarse / mesh) ^ dimension ∧
      ∀ z ∈ cur, modelCode pm coarse coarse z = q → modelCode pm mesh mesh z ∈ S :=
    fun q _ => stage_model_count hp old X good hgood hB hcoef hd hX stage hF n hmesh hcoarse hθ hcell hdim0 hCband
      hKg1 hKgCount hband q
  have hlong : ∀ z ∈ cur, ENNReal.ofReal (durationRate * coarse) ≤
      incidenceDuration (pm.event ∩ modelCode pm coarse coarse ⁻¹'
        {modelCode pm coarse coarse z}) z.1 :=
    fun z hz => stage_model_durations hp old X good hgood hB hcoef hd stage hF z (hcurSub hz)
  have hbroad := stage_model_breadth hp old X good hgood hB hcoef hd stage hF hX hratio0 hV0 hvelGood
    hbaseRho hbaseRho4 hwRho
    hwRadius
  rw [hmesh] at hbroad
  obtain ⟨row, retained, hrow, hret, hsub, hbound, hloss, hfit⟩ :=
    model_velocity_rows pm (H := Hj) hHj hjets ν' pm.event cur
      pm.measurable_event subset_rfl hcur hcurE n n hcoarseEq hcoarseEq
      (K := Kg) (lossRate := durationRate)
      (liftRho := mesh ^ ((1 - dimension) / 24)) (baseRho := baseRho)
      (fraction := gfraction) (baseFraction := 1 - ratio)
      (dimension := dimension) (ε := ε) (by linarith) hmesh0 le_rfl hshape
      hdur hKgRate (Real.rpow_pos_of_pos hmesh0 _) hbaseRho
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
    rw [h, preimage_univ, inter_univ, stagePositive_null hp old X good stage, mul_zero]
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

end Stage

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
