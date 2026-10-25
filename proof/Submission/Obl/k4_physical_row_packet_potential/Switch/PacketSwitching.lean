-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketSwitching.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The six-switch curl bound in the frame of one old packet.

Base: the frozen `packetBase` (normalized time and planar position at the
packet's clock `h`), started at `t0 = j h`; velocity `(1, V)`; height the
parent signal in units of the clock, `P(x(l, t)) / h`. In these coordinates
the quadratic incidence point of `field_six_switch_curl_coefficients_box` is
exactly `(packetBase z, P(x z) / h)` and the height speed is `rate P l t`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.FieldExperiment
import Submission.Obl.k4_physical_row_packet_potential.PotentialFits
import Submission.Obl.k4_initial_horizon_bound.Duration

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialNorming
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open Submission.Lib.K4ProjectedGroups (sc0 sc1 sc2 sig sig_eq continuous_sc0 continuous_sc1
  continuous_sc2)
open scoped ENNReal

noncomputable section

namespace PacketSwitching

/-- The packet base at the start of the block, as a coordinate vector. -/
def startBase (T j : ℕ) (c u : P2) (l : Ln) : Fin 3 → ℝ :=
  fun i => packetBase T j c u (l, start T j) i

/-- `P / h` at the start of the block. -/
def height0 (T j : ℕ) (P : Po) (l : Ln) : ℝ :=
  (sc0 P l.2 + start T j * sc1 P l.2 + start T j ^ 2 * sc2 P l.2) / clock T

/-- The parent rate at the start of the block. -/
def height1 (T j : ℕ) (P : Po) (l : Ln) : ℝ := sc1 P l.2 + 2 * start T j * sc2 P l.2

/-- The quadratic coefficient of `P / h` in normalized block time. -/
def height2 (T : ℕ) (P : Po) (l : Ln) : ℝ := clock T * sc2 P l.2

theorem continuous_packetBase_line (T j : ℕ) (c u : P2) (t : ℝ) (i : Fin 3) :
    Continuous (fun l : Ln => packetBase T j c u (l, t) i) := by
  fin_cases i <;>
    simp only [packetBase, xp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop

theorem measurable_startBase (T j : ℕ) (c u : P2) : Measurable (startBase T j c u) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (continuous_packetBase_line T j c u (start T j) i).measurable

theorem measurable_direction : Measurable (direction : Ln → Fin 3 → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact ((continuous_apply 3).comp continuous_snd).measurable
  · exact ((continuous_apply 4).comp continuous_snd).measurable

theorem measurable_height0 (T j : ℕ) (P : Po) : Measurable (height0 T j P) :=
  ((((continuous_sc0 P).comp continuous_snd).add
    (continuous_const.mul ((continuous_sc1 P).comp continuous_snd))).add
      (continuous_const.mul ((continuous_sc2 P).comp continuous_snd))).measurable.div_const _

theorem measurable_height1 (T j : ℕ) (P : Po) : Measurable (height1 T j P) :=
  (((continuous_sc1 P).comp continuous_snd).add
    (continuous_const.mul ((continuous_sc2 P).comp continuous_snd))).measurable

theorem measurable_height2 (T : ℕ) (P : Po) : Measurable (height2 T P) :=
  (continuous_const.mul ((continuous_sc2 P).comp continuous_snd)).measurable

theorem signal_eq {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    packetSignal P (l, t) = sc0 P l.2 + t * sc1 P l.2 + t ^ 2 * sc2 P l.2 := by
  rw [← sig_eq hP]
  rfl

/-- The quadratic line point is the packet base and `P / h`. -/
theorem linePoint_eq {P : Po} (hP : P.totalDegree ≤ 2) (T j : ℕ) (c u : P2) (l : Ln) (s : ℝ) :
    quadraticLinePoint (startBase T j c u) direction (height0 T j P) (height1 T j P)
        (height2 T P) l s =
      ((fun i => packetBase T j c u (l, start T j + clock T * s) i),
        packetSignal P (l, start T j + clock T * s) / clock T) := by
  have hh := (clock_pos T).ne'
  refine Prod.ext ?_ ?_
  · change startBase T j c u l + s • direction l = _
    rw [packetBase_normalized]
    rfl
  · change quadraticHeight (height0 T j P l) (height1 T j P l) (height2 T P l) s = _
    rw [signal_eq hP]
    simp only [quadraticHeight, height0, height1, height2]
    field_simp
    ring

/-- The quadratic incidence point is `(packetBase z, P(x z) / h)`. -/
theorem incidencePoint_eq {P : Po} (hP : P.totalDegree ≤ 2) (T j : ℕ) (c u : P2) (z : Ev) :
    quadraticIncidencePoint (start T j) (clock T) (startBase T j c u) direction
        (height0 T j P) (height1 T j P) (height2 T P) z =
      ((fun i => packetBase T j c u z i), packetSignal P z / clock T) := by
  have hz : start T j + clock T * ((z.2 - start T j) / clock T) = z.2 := by
    field_simp [(clock_pos T).ne']
    ring
  change quadraticLinePoint _ _ _ _ _ z.1 ((z.2 - start T j) / clock T) = _
  rw [linePoint_eq hP, hz]

/-- The height speed is the parent rate. -/
theorem speed_eq {P : Po} (hP : P.totalDegree ≤ 2) (T j : ℕ) (l : Ln) (s : ℝ) :
    quadraticHeightSpeed (height1 T j P l) (height2 T P l) s =
      ParentSignal.rate P l (start T j + clock T * s) := by
  rw [ParentSignal.rate_eq_coefficients hP]
  simp only [quadraticHeightSpeed, height1, height2]
  ring

/-- The original incidence law of an event set in unit time. -/
theorem law_eq (ν₀ : Measure Ln) [SFinite ν₀] {S : Set Ev} (hS : MeasurableSet S)
    (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (ν₀.prod (volume.restrict (Icc (0 : ℝ) 1))).withDensity (S.indicator 1) =
      (ν₀.prod volume).restrict S := by
  rw [withDensity_indicator hS, withDensity_one]
  rw [← Measure.restrict_univ (μ := ν₀), Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict hS, inter_eq_left.mpr hSunit]

theorem incidenceDuration_eq {S : Set Ev} (hS : MeasurableSet S)
    (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) (l : Ln) :
    Submission.Lib.K4Homogenization.incidenceDuration (volume.restrict (Icc (0 : ℝ) 1))
        (S.indicator 1) univ l =
      Submission.Obl.k4_initial_horizon_bound.incidenceDuration S l := by
  unfold Submission.Lib.K4Homogenization.incidenceDuration
    Submission.Obl.k4_initial_horizon_bound.incidenceDuration
  rw [Measure.restrict_univ]
  have hm : MeasurableSet (Prod.mk l ⁻¹' S) := measurable_prodMk_left hS
  have hind : (fun t => S.indicator (1 : Ev → ℝ≥0∞) (l, t)) =
      (Prod.mk l ⁻¹' S).indicator 1 := by
    funext t
    simp only [Set.indicator, mem_preimage, Pi.one_apply]
    rfl
  rw [hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_eq_left.mpr]
  intro t ht
  exact (hSunit ht).2

theorem time_eq (T j : ℕ) (z : Ev) :
    start T j + clock T * ((z.2 - start T j) / clock T) = z.2 := by
  field_simp [(clock_pos T).ne']
  ring

/-- The packet base of an event is the start base moved along the direction. -/
theorem startBase_shift (T j : ℕ) (c u : P2) (z : Ev) :
    startBase T j c u z.1 + ((z.2 - start T j) / clock T) • direction z.1 =
      fun i => packetBase T j c u z i := by
  have hh := packetBase_normalized T j c u z.1 ((z.2 - start T j) / clock T)
  rw [time_eq] at hh
  exact hh.symm

theorem startBase_add_norm_le (T j : ℕ) (c u : P2) (z : Ev)
    (hz : z.2 ∈ Icc (start T j) (start T j + clock T)) {Rz Mbase : ℝ}
    (hbase : ‖(fun i => packetBase T j c u z i)‖ ≤ Rz) (hdir : ‖direction z.1‖ ≤ Mbase)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖startBase T j c u z.1 + t • direction z.1‖ ≤ Rz + Mbase := by
  have hc := clock_pos T
  set sz := (z.2 - start T j) / clock T with hsz
  have hsz0 : 0 ≤ sz := div_nonneg (by linarith [hz.1]) hc.le
  have hsz1 : sz ≤ 1 := (div_le_one hc).mpr (by linarith [hz.2])
  have heq : startBase T j c u z.1 + t • direction z.1 =
      (fun i => packetBase T j c u z i) + (t - sz) • direction z.1 := by
    rw [← startBase_shift T j c u z, ← hsz, add_assoc, ← add_smul]
    congr 2
    ring
  have hts : |t - sz| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [heq]
  calc
    _ ≤ ‖(fun i => packetBase T j c u z i)‖ + ‖(t - sz) • direction z.1‖ := norm_add_le _ _
    _ = ‖(fun i => packetBase T j c u z i)‖ + |t - sz| * ‖direction z.1‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Rz + 1 * Mbase := by
      gcongr
    _ = Rz + Mbase := by ring

/-- **Six-switch curl bound on one old packet.** The incidence law is the
original `(ν₀ × dt)` on an event set `S` of the block; base `packetBase`,
height `P / h`. States are shared to precision `b` in base and `w` in height;
the field fits the parent rate along the direction `(1, V)`. -/
theorem packet_six_switch_curl_coefficients (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ {Q C ι : Type*}
      [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q] [StandardBorelSpace Q]
      [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C]
      [Nonempty C]
      (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (ν₀ : Measure Ln) [IsFiniteMeasure ν₀]
      (S : Set Ev) (hS : MeasurableSet S) (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (hpos : 0 < (ν₀.prod volume) S)
      (state : Ev → Q) (hstate : Measurable state)
      (control : Ln → C) (hcontrol : Measurable control) (v : C → EuclideanSpace ℝ (Fin 3))
      (π : Measure C) [IsProbabilityMeasure π]
      (K p : ENNReal) (r U : ℝ) (hr : 0 < r) (hU : 0 < U)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        (ν₀.prod volume) ({z | state z = q ∧ control z.1 ∈ A} ∩ S) ≤
          K * (ν₀.prod volume) (state ⁻¹' {q} ∩ S) * π A)
      (hratio : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
        (ν₀.prod volume)
            ((state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ∩ S) ≤
          p * (ν₀.prod volume) (state ⁻¹' {q} ∩ S))
      (hv : ∀ z ∈ S, ∀ i, |v (control z.1) i| ≤ U)
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D)
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ clock T)
      (ε b w τv B A Rz Mbase Mheight : ℝ) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : 0 ≤ w)
      (hτv : 0 ≤ τv) (hB : 0 ≤ B) (hA : 0 ≤ A) (hMbase : 0 ≤ Mbase) (hMheight : 0 ≤ Mheight)
      (hvelocity : ∀ z ∈ S, ‖direction z.1 - (fun i : Fin 3 => v (control z.1) i)‖ ≤ τv)
      (hfit : ∀ z ∈ S, |ParentSignal.rate P z.1 z.2 -
        ∑ i, direction z.1 i * MvPolynomial.eval (fun k => packetBase T j c u z k) (Tf i)| ≤ ε)
      (hbaseR : ∀ z ∈ S, ‖(fun i => packetBase T j c u z i)‖ ≤ Rz)
      (hdirR : ∀ z ∈ S, ‖direction z.1‖ ≤ Mbase)
      (hheightR : ∀ z ∈ S, |height1 T j P z.1| + 2 * |height2 T P z.1| ≤ Mheight)
      (hfield : ∀ x ∈ Metric.closedBall 0 (Rz + Mbase + 7 * (b + b * Mbase + τv)), ∀ i,
        |MvPolynomial.eval x (Tf i)| ≤ B)
      (hspace : ∀ x ∈ Metric.closedBall 0 (Rz + Mbase + 7 * (b + b * Mbase + τv)),
        ∀ y ∈ Metric.closedBall 0 (Rz + Mbase + 7 * (b + b * Mbase + τv)), ∀ i,
          |MvPolynomial.eval x (Tf i) - MvPolynomial.eval y (Tf i)| ≤ A * ‖x - y‖)
      (hgeom : ∀ z ∈ S, ∀ z' ∈ S, state z = state z' →
        ‖(fun i => packetBase T j c u z i) - (fun i => packetBase T j c u z' i)‖ ≤ b ∧
          |packetSignal P z / clock T - packetSignal P z' / clock T| ≤ w)
      (Target : Set ((Fin 3 → ℝ) × ℝ))
      (hsupport : ∀ z ∈ S,
        ((fun i => packetBase T j c u z i), packetSignal P z / clock T) ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ k,
        |(splitHeadCoordinates 3).symm y k - centers i k| ≤ widths k)
      (hwidthH : simHeightError D (clock T / q) ε (b + b * Mbase) τv (w + b * Mheight) B U A ≤
        widths 0)
      (hwidthB : ∀ k : Fin 3, 6 * (b + b * Mbase + τv) ≤ widths k.succ)
      (Rb : ℝ) (hRb : 1 ≤ Rb) (Kcap : ENNReal)
      (hcap : ((ν₀.prod volume).restrict S).map
          (fun z => fun i => Rb⁻¹ * packetBase T j c u z i) ≤ Kcap • volume)
      (hbox : ∀ z ∈ S, ∀ i, |packetBase T j c u z i| ≤ Rb)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (K * ENNReal.ofReal (clock T / q)) ^ 6 *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * (((ν₀.prod volume) S)⁻¹ * (ENNReal.ofReal q * ν₀ univ) + p) +
          ((ν₀.prod volume) S)⁻¹ * Kcap * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i k m, |(pderiv k (Tf i) - pderiv i (Tf k)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := field_six_switch_curl_coefficients_box D
  refine ⟨cNorm, cCurl, ?_⟩
  intro Q C ι _ _ _ _ _ _ _ _ _ T j c u P hP ν₀ _ S hS hSunit htime hpos state hstate control
    hcontrol v π _ K p r U hr hU hrect hratio hv Tf hT q hq hqh ε b w τv B A Rz Mbase Mheight
    hε hb hw hτv hB hA hMbase hMheight hvelocity hfit hbaseR hdirR hheightR hfield hspace hgeom
    Target hsupport I centers widths hcover hwidthH hwidthB Rb hRb Kcap hcap hbox θ Λ Λ' hθ hΛ
    hΛ' hbudget
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hlaw := law_eq ν₀ hS hSunit
  have hF : Measurable (S.indicator (1 : Ev → ℝ≥0∞)) := measurable_one.indicator hS
  have hF1 : ∀ z, S.indicator (1 : Ev → ℝ≥0∞) z ≤ 1 := fun z =>
    Set.indicator_le_self' (fun _ _ => zero_le_one) z
  have hae {pr : Ev → Prop} (h : ∀ z ∈ S, pr z) :
      ∀ᵐ z ∂((ν₀.prod (volume.restrict (Icc (0 : ℝ) 1))).withDensity (S.indicator 1)), pr z := by
    rw [hlaw]
    exact ae_restrict_of_forall_mem hS h
  have hmass : ((ν₀.prod (volume.restrict (Icc (0 : ℝ) 1))).withDensity (S.indicator 1)) univ =
      (ν₀.prod volume) S := by
    rw [hlaw, Measure.restrict_apply_univ]
  have hpoint (z : Ev) := incidencePoint_eq hP T j c u z
  apply hcurl ν₀ (volume.restrict (Icc (0 : ℝ) 1)) Measure.restrict_le_self (S.indicator 1) hF hF1
    (by rw [hmass]; exact hpos) state hstate control hcontrol v π K p r U hr hU
    (fun q A hA => by rw [hlaw, Measure.restrict_apply' hS, Measure.restrict_apply' hS]; exact hrect q A hA)
    (fun q W hW => by rw [hlaw, Measure.restrict_apply' hS, Measure.restrict_apply' hS]; exact hratio q W hW)
    (start T j) (clock T) (clock_pos T) (hae htime) (hae hv)
    (startBase T j c u) direction (height0 T j P) (height1 T j P) (height2 T P)
    (measurable_startBase T j c u) measurable_direction (measurable_height0 T j P)
    (measurable_height1 T j P) (measurable_height2 T P) Tf hT q hq hqh ε (b + b * Mbase) τv
    (w + b * Mheight) B A (Rz + Mbase) hε (by positivity) hτv (by positivity) hB hA
    (hae hvelocity)
    (hae (fun z hz => by
      rw [speed_eq hP, time_eq, startBase_shift]
      simpa only [mul_comm] using hfit z hz))
    (hae (fun z hz _ t ht => startBase_add_norm_le T j c u z (htime z hz) (hbaseR z hz)
      (hdirR z hz) ht))
    hfield hspace (· ∈ S) (hae (fun z hz => hz))
    (fun old redraw hstate' hold hred hs _ => by
      have hgeo := hgeom redraw hred old hold hstate'
      have hred01 : (redraw.2 - start T j) / clock T ∈ Icc (0 : ℝ) 1 := by
        have hc := clock_pos T
        constructor
        · exact div_nonneg (by linarith [(htime redraw hred).1]) hc.le
        · exact (div_le_one hc).mpr (by linarith [(htime redraw hred).2])
      have htime' : |(old.2 - start T j) / clock T - (redraw.2 - start T j) / clock T| ≤ b := by
        have h0 := norm_le_pi_norm ((fun i => packetBase T j c u redraw i) -
          (fun i => packetBase T j c u old i)) 0
        have hp0 (z : Ev) : packetBase T j c u z 0 = (z.2 - start T j) / clock T := rfl
        rw [Real.norm_eq_abs, Pi.sub_apply, hp0, hp0, abs_sub_comm] at h0
        exact h0.trans hgeo.1
      have hbase0 : ‖(quadraticLinePoint (startBase T j c u) direction (height0 T j P)
          (height1 T j P) (height2 T P) redraw.1 ((redraw.2 - start T j) / clock T)).1 -
          (quadraticLinePoint (startBase T j c u) direction (height0 T j P) (height1 T j P)
            (height2 T P) old.1 ((old.2 - start T j) / clock T)).1‖ ≤ b := by
        have h1 := hpoint redraw
        have h2 := hpoint old
        change (quadraticLinePoint _ _ _ _ _ redraw.1 _) = _ at h1
        change (quadraticLinePoint _ _ _ _ _ old.1 _) = _ at h2
        rw [h1, h2]
        exact hgeo.1
      have hheight0 : |(quadraticLinePoint (startBase T j c u) direction (height0 T j P)
          (height1 T j P) (height2 T P) redraw.1 ((redraw.2 - start T j) / clock T)).2 -
          (quadraticLinePoint (startBase T j c u) direction (height0 T j P) (height1 T j P)
            (height2 T P) old.1 ((old.2 - start T j) / clock T)).2| ≤ w := by
        have h1 := hpoint redraw
        have h2 := hpoint old
        change (quadraticLinePoint _ _ _ _ _ redraw.1 _) = _ at h1
        change (quadraticLinePoint _ _ _ _ _ old.1 _) = _ at h2
        rw [h1, h2]
        exact hgeo.2
      exact quadratic_shared_state_error_of_point_time_error (startBase T j c u) direction
        (height0 T j P) (height1 T j P) (height2 T P) old.1 redraw.1
        ((old.2 - start T j) / clock T) ((redraw.2 - start T j) / clock T) b b w Mbase Mheight
        hs hred01 htime' (hdirR redraw hred) (hheightR redraw hred) hbase0 hheight0)
    Target (hae (fun z hz => by rw [hpoint z]; exact hsupport z hz)) I centers widths hcover
    hwidthH hwidthB Rb hRb Kcap
    (by
      have hfun : (fun z => fun i => Rb⁻¹ * (quadraticIncidencePoint (start T j) (clock T)
          (startBase T j c u) direction (height0 T j P) (height1 T j P) (height2 T P) z).1 i) =
          (fun z => fun i => Rb⁻¹ * packetBase T j c u z i) := by
        funext z i
        rw [hpoint z]
      rw [hfun, hlaw]
      exact hcap)
    (hae (fun z hz => by rw [hpoint z]; exact hbox z hz)) θ Λ Λ' hθ hΛ hΛ'
    (by rw [hmass]; exact hbudget)

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
