import Submission.Obl.k4_raw_localized_native_systems.C.StripFrame
import Submission.Obl.k4_raw_localized_native_systems.C.CStrip
import Submission.Obl.k4_horizon_chart_assembly.Selections
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry
import Submission.Lib.K4XInterface.Formats
import Submission.Lib.K4XInterface.Charts

/-
Adapted from this LOT tree, o178, session x0596, `CChart.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# A full-time strip as a frozen chart at depth zero

For a world `γ`, a binning time `t₀` and a representative later chart `b`, the
full-time chart has

* frame `stripFrame g n` (unit tangent, normal width `g`), centre `int ⋅ n` and
  velocity `speed ⋅ n`, where `n`, `int`, `speed` are the clipped strip data of `b`;
* assignment: the lines of the bin mates of `b` at `t₀` that fit the native test
  in this frame over the whole unit interval (accepted o160 `WholeBlockFit`);
* selected incidences: the incidences of these lines selected by a later chart
  of the same world whose strip data are compatible with those of `b` (up to a
  simultaneous sign), with the native derivative floor (accepted o160
  `selectedEvent`);
* lists: the representatives compatible with a later chart listed by the
  original observation.

Every clause of the frozen `chart` predicate at depth zero and time exponent zero
holds, with the lists as extra clause.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Lib.K4XInterface (gfmt gfmt_inter gfmt_union gfmt_compl gfmt_univ gfmt_mono
  measurableSet_of_gfmt)

noncomputable section

variable {p : Data} {k : ℕ}

/-- Two later charts with nearly equal strip data, up to a simultaneous sign. -/
def Compat (a : Atlas p k) (Kc ε : ℝ) (b b' : Fin a.C) : Prop :=
  (‖q2normal a b - q2normal a b'‖ ≤ ε ∧ |q2intercept a Kc b - q2intercept a Kc b'| ≤ ε ∧
      |q2speed a Kc b - q2speed a Kc b'| ≤ ε) ∨
  (‖q2normal a b + q2normal a b'‖ ≤ ε ∧ |q2intercept a Kc b + q2intercept a Kc b'| ≤ ε ∧
      |q2speed a Kc b + q2speed a Kc b'| ≤ ε)

/-- The later charts of world `γ` compatible with `b`. -/
def compatSet (a : Atlas p k) (γ : Fin (p.W k)) (Kc ε : ℝ) (b : Fin a.C) :
    Finset (Fin a.C) := by
  classical
  exact Finset.univ.filter fun b'' => a.γ b'' = γ ∧ Compat a Kc ε b'' b

/-- The whole-block native fit in the frame of the strip of `b`. -/
def stripFit (a : Atlas p k) (γ : Fin (p.W k)) (Kc g κC : ℝ) (b : Fin a.C) :
    Set (Fin 6 → ℝ) :=
  {x | Submission.Obl.k4_horizon_chart_assembly.WholeBlockFit (p.P k γ)
    (stripFrame g (q2normal a b)) (q2intercept a Kc b • q2normal a b)
    (q2speed a Kc b • q2normal a b) κC (p.B k γ) 1 0 1 x}

/-- The assignment of the full-time chart represented by `b`. -/
def cA (a : Atlas p k) (γ : Fin (p.W k)) (t₀ lam Kc G g κC : ℝ) (b : Fin a.C) : Set Line :=
  (⋃ b' ∈ binMates a γ t₀ lam Kc G b, a.A b') ∩ {l | l.2 ∈ stripFit a γ Kc g κC b}

/-- The compatible later incidences of world `γ`. -/
def compatEvent (a : Atlas p k) (γ : Fin (p.W k)) (Kc ε : ℝ) (b : Fin a.C) : Set Point :=
  ⋃ b'' ∈ compatSet a γ Kc ε b, a.F b''

/-- The selected incidences of the full-time chart represented by `b`. -/
def cF (a : Atlas p k) (γ : Fin (p.W k)) (t₀ lam Kc G g κC ε : ℝ) (b : Fin a.C) :
    Set Point :=
  Submission.Obl.k4_horizon_chart_assembly.selectedEvent (compatEvent a γ Kc ε b)
    (cA a γ t₀ lam Kc G g κC b) (p.P k γ) (p.B k γ / κC) 0 2

/-- The lists: the representatives compatible with a listed later chart. -/
def cLst (a : Atlas p k) (γ : Fin (p.W k)) (Kc ε : ℝ) {m : ℕ} (rep : Fin m → Fin a.C)
    (o : Observation) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ∃ b'' ∈ a.lst γ o, b'' ∈ compatSet a γ Kc ε (rep i)

/-- Boolean format of a finite union. -/
theorem gfmt_biUnion {n : ℕ} {ι : Type*} (s : Finset ι) {H : ℝ} {D : ℕ}
    (A : ι → Set (Fin n → ℝ)) (hA : ∀ i ∈ s, gfmt n H D (A i)) :
    gfmt n (s.card * H) D (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.notMem_empty,
        Set.iUnion_of_empty, Set.iUnion_empty]
      have := gfmt_compl (gfmt_univ n 0 le_rfl D)
      simpa using this
  | insert i s hi ih =>
      have h1 := hA i (Finset.mem_insert_self i s)
      have h2 := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      have h3 := gfmt_union h1 h2
      rw [Finset.card_insert_of_notMem hi, Finset.set_biUnion_insert]
      simp only [max_self] at h3
      convert h3 using 2
      push_cast; ring

theorem stripFit_format (a : Atlas p k) (γ : Fin (p.W k)) (Kc g κC : ℝ) (b : Fin a.C)
    (hP : (p.P k γ).totalDegree ≤ 2) (hκC : 0 ≤ κC) :
    gfmt 6 84 4 (stripFit a γ Kc g κC b) := by
  have h := Submission.Obl.k4_horizon_chart_assembly.wholeBlockFit_polynomialFormat (p.P k γ) hP
    (stripFrame g (q2normal a b)) (q2intercept a Kc b • q2normal a b)
    (q2speed a Kc b • q2normal a b) κC (p.B k γ) 1 0 1 84 1 hκC zero_le_one (by norm_num)
  unfold Submission.Obl.k4_horizon_chart_assembly.PolynomialFormat at h
  rw [pow_one] at h
  exact h

theorem mem_cA {a : Atlas p k} {γ : Fin (p.W k)} {t₀ lam Kc G g κC : ℝ} {b : Fin a.C} {l : Line} :
    l ∈ cA a γ t₀ lam Kc G g κC b ↔
      (∃ b' ∈ binMates a γ t₀ lam Kc G b, l ∈ a.A b') ∧ l.2 ∈ stripFit a γ Kc g κC b := by
  simp [cA]

theorem mem_compatEvent {a : Atlas p k} {γ : Fin (p.W k)} {Kc ε : ℝ} {b : Fin a.C} {z : Point} :
    z ∈ compatEvent a γ Kc ε b ↔ ∃ b'' ∈ compatSet a γ Kc ε b, z ∈ a.F b'' := by
  simp [compatEvent]

theorem mem_compatSet {a : Atlas p k} {γ : Fin (p.W k)} {Kc ε : ℝ} {b b'' : Fin a.C} :
    b'' ∈ compatSet a γ Kc ε b ↔ a.γ b'' = γ ∧ Compat a Kc ε b'' b := by
  classical
  simp [compatSet]

theorem mem_cLst {a : Atlas p k} {γ : Fin (p.W k)} {Kc ε : ℝ} {m : ℕ} {rep : Fin m → Fin a.C}
    {o : Observation} {i : Fin m} :
    i ∈ cLst a γ Kc ε rep o ↔ ∃ b'' ∈ a.lst γ o, b'' ∈ compatSet a γ Kc ε (rep i) := by
  classical
  simp [cLst]

section chart

variable {M₂ D₂ : ℕ} {κ r : ℝ} {a : Atlas p k} {ex : Fin a.C → Prop}

/-- **The full-time chart** at depth zero and time exponent zero. -/
theorem cChart (hc : ChartsHyp a M₂ D₂ κ r ex)
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (γ : Fin (p.W k)) {m : ℕ} (rep : Fin m → Fin a.C) (i : Fin m)
    {t₀ lam Kc G g κC ε : ℝ} (M D : ℕ)
    (hPd : (p.P k γ).totalDegree ≤ 2) (hPc : ∀ e, |(p.P k γ).coeff e| ≤ p.N k ^ M)
    (hEsub : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hKc : 0 ≤ Kc) (hg : 0 < g) (hκC : 2 * (1 + g) ≤ κC)
    (hM₁ : 2 * Kc ≤ p.N k ^ M) (hM₂ : 2 * (2 + g + g⁻¹) ≤ p.N k ^ M)
    (hM₃ : 2 * (a.C : ℝ) * p.N k ^ M₂ + 88 ≤ p.N k ^ M) (hM₄ : p.N k ^ M₂ ≤ p.N k ^ M)
    (hM₂0 : 0 ≤ p.N k ^ M₂) (hD₂ : D₂ ≤ D) (hD : 4 ≤ D) :
    chart (p.N k) M D κC 0 0 0 (p.B k γ) (p.E k γ)
      (q2intercept a Kc (rep i) • q2normal a (rep i)) (q2speed a Kc (rep i) • q2normal a (rep i))
      (stripFrame g (q2normal a (rep i))) (p.P k γ) (cA a γ t₀ lam Kc G g κC (rep i))
      (cF a γ t₀ lam Kc G g κC ε (rep i))
      (∀ z ∈ cF a γ t₀ lam Kc G g κC ε (rep i),
        i ∈ cLst a γ Kc ε rep (obs (p.B k γ) (δ (p.N k) p.L) z)) := by
  classical
  set b := rep i with hb
  have hdet : (a.Q b).det ≠ 0 := hc.det_ne b
  have hn : ‖q2normal a b‖ = 1 := norm_minorNormal hdet
  have hint : |q2intercept a Kc b| ≤ Kc := abs_clip_le hKc
  have hsp : |q2speed a Kc b| ≤ Kc := abs_clip_le hKc
  have hn0 : |q2normal a b 0| ≤ 1 := (abs_coord_le_norm_fin2 _ 0).trans hn.le
  have hn1 : |q2normal a b 1| ≤ 1 := (abs_coord_le_norm_fin2 _ 1).trans hn.le
  have hκC0 : 0 ≤ κC := by linarith
  have hcard1 : ((binMates a γ t₀ lam Kc G b).card : ℝ) ≤ a.C := by
    have := Finset.card_le_univ (binMates a γ t₀ lam Kc G b)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hcard2 : ((compatSet a γ Kc ε b).card : ℝ) ≤ a.C := by
    have := Finset.card_le_univ (compatSet a γ Kc ε b)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hfit := stripFit_format a γ Kc g κC b hPd hκC0
  have hAm : MeasurableSet (cA a γ t₀ lam Kc G g κC b) := by
    refine (Finset.measurableSet_biUnion _ fun b' _ => hc.measA b').inter ?_
    exact measurable_snd (measurableSet_of_gfmt hfit)
  have hEm : MeasurableSet (compatEvent a γ Kc ε b) :=
    Finset.measurableSet_biUnion _ fun b'' _ => hc.measF b''
  -- formats
  have hAfmt : ∀ i₀ : ℕ, gfmt 6
      ((binMates a γ t₀ lam Kc G b).card * p.N k ^ M₂ + 84) (max D₂ 4)
      {x | (i₀, x) ∈ cA a γ t₀ lam Kc G g κC b} := by
    intro i₀
    have h1 := gfmt_biUnion (binMates a γ t₀ lam Kc G b) (H := p.N k ^ M₂) (D := D₂)
      (fun b' => {x | (i₀, x) ∈ a.A b'}) (fun b' _ => ((hc b').2.2.2.2.2.2.2.2.1 i₀).1)
    have h2 := gfmt_inter h1 hfit
    convert h2 using 1
    ext x
    simp [cA, stripFit]
  have hEfmt : ∀ i₀ : ℕ, gfmt 7 ((compatSet a γ Kc ε b).card * p.N k ^ M₂) D₂
      {z : Fin 7 → ℝ | ((i₀, fun e : Fin 6 => z e.castSucc), z 6) ∈ compatEvent a γ Kc ε b} := by
    intro i₀
    have h1 := gfmt_biUnion (compatSet a γ Kc ε b) (H := p.N k ^ M₂) (D := D₂)
      (fun b'' => {z : Fin 7 → ℝ | ((i₀, fun e : Fin 6 => z e.castSucc), z 6) ∈ a.F b''})
      (fun b'' _ => ((hc b'').2.2.2.2.2.2.2.2.1 i₀).2)
    convert h1 using 1
    ext z
    simp [compatEvent]
  refine ⟨?_, ?_, ?_, ?_, hPd, hPc, hAm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stripFrame_det hn]; exact hg.ne'
  · rw [norm_smul, norm_smul, hn, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [stripFrame_inv hn hg.ne', stripFrame_apply]
    simp only [stripFrameInv, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_div, abs_of_pos hg]
    have hgi : 0 < g⁻¹ := inv_pos.2 hg
    have e1 : |q2normal a b 0| / g ≤ g⁻¹ := by
      rw [div_eq_mul_inv]; nlinarith
    have e2 : |q2normal a b 1| / g ≤ g⁻¹ := by
      rw [div_eq_mul_inv]; nlinarith
    have e3 : g * |q2normal a b 0| ≤ g := by nlinarith
    have e4 : g * |q2normal a b 1| ≤ g := by nlinarith
    linarith
  · rw [stripFrame_apply]
    simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, pow_zero, div_one]
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hg]
    have e3 : g * |q2normal a b 0| ≤ g := by nlinarith
    have e4 : g * |q2normal a b 1| ≤ g := by nlinarith
    linarith
  · exact Submission.Obl.k4_horizon_chart_assembly.selectedEvent_measurable hEm hAm _ _ _ _
  · intro i₀
    constructor
    · have h := gfmt_mono (n := 6) (H' := p.N k ^ M) (D' := D) ?_ ?_ (hAfmt i₀)
      · exact h
      · have : ((binMates a γ t₀ lam Kc G b).card : ℝ) * p.N k ^ M₂ ≤ a.C * p.N k ^ M₂ :=
          mul_le_mul_of_nonneg_right hcard1 hM₂0
        nlinarith
      · exact max_le hD₂ hD
    · have h := Submission.Obl.k4_horizon_chart_assembly.selectedEvent_format
        (compatEvent a γ Kc ε b) (cA a γ t₀ lam Kc G g κC b) hEfmt hAfmt (p.P k γ) hPd
        (p.B k γ / κC) 0 2 i₀
      refine gfmt_mono ?_ ?_ h
      · have h1 : ((binMates a γ t₀ lam Kc G b).card : ℝ) * p.N k ^ M₂ ≤ a.C * p.N k ^ M₂ :=
          mul_le_mul_of_nonneg_right hcard1 hM₂0
        have h2 : ((compatSet a γ Kc ε b).card : ℝ) * p.N k ^ M₂ ≤ a.C * p.N k ^ M₂ :=
          mul_le_mul_of_nonneg_right hcard2 hM₂0
        nlinarith
      · exact max_le hD₂ (max_le (max_le hD₂ hD) (by omega))
  · intro l hl
    rw [mem_cA] at hl
    obtain ⟨⟨b', -, hlA⟩, hlfit⟩ := hl
    obtain ⟨h1, h2, -⟩ := (hc b').2.2.2.2.2.2.2.2.2.1 l hlA
    refine ⟨h1.trans hM₄, fun e => (h2 e).trans hM₄, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa using ht
    obtain ⟨f1, f2, f3, f4⟩ := hlfit t ht'
    refine ⟨f1, ?_, ?_, ?_⟩
    · rw [delta_zero]; exact f2
    · exact f3
    · rw [delta_zero]; exact f4
  · intro z hz
    obtain ⟨⟨hzE, hzA, -⟩, hzD⟩ := hz
    rw [mem_compatEvent] at hzE
    obtain ⟨b'', hb'', hzF⟩ := hzE
    rw [mem_compatSet] at hb''
    have hsel := hc.selected b'' hzF
    rw [hb''.1] at hsel
    refine ⟨hsel.1, hzA, ?_, hzD⟩
    have := (hEsub hsel.1).2
    simpa using this
  · intro z hz
    obtain ⟨⟨hzE, -, -⟩, -⟩ := hz
    rw [mem_compatEvent] at hzE
    obtain ⟨b'', hb'', hzF⟩ := hzE
    have hl := hknown b'' z hzF
    rw [mem_compatSet] at hb''
    rw [hb''.1] at hl
    rw [mem_cLst]
    exact ⟨b'', hl, mem_compatSet.2 hb''⟩

end chart

end

end Submission.Obl.k4_raw_localized_native_systems.C
