-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceWindow
import Submission.Obl.k4_finite_affine_parent_sources.SourceNumerator

/-!
# The window parent of a prepared residual, in original units

For a prepared residual `S0` inside the terminal path with weighted mass at least `Z`, the
fixed law `μ₀ = WorldPath.probability ν ω S0`, the likelihood window `exists_window_parent`
(weights: the packets of the labels, normalised by the mass of `S0`) and the numerator
conversion `numerator_original` give one window `i < J`, one parent `b₀` at level `level i` and
its retained set `S1 ⊆ S0 ∩ par` with

* the packet floor `Z / (8 m) · (ν × dt)(packet b₀) ≤ (ν × dt)(S1)`,
* the success floor `(ν × dt)(S0 ∩ par) ≤ 8 (ν × dt)(S1)`,
* the end-history/velocity-code numerator with constant `winBase^(1/2)`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance optMeasBW (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingBW (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- The number of planar velocity codes of the window, plus one. -/
def winCount (Rv δv : ℝ) : ℕ := (Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1

/-- The base of the likelihood window, chosen so that the window exponent is `1/2`. -/
def winBase (Rv δv : ℝ) (J : ℕ) : ℝ := Real.exp (4 * (Real.log (winCount Rv δv) / J + 1))

theorem winBase_exponent_pos (Rv δv : ℝ) (J : ℕ) :
    0 < Real.log (winCount Rv δv) / J + 1 := by
  have h1 : (1 : ℝ) ≤ winCount Rv δv := by
    have : 1 ≤ winCount Rv δv := by unfold winCount; omega
    exact_mod_cast this
  have : 0 ≤ Real.log (winCount Rv δv) := Real.log_nonneg h1
  positivity

theorem winBase_theta (Rv δv : ℝ) (J : ℕ) :
    Real.sqrt ((Real.log (winCount Rv δv) / J + 1) / Real.log (winBase Rv δv J)) = 1 / 2 := by
  have hpos := winBase_exponent_pos Rv δv J
  rw [winBase, Real.log_exp]
  rw [show (Real.log (winCount Rv δv) / J + 1) / (4 * (Real.log (winCount Rv δv) / J + 1)) =
    (1 / 2) ^ 2 by field_simp; norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem one_lt_winBase (Rv δv : ℝ) (J : ℕ) : 1 < winBase Rv δv J := by
  have hpos := winBase_exponent_pos Rv δv J
  exact Real.one_lt_exp_iff.mpr (by positivity)

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- A history at a level below the terminal level is a label of that level. -/
theorem history_level {i : ℕ} (hi : i ≤ m - 1) {b : Fin p.C} {y : Fin W × Incidence}
    (hy : p.history m i y = some b) : p.lev b = i := by
  cases hcode : p.terminalCode m y with
  | none =>
    simp [PathData.history, hcode, PathData.ancestorCode] at hy
  | some bt =>
    have hspec := p.terminalCode_spec m hcode
    simp only [PathData.history, Function.comp_apply, hcode, PathData.ancestorCode,
      Option.map_some, Option.some.injEq] at hy
    rw [← hy]
    exact forestAncestor_level (fun b hb => (hp.parent b hb).1) bt i (by omega)

omit hp in
/-- Terminal incidences have a history at every level. -/
theorem history_ne_none {i : ℕ} {y : Fin W × Incidence}
    (hy : y.2 ∈ TerminalInc W p.C m p.lev p.world p.counted y.1) :
    p.history m i y ≠ none := by
  obtain ⟨bt, hbt⟩ := p.terminalCode_exists m y.1 hy
  simp [PathData.history, PathData.ancestorCode, hbt]

/-- The packets of one level fill at most the unit weighted time (real form). -/
theorem level_packets_real (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1) (i : ℕ) :
    (∑ b, if p.lev b = i then ω (p.world b) *
      ((ν (p.world b)).prod volume).real (p.packet b) else 0) ≤ 1 := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have h := hp.assignment_time_budget hν hω0 hω1 i
  have hfin : ∀ b ∈ (Finset.univ : Finset (Fin p.C)),
      (if p.lev b = i then ENNReal.ofReal (ω (p.world b)) *
        (ν (p.world b)).prod volume (p.packet b) else 0) ≠ ⊤ := by
    intro b _
    split_ifs
    · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      have hsub : p.packet b ⊆ univ ×ˢ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
          (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
        intro x hx
        exact ⟨trivial, hx.2⟩
      refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
      rw [Measure.prod_prod, Real.volume_Icc]
      exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_sum hfin, ENNReal.toReal_one] at hreal
  convert hreal using 2 with b
  split_ifs
  · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω0 _), measureReal_def]
  · rfl

/-- The packets of all levels fill at most `m` (real form). -/
theorem all_packets_real (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1) :
    (∑ b, ω (p.world b) * ((ν (p.world b)).prod volume).real (p.packet b)) ≤ m := by
  have hsplit : (∑ b, ω (p.world b) * ((ν (p.world b)).prod volume).real (p.packet b)) =
      ∑ i ∈ Finset.range m, ∑ b, if p.lev b = i then ω (p.world b) *
        ((ν (p.world b)).prod volume).real (p.packet b) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (hp.label_level b))]
  rw [hsplit]
  calc (∑ i ∈ Finset.range m, ∑ b, if p.lev b = i then ω (p.world b) *
        ((ν (p.world b)).prod volume).real (p.packet b) else 0)
      ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => level_packets_real hp hν hω0 hω1 i
    _ = m := by simp

/-- **The window parent of a prepared residual, in original units.** -/
theorem window_parent_original (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1) (hm : 0 < m)
    (S0 : Fin W → Set Incidence) (hS0m : ∀ w, MeasurableSet (S0 w))
    (hS0T : ∀ w, S0 w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (hS0t : ∀ w, S0 w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {Z : ℝ} (hZ : 0 < Z)
    (hmass : ENNReal.ofReal Z ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (S0 w))
    (level : ℕ → ℕ) (hlevel : Monotone level) (hle : ∀ i, level i ≤ m - 1)
    (δv Rv : ℝ) (hδv : 0 < δv) (hRv : 0 ≤ Rv)
    (hvel : ∀ w, ∀ᵐ l ∂(ν w), |l.2 3| ≤ Rv ∧ |l.2 4| ≤ Rv)
    (J : ℕ) (hJ : 0 < J) :
    ∃ i < J, ∃ (b₀ : Fin p.C) (S1 : Set Incidence), MeasurableSet S1 ∧ p.lev b₀ = level i ∧
      S1 ⊆ S0 (p.world b₀) ∩ {x | p.history m (level i) (p.world b₀, x) = some b₀} ∧
      0 < ((ν (p.world b₀)).prod volume).real S1 ∧
      Z / (8 * m) * ((ν (p.world b₀)).prod volume).real (p.packet b₀) ≤
        ((ν (p.world b₀)).prod volume).real S1 ∧
      ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
          {x | p.history m (level i) (p.world b₀, x) = some b₀}) ≤
        8 * ((ν (p.world b₀)).prod volume).real S1 ∧
      ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
        ((ν (p.world b₀)).prod volume).real (S1 ∩
          {x | p.history m (level (i + 1)) (p.world b₀, x) = h ∧
            worldBin δv (p.world b₀, x) = z}) ≤
        winBase Rv δv J ^ (1 / 2 : ℝ) * ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
            {x | p.history m (level i) (p.world b₀, x) = some b₀} ∩
            {x | p.history m (level (i + 1)) (p.world b₀, x) = h}) *
          (((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
              {x | p.history m (level i) (p.world b₀, x) = some b₀} ∩
              {x | worldBin δv (p.world b₀, x) = z}) /
            ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
              {x | p.history m (level i) (p.world b₀, x) = some b₀})) := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hmass' : ENNReal.ofReal Z ≤ WorldPath.original ν ω S0 univ := by
    rw [WorldPath.original_mass]; exact hmass
  have hpos : WorldPath.original ν ω S0 univ ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr hZ).trans_le hmass')
  have hfin : WorldPath.original ν ω S0 univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (WorldPath.original_mass_le_one ν ω hω0 hω1 S0 hS0t)
  obtain ⟨hprob, hslice⟩ := WorldPath.probability_spec ν ω hω0 hω1 S0 hS0t hpos
  set μ₀ := WorldPath.probability ν ω S0 with hμ₀
  set Zr := (WorldPath.original ν ω S0 univ).toReal with hZrdef
  have hZr : Z ≤ Zr := by
    have := ENNReal.toReal_mono hfin hmass'
    rwa [ENNReal.toReal_ofReal hZ.le] at this
  have hZr0 : 0 < Zr := lt_of_lt_of_le hZ hZr
  -- the velocity bound under the fixed law
  have hbadm : MeasurableSet {l : Trajectory | ¬(|l.2 3| ≤ Rv ∧ |l.2 4| ≤ Rv)} := by
    refine MeasurableSet.compl ?_
    exact (measurableSet_le (continuous_abs.measurable.comp
        ((measurable_pi_apply 3).comp measurable_snd)) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp
        ((measurable_pi_apply 4).comp measurable_snd)) measurable_const)
  have hbound : ∀ᵐ y ∂μ₀, ∀ e, |worldVel y e| ≤ Rv := by
    rw [ae_iff]
    apply measure_mono_null (t := ⋃ w, {w} ×ˢ
      ({l : Trajectory | ¬(|l.2 3| ≤ Rv ∧ |l.2 4| ≤ Rv)} ×ˢ (univ : Set ℝ)))
    · intro y hy
      simp only [mem_ofPred_eq, not_forall] at hy
      obtain ⟨e, he⟩ := hy
      refine mem_iUnion.mpr ⟨y.1, ⟨mem_singleton _, ?_, mem_univ _⟩⟩
      intro hcon
      fin_cases e
      · exact he hcon.1
      · exact he hcon.2
    · refine measure_iUnion_null fun w => ?_
      rw [hslice w _ (hbadm.prod MeasurableSet.univ)]
      have h0 : ((ν w).prod volume) (({l : Trajectory | ¬(|l.2 3| ≤ Rv ∧ |l.2 4| ≤ Rv)} ×ˢ
          (univ : Set ℝ)) ∩ S0 w) = 0 := by
        apply measure_mono_null inter_subset_left
        rw [Measure.prod_prod, ae_iff.mp (hvel w), zero_mul]
      rw [h0, mul_zero]
  -- the weights: packets normalised by the mass of the residual
  let wt : Option (Fin p.C) → ℝ := fun a => match a with
    | none => 0
    | some b => ω (p.world b) * ((ν (p.world b)).prod volume).real (p.packet b) / Zr
  have hwt : ∀ a, 0 ≤ wt a := by
    intro a
    cases a with
    | none => exact le_rfl
    | some b => exact div_nonneg (mul_nonneg (hω0 _) measureReal_nonneg) hZr0.le
  have hwtB : ∑ a, wt a ≤ m / Zr := by
    rw [Fintype.sum_option]
    show 0 + ∑ b, ω (p.world b) * ((ν (p.world b)).prod volume).real (p.packet b) / Zr ≤ m / Zr
    rw [zero_add, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (all_packets_real hp hν hω0 hω1) hZr0.le
  have hθ : Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
      J + 1) / Real.log (winBase Rv δv J)) = 1 / 2 := winBase_theta Rv δv J
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨i, hi, a, D, hD, ha, hfl1, hfl2, hnum⟩ := exists_window_parent hp μ₀ level hlevel hle
    δv Rv hδv hRv hbound J hJ (winBase Rv δv J) (one_lt_winBase Rv δv J) wt hwt (m / Zr)
    (by positivity) hwtB (by rw [hθ]; norm_num)
  rw [hθ] at hfl1 hfl2 hnum
  -- the fixed law lives on the residual, so the parent is a label
  have hout : μ₀ {y | y.2 ∉ S0 y.1} = 0 := by
    apply measure_mono_null (t := ⋃ w, {w} ×ˢ (S0 w)ᶜ)
    · intro y hy
      exact mem_iUnion.mpr ⟨y.1, ⟨mem_singleton _, hy⟩⟩
    · refine measure_iUnion_null fun w => ?_
      rw [hslice w _ (hS0m w).compl, compl_inter_self, measure_empty, mul_zero]
  obtain ⟨b₀, rfl⟩ : ∃ b₀, a = some b₀ := by
    cases a with
    | some b => exact ⟨b, rfl⟩
    | none =>
      exfalso
      apply ha
      apply measure_mono_null _ hout
      intro y hy
      simp only [mem_ofPred_eq] at hy ⊢
      intro hyS
      exact history_ne_none (hS0T y.1 hyS) hy
  have hne : ({y | p.history m (level i) y = some b₀} : Set (Fin W × Incidence)).Nonempty :=
    nonempty_of_measure_ne_zero ha
  obtain ⟨y₀, hy₀⟩ := hne
  have hlev : p.lev b₀ = level i := history_level hp (hle i) hy₀
  set w₀ := p.world b₀ with hw₀
  -- the world weight is positive
  have hparm : MeasurableSet {x : Incidence | p.history m (level i) (w₀, x) = some b₀} :=
    (hp.measurable_history _).comp measurable_prodMk_left (measurableSet_singleton _)
  have hslX : ∀ X : Set (Fin W × Incidence), X ∩ {y | p.history m (level i) y = some b₀} =
      {w₀} ×ˢ ({x | (w₀, x) ∈ X} ∩ {x | p.history m (level i) (w₀, x) = some b₀}) := by
    intro X
    ext ⟨w, z⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨hX, hh⟩
      have hw := (history_some hp hh).1
      simp only at hw
      subst hw
      exact ⟨rfl, hX, hh⟩
    · rintro ⟨rfl, hX, hh⟩
      exact ⟨hX, hh⟩
  have hpar_eq : {y : Fin W × Incidence | p.history m (level i) y = some b₀} =
      {w₀} ×ˢ {x | p.history m (level i) (w₀, x) = some b₀} := by
    have := hslX univ
    rw [univ_inter] at this
    rw [this]
    congr 1
    ext x
    simp
  have hω₀ : 0 < ω w₀ := by
    rcases (hω0 w₀).lt_or_eq with h | h
    · exact h
    · exfalso
      apply ha
      rw [hpar_eq, hslice _ _ hparm, ← h, ENNReal.ofReal_zero, mul_zero, zero_mul]
  -- the retained set of the parent
  set S1 : Set Incidence := {x | (w₀, x) ∈ D} ∩ S0 w₀ ∩
    {x | p.history m (level i) (w₀, x) = some b₀} with hS1
  have hS1m : MeasurableSet S1 :=
    ((measurable_prodMk_left hD).inter (hS0m w₀)).inter hparm
  have hslD : μ₀.real (D ∩ {y | p.history m (level i) y = some b₀}) =
      Zr⁻¹ * ω w₀ * ((ν w₀).prod volume).real S1 := by
    rw [hslX D]
    have hA : MeasurableSet ({x : Incidence | (w₀, x) ∈ D} ∩
        {x | p.history m (level i) (w₀, x) = some b₀}) :=
      (measurable_prodMk_left hD).inter hparm
    rw [probability_slice_real hp hν hω0 hω1 S0 hS0t hpos _ hA]
    congr 2
    ext x
    simp only [S1, mem_inter_iff, mem_ofPred_eq]
    tauto
  have hslP : μ₀.real {y | p.history m (level i) y = some b₀} =
      Zr⁻¹ * ω w₀ * ((ν w₀).prod volume).real (S0 w₀ ∩
        {x | p.history m (level i) (w₀, x) = some b₀}) := by
    rw [hpar_eq, probability_slice_real hp hν hω0 hω1 S0 hS0t hpos _ hparm, inter_comm]
  have hS1pos : 0 < ((ν w₀).prod volume).real S1 := by
    have hpos' : 0 < μ₀.real {y | p.history m (level i) y = some b₀} :=
      ENNReal.toReal_pos ha (measure_ne_top _ _)
    rw [hslP] at hpos'
    have hR : 0 < ((ν w₀).prod volume).real (S0 w₀ ∩
        {x | p.history m (level i) (w₀, x) = some b₀}) := by
      by_contra hn
      push Not at hn
      have h0 : ((ν w₀).prod volume).real (S0 w₀ ∩
          {x | p.history m (level i) (w₀, x) = some b₀}) = 0 :=
        le_antisymm hn measureReal_nonneg
      rw [h0, mul_zero] at hpos'
      exact lt_irrefl _ hpos'
    have hfl := hfl2
    rw [hslD, hslP] at hfl
    have hc : 0 < Zr⁻¹ * ω w₀ := by positivity
    nlinarith [hfl, hc, hR]
  refine ⟨i, hi, b₀, S1, hS1m, hlev, ?_, hS1pos, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hx.1.2, hx.2⟩
  · -- the packet floor
    rw [hslD] at hfl1
    have hwb : wt (some b₀) = ω w₀ * ((ν w₀).prod volume).real (p.packet b₀) / Zr := rfl
    rw [hwb] at hfl1
    have hP := (measureReal_nonneg : 0 ≤ ((ν w₀).prod volume).real (p.packet b₀))
    have e1 : (1 - 1 / 2) / (4 * (m / Zr)) *
        (ω w₀ * ((ν w₀).prod volume).real (p.packet b₀) / Zr) =
        ω w₀ * ((ν w₀).prod volume).real (p.packet b₀) / (8 * m) := by
      field_simp
      ring
    have e2 : Zr⁻¹ * ω w₀ * ((ν w₀).prod volume).real S1 =
        ω w₀ * ((ν w₀).prod volume).real S1 / Zr := by
      field_simp
    rw [e1, e2, div_le_div_iff₀ (by positivity) hZr0] at hfl1
    have h1 : ω w₀ * (((ν w₀).prod volume).real (p.packet b₀) * Zr) ≤
        ω w₀ * (((ν w₀).prod volume).real S1 * (8 * m)) := by
      linarith [hfl1]
    have h2 := le_of_mul_le_mul_left h1 hω₀
    have key' : Zr * ((ν w₀).prod volume).real (p.packet b₀) / (8 * m) ≤
        ((ν w₀).prod volume).real S1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [h2]
    calc Z / (8 * m) * ((ν w₀).prod volume).real (p.packet b₀)
        ≤ Zr / (8 * m) * ((ν w₀).prod volume).real (p.packet b₀) := by
          gcongr
      _ = Zr * ((ν w₀).prod volume).real (p.packet b₀) / (8 * m) := by ring
      _ ≤ _ := key'
  · -- the success floor
    rw [hslD, hslP] at hfl2
    have hω' : 0 < Zr⁻¹ * ω w₀ := by positivity
    have e : (1 - 1 / 2) / 4 * (Zr⁻¹ * ω w₀ * ((ν w₀).prod volume).real (S0 w₀ ∩
        {x | p.history m (level i) (w₀, x) = some b₀})) =
        (Zr⁻¹ * ω w₀) * ((ν w₀).prod volume).real (S0 w₀ ∩
          {x | p.history m (level i) (w₀, x) = some b₀}) / 8 := by ring
    rw [e] at hfl2
    have h8 : (Zr⁻¹ * ω w₀) * ((ν w₀).prod volume).real (S0 w₀ ∩
        {x | p.history m (level i) (w₀, x) = some b₀}) ≤
        (Zr⁻¹ * ω w₀) * (8 * ((ν w₀).prod volume).real S1) := by linarith
    exact le_of_mul_le_mul_left h8 hω'
  · -- the numerator
    intro h z
    have hnum' : ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
        μ₀.real ({y | (p.history m (level (i + 1)) y, worldBin δv y) = (h, z)} ∩
            {y | p.history m (level i) y = some b₀} ∩ D) ≤
          winBase Rv δv J ^ (1 / 2 : ℝ) * μ₀.real ({y | p.history m (level (i + 1)) y = h} ∩
              {y | p.history m (level i) y = some b₀}) *
            μ₀.real ({y | worldBin δv y = z} ∩ {y | p.history m (level i) y = some b₀}) /
            μ₀.real {y | p.history m (level i) y = some b₀} := hnum
    have := numerator_original hp hν hω0 hω1 S0 hS0m hS0t hpos hω₀ hD
      δv (winBase Rv δv J ^ (1 / 2 : ℝ)) hnum' h z
    exact this

end

end

end Submission.Obl.k4_finite_affine_parent_sources
