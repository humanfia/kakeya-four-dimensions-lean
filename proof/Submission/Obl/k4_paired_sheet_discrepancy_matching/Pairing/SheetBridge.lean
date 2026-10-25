/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SheetBridge.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/SheetBridge.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DiscrepancyGroups
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.PolynomialSheets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingCoordinates
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.BallNet
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.LocalPairAssembly

/-! Sheets of normalized quadratic equations on grid balls, in the matching coordinates. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric MeasureTheory MvPolynomial

/-- The sign selecting the nearest real sheet. -/
noncomputable def sgn (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

lemma sgn_sq (r : ℝ) : sgn r ^ 2 = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_mul_self (r : ℝ) : sgn r * r = |r| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

lemma emb_sub' (x y : EuclideanSpace ℝ (Fin 3)) : emb x - emb y = emb (x - y) := by
  ext i
  change (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ)
  push_cast
  ring

/-- Positive real part of the complexified discriminant on the complex ball of radius `8 r`. -/
def DiscPosOn (P : MvPolynomial (Fin 4) ℝ) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) : Prop :=
  ∀ ζ ∈ ball (emb c) (8 * r),
    0 < (eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ))).re

/-- The matching-coordinate sheet of `P` at the grid center `c`, radius `r`, sign `σ`. -/
noncomputable def matchSheet (P : MvPolynomial (Fin 4) ℝ) (c : EuclideanSpace ℝ (Fin 3))
    (r σ : ℝ) : EuclideanSpace ℂ (Fin 3) → ℂ := by
  classical
  exact if DiscPosOn P c r then
    (fun ζ => simpleSheet P σ (emb c + ((2 * r : ℝ) : ℂ) • ζ)) else fun _ => 0

lemma isMatchSheet_zero : IsMatchSheet (fun _ => (0 : ℂ)) := by
  refine ⟨⟨MvPolynomial.X 3, MvPolynomial.X_ne_zero 3, ?_, ?_⟩, differentiableOn_const 0, ?_⟩
  · rw [MvPolynomial.totalDegree_X]; norm_num
  · intro z _
    rw [MvPolynomial.eval_X]
    exact Fin.snoc_last (α := fun _ => ℂ) _ _
  · intro x _
    simp

lemma disc_ne_zero_of_discPosOn {P : MvPolynomial (Fin 4) ℝ} {c : EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} (hr : 0 < r) (h : DiscPosOn P c r) : P ≠ 0 := by
  intro hP
  have := h (emb c) (mem_ball_self (by positivity))
  subst hP
  simp [disc] at this

lemma matchSheet_isMatchSheet {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (c : EuclideanSpace ℝ (Fin 3)) {r σ : ℝ} (hr : 0 < r) (hσ : σ ^ 2 = 1) :
    IsMatchSheet (matchSheet P c r σ) := by
  classical
  unfold matchSheet
  split_ifs with hpos
  · obtain ⟨hF, hroot, hreal⟩ := simpleSheet_spec P hP σ hσ _ hpos
    have hP0 : P ≠ 0 := disc_ne_zero_of_discPosOn hr hpos
    have hmap0 : P.map (algebraMap ℝ ℂ) ≠ 0 := by
      intro h
      apply hP0
      have hinj : Function.Injective (MvPolynomial.map (σ := Fin 4) (algebraMap ℝ ℂ)) :=
        MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℝ ℂ)
      apply hinj
      rw [h, map_zero]
    have hdeg : (P.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 :=
      (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hP
    apply local_sheet_isMatchSheet (P.map (algebraMap ℝ ℂ)) hmap0 hdeg (simpleSheet P σ) c hr hF
    · intro z hz; exact (hroot z hz).1
    · intro x hx
      apply hreal
      rw [mem_ball, dist_eq_norm, emb_sub', norm_emb]
      exact mem_ball_iff_norm.mp hx
  · exact isMatchSheet_zero

lemma emb_sub (x y : EuclideanSpace ℝ (Fin 3)) : emb x - emb y = emb (x - y) := by
  ext i
  change (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ)
  push_cast
  ring

lemma emb_add_smul (c x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    emb c + ((2 * r : ℝ) : ℂ) • emb x = emb (c + (2 * r) • x) := by
  ext i
  change (c i : ℂ) + ((2 * r : ℝ) : ℂ) * (x i : ℂ) = ((c i + (2 * r) * x i : ℝ) : ℂ)
  push_cast
  ring

/-- On a positive-discriminant ball, the matching sheet evaluates the simple sheet. -/
lemma matchSheet_emb {P : MvPolynomial (Fin 4) ℝ} {c : EuclideanSpace ℝ (Fin 3)} {r σ : ℝ}
    (hpos : DiscPosOn P c r) (x : EuclideanSpace ℝ (Fin 3)) :
    matchSheet P c r σ (emb x) = simpleSheet P σ (emb (c + (2 * r) • x)) := by
  classical
  unfold matchSheet
  rw [ite_eq_left_iff.mpr (fun h => absurd hpos h), emb_add_smul]

/-- Real discriminant positivity at a point of the ball. -/
lemma disc_pos_of_discPosOn {P : MvPolynomial (Fin 4) ℝ} {c z : EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} (hpos : DiscPosOn P c r) (hz : ‖z - c‖ < 8 * r) :
    0 < eval (fun i => z i) (disc P) := by
  have h := hpos (emb z) (by rw [mem_ball, dist_eq_norm, emb_sub', norm_emb]; exact hz)
  have hev : eval (fun i => (emb z) i) ((disc P).map (algebraMap ℝ ℂ)) =
      ((eval (fun i => z i) (disc P) : ℝ) : ℂ) :=
    eval_complexification (disc P) (fun i => z i)
  rw [hev, Complex.ofReal_re] at h
  exact h

/-- Near-source bound for the matching sheet with the derivative sign. -/
lemma matchSheet_near {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    {c z : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : 0 < r) (hpos : DiscPosOn P c r)
    (hz : ‖z - c‖ < 8 * r) (w : ℝ)
    (hne : eval (Fin.snoc (fun i : Fin 3 => z i) w) (pderiv (3 : Fin 4) P) ≠ 0) :
    ‖matchSheet P c r (sgn (eval (Fin.snoc (fun i : Fin 3 => z i) w) (pderiv (3 : Fin 4) P)))
        (emb ((2 * r)⁻¹ • (z - c))) - (w : ℂ)‖ ≤
      2 * |eval (Fin.snoc (fun i : Fin 3 => z i) w) P| /
        |eval (Fin.snoc (fun i : Fin 3 => z i) w) (pderiv (3 : Fin 4) P)| := by
  rw [matchSheet_emb hpos]
  have hcz : c + (2 * r) • ((2 * r)⁻¹ • (z - c)) = z := by
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel]
  rw [hcz]
  exact simpleSheet_error P hP _ (sgn_sq _) z w (disc_pos_of_discPosOn hpos hz).le hne
    (sgn_mul_self _)

lemma volume_affine_preimage (c : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r)
    (U : Set (EuclideanSpace ℝ (Fin 3))) :
    volume {z : EuclideanSpace ℝ (Fin 3) | r⁻¹ • (z - c) ∈ U} =
      ENNReal.ofReal (r ^ 3) * volume U := by
  have h1 : {z : EuclideanSpace ℝ (Fin 3) | r⁻¹ • (z - c) ∈ U} =
      (fun z => z + (-c)) ⁻¹' ((fun y => r⁻¹ • y) ⁻¹' U) := by
    ext z; simp [sub_eq_add_neg]
  rw [h1, measure_preimage_add_right, Measure.addHaar_preimage_smul volume (inv_ne_zero hr.ne')]
  simp [finrank_euclideanSpace, abs_of_pos hr]

lemma measurable_eval_snoc (Q : MvPolynomial (Fin 4) ℝ) :
    Measurable (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      eval (Fin.snoc (fun i : Fin 3 => q.1 i) q.2) Q) := by
  have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      (Fin.snoc (fun i : Fin 3 => q.1 i) q.2 : Fin 4 → ℝ)) := by
    refine continuous_pi (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact continuous_snd
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
  exact ((MvPolynomial.continuous_eval Q).comp hc).measurable

lemma measurable_eval_snoc_comp {α : Type*} [MeasurableSpace α] (Q : MvPolynomial (Fin 4) ℝ)
    {z : α → EuclideanSpace ℝ (Fin 3)} {w : α → ℝ} (hz : Measurable z) (hw : Measurable w) :
    Measurable (fun p => eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) Q) := by
  have hc : Measurable (fun p => (Fin.snoc (fun i : Fin 3 => z p i) (w p) : Fin 4 → ℝ)) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact hw
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp ((PiLp.continuous_ofLp 2 _).measurable.comp hz)
  exact (MvPolynomial.continuous_eval Q).measurable.comp hc

/-- The sign bit of a real number (irreducible, so that it is never unfolded). -/
@[irreducible] noncomputable def nonnegBool (x : ℝ) : Bool := decide (0 ≤ x)

lemma nonnegBool_eq_true {x : ℝ} : nonnegBool x = true ↔ 0 ≤ x := by
  unfold nonnegBool; simp

lemma nonnegBool_eq_false {x : ℝ} : nonnegBool x = false ↔ ¬ 0 ≤ x := by
  unfold nonnegBool; simp

lemma sign_eq_sgn (x : ℝ) : (if nonnegBool x then (1 : ℝ) else -1) = sgn x := by
  unfold sgn
  by_cases h : 0 ≤ x
  · rw [if_pos (nonnegBool_eq_true.mpr h), if_pos h]
  · rw [if_neg (by rw [nonnegBool_eq_true]; exact h), if_neg h]

/-- Per-pair test data for the sheet bridge: normalized equations, source and witness entries
with a common frame, normalized base points in the radius-`1/8` ball, hidden values, simple
nearest-root tests and positive discriminants on the grid balls, and base densities. -/
structure PairTests (En Fr Ω : Type*) [MeasurableSpace Ω] where
  Pm : Measure Ω
  frameOf : En → Fr
  P : En → MvPolynomial (Fin 4) ℝ
  src : Ω → En
  wit : Ω → En
  z : Ω → EuclideanSpace ℝ (Fin 3)
  w : Ω → ℝ
  h : ℝ
  r : ℝ
  Δ : ℝ
  ρn : Fr → ℝ
  finite : IsFiniteMeasure Pm
  deg : ∀ s, (P s).totalDegree ≤ 2
  src_meas : ∀ s, MeasurableSet {p | src p = s}
  wit_meas : ∀ s, MeasurableSet {p | wit p = s}
  z_meas : Measurable z
  w_meas : Measurable w
  frame_eq : ∀ p, frameOf (src p) = frameOf (wit p)
  z_mem : ∀ p, ‖z p‖ ≤ 1 / 8
  h_pos : 0 < h
  h_le : h ≤ r
  pos_src : ∀ p, DiscPosOn (P (src p)) (gridCenter h (gridLabel h (z p))) r
  pos_wit : ∀ p, DiscPosOn (P (wit p)) (gridCenter h (gridLabel h (z p))) r
  ne_src : ∀ p, eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (pderiv (3 : Fin 4) (P (src p))) ≠ 0
  ne_wit : ∀ p, eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (pderiv (3 : Fin 4) (P (wit p))) ≠ 0
  near_src : ∀ p, 2 * |eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (P (src p))| /
    |eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (pderiv (3 : Fin 4) (P (src p)))| ≤ Δ
  near_wit : ∀ p, 2 * |eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (P (wit p))| /
    |eval (Fin.snoc (fun i : Fin 3 => z p i) (w p)) (pderiv (3 : Fin 4) (P (wit p)))| ≤ Δ
  Δ_pos : 0 < Δ
  ρn_nonneg : ∀ f, 0 ≤ ρn f
  dens_src : ∀ s (V : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet V →
    Pm {p | src p = s ∧ z p ∈ V} ≤ ENNReal.ofReal (ρn (frameOf s)) * volume V
  dens_wit : ∀ s (V : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet V →
    Pm {p | wit p = s ∧ z p ∈ V} ≤ ENNReal.ofReal (ρn (frameOf s)) * volume V

namespace PairTests

variable {En Fr Ω : Type*} [MeasurableSpace Ω] (T : PairTests En Fr Ω)

lemma r_pos : 0 < T.r := lt_of_lt_of_le T.h_pos T.h_le

/-- The grid cell of a pair. -/
noncomputable def cell (p : Ω) : ↥(gridBox T.h (1 / 8)) :=
  ⟨gridLabel T.h (T.z p), gridLabel_mem_gridBox T.h_pos (T.z_mem p)⟩

/-- The grid center of a pair. -/
noncomputable def center (p : Ω) : EuclideanSpace ℝ (Fin 3) := gridCenter T.h (gridLabel T.h (T.z p))

lemma norm_z_sub_center (p : Ω) : ‖T.z p - T.center p‖ ≤ T.h :=
  norm_sub_gridCenter_le T.h_pos (T.z p)

/-- Source sheet label: entry, grid cell, derivative sign. -/
noncomputable def srcLab (p : Ω) : En × ↥(gridBox T.h (1 / 8)) × Bool :=
  (T.src p, T.cell p,
    nonnegBool (eval (Fin.snoc (fun i : Fin 3 => T.z p i) (T.w p)) (pderiv (3 : Fin 4) (T.P (T.src p)))))

/-- Witness sheet label. -/
noncomputable def witLab (p : Ω) : En × ↥(gridBox T.h (1 / 8)) × Bool :=
  (T.wit p, T.cell p,
    nonnegBool (eval (Fin.snoc (fun i : Fin 3 => T.z p i) (T.w p)) (pderiv (3 : Fin 4) (T.P (T.wit p)))))

/-- The sheet of a label, in matching coordinates. -/
noncomputable def sheet (i : En × ↥(gridBox T.h (1 / 8)) × Bool) : EuclideanSpace ℂ (Fin 3) → ℂ :=
  matchSheet (T.P i.1) (gridCenter T.h i.2.1.1) T.r (if i.2.2 then 1 else -1)

/-- The matching coordinates of a pair. -/
noncomputable def xm (p : Ω) : EuclideanSpace ℝ (Fin 3) := (2 * T.r)⁻¹ • (T.z p - T.center p)


lemma measurableSet_lab {f : Ω → En} (hf : ∀ s, MeasurableSet {p | f p = s})
    (i : En × ↥(gridBox T.h (1 / 8)) × Bool) :
    MeasurableSet {p | (f p, T.cell p, nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
      (pderiv (3 : Fin 4) (T.P (f p))))) = i} := by
  obtain ⟨s, n, b⟩ := i
  have hcell : MeasurableSet {p | T.cell p = n} := by
    have : {p | T.cell p = n} = (fun p => gridLabel T.h (T.z p)) ⁻¹' {n.1} := by
      ext p; simp [cell, Subtype.ext_iff]
    rw [this]
    exact ((measurable_gridLabel T.h).comp T.z_meas) (measurableSet_singleton _)
  have hsign : MeasurableSet {p | 0 ≤ eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
      (pderiv (3 : Fin 4) (T.P s))} :=
    measurableSet_le measurable_const (measurable_eval_snoc_comp _ T.z_meas T.w_meas)
  have : {p | (f p, T.cell p, nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
      (pderiv (3 : Fin 4) (T.P (f p))))) = (s, n, b)} =
      {p | f p = s} ∩ {p | T.cell p = n} ∩
        {p | nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
          (pderiv (3 : Fin 4) (T.P s))) = b} := by
    ext p
    constructor
    · intro hp
      have h1 : f p = s := congrArg Prod.fst hp
      have h2 : T.cell p = n := congrArg (fun q => q.2.1) hp
      have h3 := congrArg (fun q => q.2.2) hp
      simp only at h3
      rw [h1] at h3
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      show (f p, T.cell p, _) = (s, n, b)
      rw [h1, h2]
      exact congrArg _ (congrArg _ h3)
  have hsign' : MeasurableSet {p | nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
      (pderiv (3 : Fin 4) (T.P s))) = b} := by
    cases b
    · have : {p | nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
          (pderiv (3 : Fin 4) (T.P s))) = false} = {p | 0 ≤ eval (Fin.snoc (fun j : Fin 3 => T.z p j)
            (T.w p)) (pderiv (3 : Fin 4) (T.P s))}ᶜ := by
        ext p; simp only [mem_setOf_eq, mem_compl_iff, nonnegBool_eq_false]
      rw [this]; exact hsign.compl
    · have : {p | nonnegBool (eval (Fin.snoc (fun j : Fin 3 => T.z p j) (T.w p))
          (pderiv (3 : Fin 4) (T.P s))) = true} = {p | 0 ≤ eval (Fin.snoc (fun j : Fin 3 => T.z p j)
            (T.w p)) (pderiv (3 : Fin 4) (T.P s))} := by
        ext p; simp only [mem_setOf_eq, nonnegBool_eq_true]
      rw [this]; exact hsign
  rw [this]
  exact ((hf s).inter hcell).inter hsign'

/-- The discrepancy setup of the pair tests. -/
noncomputable def toDiscSetup [Fintype En] : DiscSetup (En × ↥(gridBox T.h (1 / 8)) × Bool)
    (Fr × (Fin 3 → ℤ)) Ω where
  Pm := T.Pm
  lab := fun i => (T.frameOf i.1, i.2.1.1)
  φ := T.sheet
  src := T.srcLab
  wit := T.witLab
  x := T.xm
  w := T.w
  Δ := T.Δ
  ρ := fun l => T.ρn l.1 * (2 * T.r) ^ 3
  finite := T.finite
  sheet := fun i => matchSheet_isMatchSheet (T.deg _) _ T.r_pos (by split_ifs <;> norm_num)
  src_meas := fun i => T.measurableSet_lab T.src_meas i
  wit_meas := fun i => T.measurableSet_lab T.wit_meas i
  x_meas := by
    unfold xm center
    exact (T.z_meas.sub (((measurable_of_countable (gridCenter T.h)).comp
      (measurable_gridLabel T.h)).comp T.z_meas)).const_smul ((2 * T.r)⁻¹)
  lab_eq := fun p => by simp [srcLab, witLab, T.frame_eq p]
  x_mem := fun p => by
    have hr := T.r_pos
    unfold xm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 * T.r)⁻¹)]
    calc (2 * T.r)⁻¹ * ‖T.z p - T.center p‖ ≤ (2 * T.r)⁻¹ * T.r :=
          mul_le_mul_of_nonneg_left ((T.norm_z_sub_center p).trans T.h_le) (by positivity)
      _ = 1 / 2 := by field_simp
  Δ_pos := T.Δ_pos
  near_src := fun p => by
    have hr := T.r_pos
    show ‖matchSheet (T.P (T.src p)) (T.center p) T.r
      (if nonnegBool (eval (Fin.snoc (fun i : Fin 3 => T.z p i) (T.w p))
        (pderiv (3 : Fin 4) (T.P (T.src p)))) then 1 else -1)
      (emb ((2 * T.r)⁻¹ • (T.z p - T.center p))) - (T.w p : ℂ)‖ ≤ T.Δ
    rw [sign_eq_sgn]
    have hzc := T.norm_z_sub_center p
    have hhr := T.h_le
    exact (matchSheet_near (T.deg _) hr (T.pos_src p)
      (by unfold center at hzc; linarith) (T.w p) (T.ne_src p)).trans (T.near_src p)
  near_wit := fun p => by
    have hr := T.r_pos
    show ‖matchSheet (T.P (T.wit p)) (T.center p) T.r
      (if nonnegBool (eval (Fin.snoc (fun i : Fin 3 => T.z p i) (T.w p))
        (pderiv (3 : Fin 4) (T.P (T.wit p)))) then 1 else -1)
      (emb ((2 * T.r)⁻¹ • (T.z p - T.center p))) - (T.w p : ℂ)‖ ≤ T.Δ
    rw [sign_eq_sgn]
    have hzc := T.norm_z_sub_center p
    have hhr := T.h_le
    exact (matchSheet_near (T.deg _) hr (T.pos_wit p)
      (by unfold center at hzc; linarith) (T.w p) (T.ne_wit p)).trans (T.near_wit p)
  ρ_nonneg := fun l => mul_nonneg (T.ρn_nonneg _) (by have := T.r_pos; positivity)
  dens_src := fun i U hU => by
    have hr := T.r_pos
    obtain ⟨s, n, b⟩ := i
    set c := gridCenter T.h n.1
    have hV : MeasurableSet {z : EuclideanSpace ℝ (Fin 3) | (2 * T.r)⁻¹ • (z - c) ∈ U} :=
      hU.preimage (by fun_prop)
    calc T.Pm {p | T.srcLab p = (s, n, b) ∧ T.xm p ∈ U}
        ≤ T.Pm {p | T.src p = s ∧ T.z p ∈ {z | (2 * T.r)⁻¹ • (z - c) ∈ U}} := by
          apply measure_mono
          rintro p ⟨hp, hx⟩
          simp only [srcLab, Prod.mk.injEq] at hp
          obtain ⟨hs, hn, -⟩ := hp
          refine ⟨hs, ?_⟩
          simp only [mem_setOf_eq]
          have : T.center p = c := by
            simp only [center, c, ← hn, cell]
          rw [← this]
          exact hx
      _ ≤ ENNReal.ofReal (T.ρn (T.frameOf s)) * volume {z : EuclideanSpace ℝ (Fin 3) |
            (2 * T.r)⁻¹ • (z - c) ∈ U} := T.dens_src s _ hV
      _ = ENNReal.ofReal (T.ρn (T.frameOf s) * (2 * T.r) ^ 3) * volume U := by
          rw [volume_affine_preimage c (by positivity : (0 : ℝ) < 2 * T.r),
            ENNReal.ofReal_mul (T.ρn_nonneg _), mul_assoc]
  dens_wit := fun i U hU => by
    have hr := T.r_pos
    obtain ⟨s, n, b⟩ := i
    set c := gridCenter T.h n.1
    have hV : MeasurableSet {z : EuclideanSpace ℝ (Fin 3) | (2 * T.r)⁻¹ • (z - c) ∈ U} :=
      hU.preimage (by fun_prop)
    calc T.Pm {p | T.witLab p = (s, n, b) ∧ T.xm p ∈ U}
        ≤ T.Pm {p | T.wit p = s ∧ T.z p ∈ {z | (2 * T.r)⁻¹ • (z - c) ∈ U}} := by
          apply measure_mono
          rintro p ⟨hp, hx⟩
          simp only [witLab, Prod.mk.injEq] at hp
          obtain ⟨hs, hn, -⟩ := hp
          refine ⟨hs, ?_⟩
          simp only [mem_setOf_eq]
          have : T.center p = c := by
            simp only [center, c, ← hn, cell]
          rw [← this]
          exact hx
      _ ≤ ENNReal.ofReal (T.ρn (T.frameOf s)) * volume {z : EuclideanSpace ℝ (Fin 3) |
            (2 * T.r)⁻¹ • (z - c) ∈ U} := T.dens_wit s _ hV
      _ = ENNReal.ofReal (T.ρn (T.frameOf s) * (2 * T.r) ^ 3) * volume U := by
          rw [volume_affine_preimage c (by positivity : (0 : ℝ) < 2 * T.r),
            ENNReal.ofReal_mul (T.ρn_nonneg _), mul_assoc]

end PairTests

/-- **Local pairs from the bridge.** Agreement of the two matching sheets on the real half
ball of the grid ball gives the frozen local-pair predicate at any source point of that ball,
once the requested radii fit inside the grid ball. -/
theorem localPair_of_matchSheets {Nk a δv q : ℝ} {P P' : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (hP' : P'.totalDegree ≤ 2)
    {c z₀ : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : 0 < r)
    (hzc : ‖z₀ - c‖ ≤ r / 2) (hrad : 8 * Nk ^ (-a) ≤ 7 * r) (hrad2 : 2 * Nk ^ (-a) ≤ r / 2)
    (hpos : DiscPosOn P c r) (hpos' : DiscPosOn P' c r)
    {σ σ' : ℝ} (hσ : σ ^ 2 = 1) (hσ' : σ' ^ 2 = 1)
    {zline : ℝ → EuclideanSpace ℝ (Fin 3)} {wline : ℝ → ℝ} {t₀ : ℝ} {I : Set ℝ}
    (hD : Nk ^ (-a) ≤ |eval (fun i => z₀ i) (disc P)|)
    (hD' : Nk ^ (-a) ≤ |eval (fun i => z₀ i) (disc P')|)
    (hnear : ‖simpleSheet P σ (emb z₀) - (wline t₀ : ℂ)‖ ≤ δv * Nk ^ a)
    (hnear' : ‖simpleSheet P' σ' (emb z₀) - (wline t₀ : ℂ)‖ ≤ δv * Nk ^ a)
    {M₀ : ℝ} (hM₀ : M₀ ≤ δv * Nk ^ a)
    (hagree : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
      ‖matchSheet P c r σ (emb y) - matchSheet P' c r σ' (emb y)‖ < M₀)
    (hfit : ∀ t ∈ I ∩ Set.Icc (t₀ - Nk ^ (-a) / (100 * q)) (t₀ + Nk ^ (-a) / (100 * q)),
      ‖(wline t : ℂ) - simpleSheet P σ (emb (zline t))‖ ≤ δv * Nk ^ a) :
    localPair Nk a δv q P P' z₀ zline wline t₀ I := by
  have hball : ball (emb z₀) (8 * Nk ^ (-a)) ⊆ ball (emb c) (8 * r) := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm] at hζ ⊢
    have h1 : ‖emb z₀ - emb c‖ ≤ r / 2 := by rw [emb_sub', norm_emb]; exact hzc
    calc ‖ζ - emb c‖ ≤ ‖ζ - emb z₀‖ + ‖emb z₀ - emb c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 8 * Nk ^ (-a) + r / 2 := by linarith
      _ ≤ 8 * r := by linarith
  apply localPair_of_simpleSheets hP hP' hσ hσ' hD hD'
    (fun ζ hζ => hpos ζ (hball hζ)) (fun ζ hζ => hpos' ζ (hball hζ))
  · intro x hx
    rw [mem_ball, dist_eq_norm, emb_sub', norm_emb]
    exact mem_ball_iff_norm.mp hx
  · exact hnear
  · exact hnear'
  · intro z' hz'
    have hz'c : ‖z' - c‖ ≤ r := by
      have := mem_closedBall_iff_norm.mp hz'
      calc ‖z' - c‖ ≤ ‖z' - z₀‖ + ‖z₀ - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ r := by linarith
    set y : EuclideanSpace ℝ (Fin 3) := (2 * r)⁻¹ • (z' - c)
    have hy : ‖y‖ ≤ 1 / 2 := by
      simp only [y, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 * r)⁻¹)]
      calc (2 * r)⁻¹ * ‖z' - c‖ ≤ (2 * r)⁻¹ * r := mul_le_mul_of_nonneg_left hz'c (by positivity)
        _ = 1 / 2 := by field_simp
    have hcy : c + (2 * r) • y = z' := by
      simp only [y, smul_smul, mul_inv_cancel₀ (by positivity : (2 * r) ≠ 0), one_smul,
        add_sub_cancel]
    have h := hagree y hy
    rw [matchSheet_emb hpos, matchSheet_emb hpos', hcy] at h
    exact (le_of_lt h).trans hM₀
  · exact hfit


end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
