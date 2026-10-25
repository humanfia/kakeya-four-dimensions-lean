import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphGeometry
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.BadCells
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.BadMass

set_option linter.unusedVariables false

/-!
# Pieces of the physical velocity graph for the frozen data

`volume_cellSet` (cubes have volume `w³`), `physIn` (the physical map sending incidences outside a
set to a far point outside all cubes of nonnegative time index), `light_deletion` (removing the
light cubes costs at most their threshold times the number of occupied cubes), and
`good_cell_graph` (a plane capturing more than `1 - c` of a cube's unit lifted directions, with
velocity breadth, gives one bounded row `(G₀, G₁)` with `|x' - G₀ - G₁ V| ≤ 2 ε (1+4H) D` on the
captured incidences, `D = (3H+1)(6H/δ+1)`).
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Submission.Lib.K4ContinuousKakeya
open scoped ENNReal NNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma cellSet_eq_preimage {w : ℝ} (hw : 0 < w) (q : Fin 3 → ℤ) :
    cellSet w q = (WithLp.ofLp : E3 → Fin 3 → ℝ) ⁻¹'
      Set.univ.pi (fun e => Set.Ico ((q e : ℝ) * w) ((q e + 1) * w)) := by
  ext x
  rw [mem_cellSet_iff hw]
  simp [Set.mem_univ_pi]

lemma volume_cellSet {w : ℝ} (hw : 0 < w) (q : Fin 3 → ℤ) :
    volume (cellSet w q) = ENNReal.ofReal w ^ 3 := by
  rw [cellSet_eq_preimage hw, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun e => measurableSet_Ico)).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [Fin.prod_univ_three]
  have : ∀ e : Fin 3, ((q e : ℝ) + 1) * w - (q e : ℝ) * w = w := fun e => by ring
  simp only [this]
  ring

/-- The far point, outside every cube of nonnegative time index. -/
def farPt : E3 := WithLp.toLp 2 ![-1, 0, 0]

lemma farPt_not_mem_cellSet {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} (hq : 0 ≤ q 0) :
    farPt ∉ cellSet w q := by
  intro h
  have := ((mem_cellSet_iff hw).mp h 0).1
  simp [farPt] at this
  have h0 : (0 : ℝ) ≤ (q 0 : ℝ) * w := mul_nonneg (by exact_mod_cast hq) hw.le
  linarith

/-- The physical map restricted to `E`: incidences outside `E` go to the far point. -/
def physIn (E : Set Inc) (p : Inc) : E3 := by
  classical exact if p ∈ E then physOf p else farPt

lemma measurable_physIn {E : Set Inc} (hE : MeasurableSet E) : Measurable (physIn E) := by
  classical
  unfold physIn
  exact Measurable.ite hE continuous_physOf.measurable measurable_const

lemma physIn_mem_cellSet {E : Set Inc} {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} (hq : 0 ≤ q 0)
    {p : Inc} (h : physIn E p ∈ cellSet w q) : p ∈ E ∧ physOf p ∈ cellSet w q := by
  classical
  unfold physIn at h
  split_ifs at h with hp
  · exact ⟨hp, h⟩
  · exact absurd h (farPt_not_mem_cellSet hw hq)

lemma measurableSet_preimage_cellIdx (w : ℝ) (S : Set (Fin 3 → ℤ)) :
    MeasurableSet {p : Inc | cellIdx w (physOf p) ∈ S} :=
  ((measurable_cellIdx w).comp continuous_physOf.measurable) (S.to_countable.measurableSet)

/-- The heavy cubes of side `w`: `ρ|E₀`-mass at least `λ`. -/
def heavyCells (ρ : Measure Inc) (E₀ : Set Inc) (w lam : ℝ) : Set (Fin 3 → ℤ) :=
  {q | ENNReal.ofReal lam ≤ ρ.restrict E₀ {p | cellIdx w (physOf p) = q}}

/-- **Light-cell deletion.** Removing the incidences of the cubes of side `w` whose
`ρ|E₀`-mass is below `λ` costs at most `λ` times the number of occupied cubes. -/
lemma light_deletion (ρ : Measure Inc) {E₀ : Set Inc}
    (hE₀ : MeasurableSet E₀) (w lam : ℝ) (Occ : Finset (Fin 3 → ℤ))
    (hOcc : ∀ q, ρ.restrict E₀ {p | cellIdx w (physOf p) = q} ≠ 0 → q ∈ Occ) :
    ρ (E₀ \ (E₀ ∩ {p | cellIdx w (physOf p) ∈ heavyCells ρ E₀ w lam})) ≤
      Occ.card * ENNReal.ofReal lam := by
  classical
  have hcell : ∀ q, MeasurableSet {p : Inc | cellIdx w (physOf p) = q} := fun q =>
    measurableSet_preimage_cellIdx w {q} |>.congr (by ext p; simp)
  have hsub : E₀ \ (E₀ ∩ {p | cellIdx w (physOf p) ∈ heavyCells ρ E₀ w lam}) ⊆
      (⋃ q ∈ Occ.filter (fun q => q ∉ heavyCells ρ E₀ w lam), E₀ ∩ {p | cellIdx w (physOf p) = q}) ∪
      ⋃ q : {q : Fin 3 → ℤ // q ∉ Occ}, E₀ ∩ {p | cellIdx w (physOf p) = q.1} := by
    intro p ⟨hp0, hp1⟩
    have hlight : cellIdx w (physOf p) ∉ heavyCells ρ E₀ w lam := fun hh => hp1 ⟨hp0, hh⟩
    by_cases hocc : cellIdx w (physOf p) ∈ Occ
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨_, Finset.mem_filter.mpr ⟨hocc, hlight⟩, hp0, rfl⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨_, hocc⟩, hp0, rfl⟩)
  have hnull : ρ (⋃ q : {q : Fin 3 → ℤ // q ∉ Occ}, E₀ ∩ {p | cellIdx w (physOf p) = q.1}) = 0 := by
    apply measure_iUnion_null
    intro q
    by_contra h
    apply q.2
    apply hOcc
    rwa [Measure.restrict_apply (hcell q.1), Set.inter_comm]
  calc ρ (E₀ \ (E₀ ∩ {p | cellIdx w (physOf p) ∈ heavyCells ρ E₀ w lam}))
      ≤ ρ (⋃ q ∈ Occ.filter (fun q => q ∉ heavyCells ρ E₀ w lam),
          E₀ ∩ {p | cellIdx w (physOf p) = q}) + 0 := by
        rw [← hnull]; exact (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ∑ q ∈ Occ.filter (fun q => q ∉ heavyCells ρ E₀ w lam),
          ρ (E₀ ∩ {p | cellIdx w (physOf p) = q}) := by
        rw [add_zero]; exact measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Occ.filter (fun q => q ∉ heavyCells ρ E₀ w lam), ENNReal.ofReal lam := by
        apply Finset.sum_le_sum
        intro q hq
        have hl := (Finset.mem_filter.mp hq).2
        simp only [heavyCells, Set.mem_ofPred_eq, not_le] at hl
        rw [Measure.restrict_apply (hcell q), Set.inter_comm] at hl
        exact hl.le
    _ ≤ Occ.card * ENNReal.ofReal lam := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact Finset.filter_subset _ _

lemma liftOf_apply (p : Inc) (e : Fin 3) :
    liftOf p e = (![1, p.1.2 1, p.1.2 3 + 2 * p.1.2 4 * p.2] : Fin 3 → ℝ) e := by
  fin_cases e <;> simp [liftOf, liftVel]

lemma norm_liftOf_le {H : ℝ} {p : Inc} (hH : ∀ e, |p.1.2 e| ≤ H) (ht : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    ‖liftOf p‖ ≤ 1 + 4 * H := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  have hX : |p.1.2 3 + 2 * p.1.2 4 * p.2| ≤ 3 * H := by
    have h3 := hH 3; have h4 := hH 4
    calc |p.1.2 3 + 2 * p.1.2 4 * p.2| ≤ |p.1.2 3| + 2 * |p.1.2 4| * |p.2| := by
          have := abs_add_le (p.1.2 3) (2 * p.1.2 4 * p.2)
          rw [abs_mul, abs_mul, abs_two] at this; exact this
      _ ≤ H + 2 * H * 1 := by
          have : |p.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
          nlinarith [abs_nonneg (p.1.2 4), abs_nonneg p.2]
      _ = 3 * H := by ring
  calc ‖liftOf p‖ ≤ |liftOf p 0| + |liftOf p 1| + |liftOf p 2| := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
        simp only [Real.norm_eq_abs, sq_abs]
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [abs_nonneg (liftOf p 0), abs_nonneg (liftOf p 1), abs_nonneg (liftOf p 2),
          sq_abs (liftOf p 0), sq_abs (liftOf p 1), sq_abs (liftOf p 2)]
    _ ≤ 1 + H + 3 * H := by
        simp only [liftOf_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, abs_one]
        linarith [hH 1]
    _ = 1 + 4 * H := by ring

lemma inner_liftOf (ν : E3) (p : Inc) :
    inner ℝ ν (liftOf p) = ν 0 + ν 1 * p.1.2 1 + ν 2 * (p.1.2 3 + 2 * p.1.2 4 * p.2) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three, liftOf_apply]
  ring

lemma one_le_norm_liftOf (p : Inc) : 1 ≤ ‖liftOf p‖ := one_le_norm_liftVel _ _ _ _

lemma inner_liftOf_eq (ν : E3) (p : Inc) :
    inner ℝ ν (liftOf p) = ‖liftOf p‖ * inner ℝ ν (unitOf p) := by
  have h : ‖liftOf p‖ ≠ 0 := (lt_of_lt_of_le one_pos (one_le_norm_liftOf p)).ne'
  rw [unitOf, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- **A good cell is a bounded graph.** If a plane (unit normal `ν`) captures, within `ε`, more
than `(1 - c)` of the unit lifted directions of the incidences of a cell `X` (all with
coefficients `≤ H` and times in `[0, 1]`), and every `δ`-window of velocities carries at most
`(1 - c)` of the cell, then one bounded row `(G₀, G₁)` satisfies
`|x_l'(t) - G₀ - G₁ V_l| ≤ 2 ε (1 + 4H) (3H + 1)(6H/δ + 1)` on all captured incidences. -/
theorem good_cell_graph (inc : Measure Inc) {X : Set Inc} (hX : MeasurableSet X)
    {H ε c δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) (hXH : ∀ p ∈ X, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ e, |p.1.2 e| ≤ H)
    (ν : E3) (hν : ‖ν‖ = 1)
    (hcap : ENNReal.ofReal (1 - c) * inc X <
      inc {p | p ∈ X ∧ |inner ℝ ν (unitOf p)| < ε})
    (hwin : ∀ v₀ : ℝ, inc {p | p ∈ X ∧ |p.1.2 1 - v₀| < δ} ≤ ENNReal.ofReal (1 - c) * inc X)
    (hsmall : ε * (1 + 4 * H) * (1 + 2 * (3 * H + 1) / δ) ≤ 1 / 2) :
    ∃ G₀ G₁ : ℝ, |G₀| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
      |G₁| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
      ∀ p, p ∈ X → |inner ℝ ν (unitOf p)| < ε →
        |(p.1.2 3 + 2 * p.1.2 4 * p.2) - G₀ - G₁ * p.1.2 1| ≤
          ε * (1 + 4 * H) * (2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1))) := by
  classical
  set Cap : Set Inc := {p | p ∈ X ∧ |inner ℝ ν (unitOf p)| < ε} with hCap
  -- a captured incidence
  have hCapne : Cap.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hcap
    exact (not_lt.mpr zero_le) hcap
  obtain ⟨p₁, hp₁X, hp₁⟩ := hCapne
  -- a second one with a separated velocity
  have hsep : ∃ p₂ ∈ Cap, δ ≤ |p₁.1.2 1 - p₂.1.2 1| := by
    by_contra h
    simp only [not_exists, not_and, not_le] at h
    have hsub : Cap ⊆ {p | p ∈ X ∧ |p.1.2 1 - p₁.1.2 1| < δ} := by
      intro p hp
      refine ⟨hp.1, ?_⟩
      have := h p hp
      rwa [abs_sub_comm] at this
    have := (measure_mono hsub).trans (hwin (p₁.1.2 1))
    exact absurd hcap (not_lt.mpr this)
  obtain ⟨p₂, ⟨hp₂X, hp₂⟩, hδ₁₂⟩ := hsep
  -- the plane condition in coordinates
  set ε' : ℝ := ε * (1 + 4 * H) with hε'
  have hcoord : ∀ p ∈ X, |inner ℝ ν (unitOf p)| < ε →
      |ν 0 + ν 1 * p.1.2 1 + ν 2 * (p.1.2 3 + 2 * p.1.2 4 * p.2)| ≤ ε' := by
    intro p hp hpε
    rw [← inner_liftOf, inner_liftOf_eq, abs_mul, abs_norm, hε']
    have hn := norm_liftOf_le (hXH p hp).2 (hXH p hp).1
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hpε.le
    calc ‖liftOf p‖ * |inner ℝ ν (unitOf p)| ≤ (1 + 4 * H) * ε :=
          mul_le_mul hn hpε.le (abs_nonneg _) (by linarith)
      _ = ε * (1 + 4 * H) := by ring
  have hν2 : ν 0 ^ 2 + ν 1 ^ 2 + ν 2 ^ 2 = 1 := by
    have := hν
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three] at this
    simp only [Real.norm_eq_abs, sq_abs] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [Real.sq_sqrt (by positivity)] at h2
    exact h2
  have hXb : ∀ p ∈ X, |p.1.2 3 + 2 * p.1.2 4 * p.2| ≤ 3 * H := by
    intro p hp
    have ht := (hXH p hp).1; have h3 := (hXH p hp).2 3; have h4 := (hXH p hp).2 4
    calc |p.1.2 3 + 2 * p.1.2 4 * p.2| ≤ |p.1.2 3| + 2 * |p.1.2 4| * |p.2| := by
          have := abs_add_le (p.1.2 3) (2 * p.1.2 4 * p.2)
          rw [abs_mul, abs_mul, abs_two] at this; exact this
      _ ≤ H + 2 * H * 1 := by
          have : |p.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
          nlinarith [abs_nonneg (p.1.2 4), abs_nonneg p.2]
      _ = 3 * H := by ring
  have hlow := normal_hidden_lower (K := 3 * H) hν2 (by linarith) hδ
    (by have := (hXH p₁ hp₁X).2 1; linarith) (hXb p₁ hp₁X) (hXb p₂ hp₂X) hδ₁₂
    (hcoord p₁ hp₁X hp₁) (hcoord p₂ hp₂X hp₂) (by rw [hε']; nlinarith)
  set D : ℝ := 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) with hD
  have hDpos : 0 < D := by positivity
  have hν2pos : 0 < |ν 2| := lt_of_lt_of_le (by positivity) hlow
  have hinv : 1 / |ν 2| ≤ D := by
    have h1 : 1 / D ≤ |ν 2| := by rw [hD]; exact hlow
    have h2 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / D) h1
    rwa [one_div_one_div] at h2
  have hcomp : ∀ i : Fin 3, |ν i| ≤ 1 := fun i => by
    have := PiLp.norm_apply_le ν i
    rwa [hν, Real.norm_eq_abs] at this
  refine ⟨-ν 0 / ν 2, -ν 1 / ν 2, ?_, ?_, ?_⟩
  · rw [abs_div, abs_neg]
    calc |ν 0| / |ν 2| ≤ 1 / |ν 2| := div_le_div_of_nonneg_right (hcomp 0) (abs_nonneg _)
      _ ≤ D := hinv
  · rw [abs_div, abs_neg]
    calc |ν 1| / |ν 2| ≤ 1 / |ν 2| := div_le_div_of_nonneg_right (hcomp 1) (abs_nonneg _)
      _ ≤ D := hinv
  · intro p hp hpε
    have hres := graph_residual_of_normal (abs_pos.mp hν2pos) (hcoord p hp hpε)
    have hε'0 : 0 ≤ ε' := le_trans (abs_nonneg _) (hcoord p hp hpε)
    calc |(p.1.2 3 + 2 * p.1.2 4 * p.2) - -ν 0 / ν 2 - -ν 1 / ν 2 * p.1.2 1|
        ≤ ε' / |ν 2| := hres
      _ = ε' * (1 / |ν 2|) := by ring
      _ ≤ ε' * D := mul_le_mul_of_nonneg_left hinv hε'0

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
