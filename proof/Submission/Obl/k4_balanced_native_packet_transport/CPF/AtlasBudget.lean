/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/AtlasBudget.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-! Normalize chart-world weights using the original assigned prior masses.
The time-block length cancels the number of blocks in the total budget. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped ENNReal

theorem incidence_mass_le_dyadic_block (ν : Measure Trajectory)
    (A : Set Trajectory) (F : Set Incidence) (T : ℕ) (j : ℝ)
    (hF : MeasurableSet F)
    (hsub : ∀ p ∈ F, p.1 ∈ A ∧
      p.2 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) :
    (ν.prod volume) F ≤ ((2 : ℝ≥0∞) ^ T)⁻¹ * ν A := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.incidence_mass_le_section_bound
    ν A F _ hF (fun p hp => (hsub p hp).1)
  intro l hl
  calc
    volume {t : ℝ | (l, t) ∈ F} ≤
        volume (Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) :=
      measure_mono (fun t ht => (hsub (l, t) ht).2)
    _ = _ := by
      rw [Real.volume_Icc,
        show (j + 1) / (2 : ℝ) ^ T - j / (2 : ℝ) ^ T = ((2 : ℝ) ^ T)⁻¹ by ring,
        ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]

theorem Chart.incidence_mass_le_assigned
    {Nk κ j r B : ℝ} {M D T : ℕ} {E : Set Incidence} {c u : Spatial}
    {Q : Frame} {R : Test} {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (hchart : Chart Nk M D κ T j r B E c u Q R A F ex) (ν : Measure Trajectory) :
    (ν.prod volume) F ≤ ((2 : ℝ≥0∞) ^ T)⁻¹ * ν A := by
  obtain ⟨_, _, _, _, _, _, _, hF, _, _, hsel, _⟩ := hchart
  exact incidence_mass_le_dyadic_block ν A F T j hF
    (fun p hp => ⟨(hsel p hp).2.1, (hsel p hp).2.2.1⟩)

noncomputable def Atlas.assignedWeight {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    ℝ≥0∞ := ENNReal.ofReal (p.ω k (a.γ b)) * ((2 : ℝ≥0∞) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)

noncomputable def Atlas.budget {p : Data} {k : ℕ} (a : Atlas p k) : ℝ≥0∞ :=
  ∑ b, a.assignedWeight b

theorem Atlas.mass_le_budget_of {p : Data} {k : ℕ} (a : Atlas p k)
    (hF : ∀ b, MeasurableSet (a.F b))
    (hsub : ∀ b p, p ∈ a.F b → p.1 ∈ a.A b ∧
      p.2 ∈ Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T) (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T)) :
    a.mass ≤ a.budget := by
  apply Finset.sum_le_sum
  intro b _
  change ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b) ≤
    ENNReal.ofReal (p.ω k (a.γ b)) * ((2 : ℝ≥0∞) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)
  rw [mul_assoc]
  exact mul_le_mul' le_rfl
    (incidence_mass_le_dyadic_block _ _ _ _ _ (hF b) (hsub b))

theorem Atlas.TrueAt.mass_le_budget {p : Data} {k M D : ℕ} {r : ℝ} {a : Atlas p k}
    (ha : a.TrueAt M D r) : a.mass ≤ a.budget := by
  apply a.mass_le_budget_of
  · intro b
    obtain ⟨_, _, _, _, _, _, _, hF, _⟩ := ha.2.2.1 b
    exact hF
  · intro b p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 b
    exact ⟨(hsel p hp).2.1, (hsel p hp).2.2.1⟩

theorem Atlas.assignment_sum_le_of {p : Data} {k : ℕ} (a : Atlas p k)
    (hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ))
    (hw0 : ∀ γ, 0 ≤ p.ω k γ) (hw : ∑ γ, p.ω k γ = 1)
    (hA : ∀ b, MeasurableSet (a.A b)) (hsep : a.Separated) :
    (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * p.ν k (a.γ b) (a.A b)) ≤
      (2 : ℝ≥0∞) ^ a.T := by
  have h := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    (p.ν k) (p.ω k) a.γ a.j a.A hprob hw0 hw hA hsep
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

theorem Atlas.TrueAt.assignment_sum_le {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) :
    (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * p.ν k (a.γ b) (a.A b)) ≤
      (2 : ℝ≥0∞) ^ a.T := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, htemp, _⟩
  obtain ⟨M₀, D₀, htemp⟩ := htemp
  have hA (b : Fin a.C) : MeasurableSet (a.A b) := by
    obtain ⟨_, _, _, _, _, _, hA, _⟩ := ha.2.2.1 b
    exact hA
  exact a.assignment_sum_le_of (fun γ => ((htemp k).2.2.2.1 γ).1)
    (htemp k).2.1 (htemp k).2.2.1 hA ha.2.1

theorem Atlas.budget_le_one_of {p : Data} {k : ℕ} (a : Atlas p k)
    (hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ))
    (hw0 : ∀ γ, 0 ≤ p.ω k γ) (hw : ∑ γ, p.ω k γ = 1)
    (hA : ∀ b, MeasurableSet (a.A b)) (hsep : a.Separated) : a.budget ≤ 1 := by
  have hfactor : a.budget = ((2 : ℝ≥0∞) ^ a.T)⁻¹ *
      ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * p.ν k (a.γ b) (a.A b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold Atlas.assignedWeight
    ring
  rw [hfactor]
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ a.T)⁻¹ * (2 : ℝ≥0∞) ^ a.T :=
      mul_le_mul' le_rfl (a.assignment_sum_le_of hprob hw0 hw hA hsep)
    _ = 1 := ENNReal.inv_mul_cancel (by positivity) (by finiteness)

theorem Atlas.TrueAt.budget_le_one {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) : a.budget ≤ 1 := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, htemp, _⟩
  obtain ⟨M₀, D₀, htemp⟩ := htemp
  apply a.budget_le_one_of (fun γ => ((htemp k).2.2.2.1 γ).1)
    (htemp k).2.1 (htemp k).2.2.1 _ ha.2.1
  intro b
  obtain ⟨_, _, _, _, _, _, hA, _⟩ := ha.2.2.1 b
  exact hA

theorem Atlas.TrueAt.budget_bounds {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) :
    ENNReal.ofReal a.κ⁻¹ ≤ a.budget ∧ a.budget ≤ 1 :=
  ⟨ha.2.2.2.trans ha.mass_le_budget, ha.budget_le_one hp⟩

theorem Atlas.TrueAt.budget_pos {p : Data} {k M D : ℕ} {r : ℝ} {a : Atlas p k}
    (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) : 0 < a.budget := by
  have hκpos : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hκpos)).trans_le
    (ha.2.2.2.trans ha.mass_le_budget)

theorem Atlas.TrueAt.budget_real_bounds {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) :
    a.budget.toReal ≤ 1 ∧ a.budget.toReal⁻¹ ≤ a.κ := by
  have hκpos : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have htop : a.budget ≠ ⊤ := ne_of_lt ((ha.budget_le_one hp).trans_lt (by simp))
  have hlo : a.κ⁻¹ ≤ a.budget.toReal := by
    simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hκpos.le)] using
      ENNReal.toReal_mono htop (ha.budget_bounds hp).1
  refine ⟨?_, ?_⟩
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ha.budget_le_one hp)
  · simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hκpos) hlo

/-- Each actual true chart has nonzero assigned prior mass. -/
theorem Atlas.TrueAt.prior_mass_pos {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ)
    (b : Fin a.C) : 0 < p.ν k (a.γ b) (a.A b) := by
  have hκpos : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hNpos : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hchart := ha.2.2.1 b
  have hbound := hchart.incidence_mass_le_assigned (p.ν k (a.γ b))
  obtain ⟨hdet, _, _, _, _, _, _, _, _, _, _, hfloor⟩ := hchart
  have hpositive : 0 < ENNReal.ofReal
      (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * a.κ)) := by
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hNpos _) (abs_pos.mpr hdet))
      (mul_pos (by positivity) hκpos)
  have hmasspos := hpositive.trans_le hfloor
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at hbound
  exact (not_le_of_gt hmasspos) hbound

noncomputable def Atlas.normalizedWeight {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    ℝ := (a.assignedWeight b / a.budget).toReal

theorem Atlas.normalized_weights_of {p : Data} {k : ℕ} (a : Atlas p k)
    (hpos : 0 < a.budget) (htop : a.budget ≠ ⊤) :
    (∀ b, 0 ≤ a.normalizedWeight b) ∧ (∑ b, a.normalizedWeight b) = 1 ∧
      ∀ b, ENNReal.ofReal (a.normalizedWeight b) = a.assignedWeight b / a.budget := by
  have hassigned (b : Fin a.C) : a.assignedWeight b ≠ ⊤ := by
    apply ne_of_lt
    apply (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ b)).trans_lt
    exact lt_top_iff_ne_top.mpr htop
  have hdiv (b : Fin a.C) : a.assignedWeight b / a.budget ≠ ⊤ :=
    ENNReal.div_ne_top (hassigned b) hpos.ne'
  have hsum : (∑ b, a.assignedWeight b / a.budget) = 1 := by
    rw [← ENNReal.sum_div]
    exact ENNReal.div_self hpos.ne' htop
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_, fun b => ENNReal.ofReal_toReal (hdiv b)⟩
  calc
    _ = (∑ b, a.assignedWeight b / a.budget).toReal :=
      (ENNReal.toReal_sum (fun b _ => hdiv b)).symm
    _ = 1 := by rw [hsum]; simp

theorem Atlas.TrueAt.normalized_weights {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) :
    (∀ b, 0 ≤ a.normalizedWeight b) ∧ (∑ b, a.normalizedWeight b) = 1 ∧
      ∀ b, ENNReal.ofReal (a.normalizedWeight b) = a.assignedWeight b / a.budget :=
  a.normalized_weights_of (ha.budget_pos hκ)
    (ne_of_lt ((ha.budget_le_one hp).trans_lt (by simp)))

/-- The conditional-prior factors cancel against the original assigned weights.
Thus the normalized mixture mass is the original weighted mass divided by the
single retained budget, rather than by a different mass for each chart. -/
theorem Atlas.normalized_mass_formula_of {p : Data} {k : ℕ} (a : Atlas p k)
    (hpos : 0 < a.budget) (htop : a.budget ≠ ⊤)
    (hprior : ∀ b, 0 < p.ν k (a.γ b) (a.A b))
    (hfinite : ∀ b, p.ν k (a.γ b) (a.A b) ≠ ⊤)
    (mass : Fin a.C → ℝ≥0∞) :
    (∑ b, ENNReal.ofReal (a.normalizedWeight b) *
      ((((2 : ℝ≥0∞) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b))⁻¹ * mass b)) =
      (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * mass b) / a.budget := by
  have hweight := (a.normalized_weights_of hpos htop).2.2
  let v (b : Fin a.C) := ((2 : ℝ≥0∞) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)
  have hv0 (b : Fin a.C) : v b ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness)) (hprior b).ne'
  have hvtop (b : Fin a.C) : v b ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity)) (hfinite b)
  have hassign (b : Fin a.C) : a.assignedWeight b = ENNReal.ofReal (p.ω k (a.γ b)) * v b := by
    exact mul_assoc _ _ _
  rw [ENNReal.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [hweight, hassign, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = (v b * (v b)⁻¹) *
        (ENNReal.ofReal (p.ω k (a.γ b)) * mass b * a.budget⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (hv0 b) (hvtop b), one_mul]

theorem Atlas.TrueAt.normalized_mass_formula {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ)
    (mass : Fin a.C → ℝ≥0∞) :
    (∑ b, ENNReal.ofReal (a.normalizedWeight b) *
      ((((2 : ℝ≥0∞) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b))⁻¹ * mass b)) =
      (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * mass b) / a.budget := by
  apply a.normalized_mass_formula_of (ha.budget_pos hκ)
    (ne_of_lt ((ha.budget_le_one hp).trans_lt (by simp))) (ha.prior_mass_pos hp hκ) _ mass
  rcases hp with ⟨_, _, _, _, _, _, _, _, htemp, _⟩
  obtain ⟨M₀, D₀, htemp⟩ := htemp
  intro b
  letI := ((htemp k).2.2.2.1 (a.γ b)).1
  exact measure_ne_top _ _

end Submission.Obl.k4_balanced_native_packet_transport.CPF
