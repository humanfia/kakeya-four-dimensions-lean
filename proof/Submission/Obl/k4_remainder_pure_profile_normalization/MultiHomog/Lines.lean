/-
Adapted from this LOT tree, o147, session x0502, commit 373d234,
Submission/Obl/k4_local_remainder_horizon_transfer/Homogenize/Lines.lean
(that session's own code).
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Encode
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Transport
import Submission.Obl.k4_joint_homogenization.Interface

/-!
# Encoded lines and their observations

The encoded trajectory of world `γ`, and the identity relating the single-world
observation of o075 at a shifted depth to the observation of the world at depth `s`
with derivative scale `B`: the hidden bins agree exactly, the base point is moved by
`baseMap`, and the unit velocity label is constant.

-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set
open scoped ENNReal

/-- The encoded trajectory of world `γ`. -/
noncomputable def encLine (W : ℕ) (γ : Fin W) (a b θ o : ℝ) (l : Trajectory) : Trajectory :=
  (encIdx W γ l.1, encCoeff a b θ o l.2)

theorem measurable_encLine (W : ℕ) (γ : Fin W) (a b θ o : ℝ) :
    Measurable (encLine W γ a b θ o) := by
  unfold encLine
  exact ((measurable_from_top (f := encIdx W γ)).comp measurable_fst).prodMk
    ((continuous_encCoeff a b θ o).measurable.comp measurable_snd)

theorem encLine_injective {W : ℕ} {γ : Fin W} {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hθ : θ ≠ 0) (o : ℝ) : Function.Injective (encLine W γ a b θ o) := by
  intro l l' h
  simp only [encLine, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext (encIdx_inj h1).2 ?_
  have := congrArg (decCoeff a b θ o) h2
  rwa [decCoeff_encCoeff ha hb hθ, decCoeff_encCoeff ha hb hθ] at this

/-- The base observation of an incidence: `(t, y₁(t), y₂(t))`. -/
def baseObs (p : Incidence) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2]

theorem obs_fst (B a : ℝ) (p : Incidence) : (obs B a p).1 = baseObs p := rfl

/-- The label map from an observation of world `γ` to the joint observation of the encoded
single world. -/
noncomputable def encObs (a b o : ℝ) (q : Observation) : JointObservation :=
  ((baseMap a b o q.1, q.2), (0 : Fin 2 → ℤ))

theorem measurable_encObs (a b o : ℝ) : Measurable (encObs a b o) := by
  unfold encObs
  exact (((continuous_baseMap a b o).measurable.comp measurable_fst).prodMk
    measurable_snd).prodMk measurable_const

theorem encObs_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ) :
    Function.Injective (encObs a b o) := by
  intro q q' h
  simp only [encObs, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  refine Prod.ext ?_ h2
  have := congrArg (baseInv a b o) h1
  rwa [baseInv_baseMap ha hb, baseInv_baseMap ha hb] at this

/-! ## Depths -/

/-- The depth of the single world whose dyadic width is `δ n s₀ * δ n s`. -/
noncomputable def depthSum (n s₀ s : ℝ) : ℝ :=
  ((⌊s₀ * Real.log n / Real.log 2⌋ + ⌊s * Real.log n / Real.log 2⌋ : ℤ) : ℝ) /
    (Real.log n / Real.log 2)

theorem log_ratio_pos {n : ℝ} (hn : 1 < n) : 0 < Real.log n / Real.log 2 :=
  div_pos (Real.log_pos hn) (Real.log_pos one_lt_two)

theorem depthSum_mul {n : ℝ} (hn : 1 < n) (s₀ s : ℝ) :
    depthSum n s₀ s * Real.log n / Real.log 2 =
      ((⌊s₀ * Real.log n / Real.log 2⌋ + ⌊s * Real.log n / Real.log 2⌋ : ℤ) : ℝ) := by
  have h := (log_ratio_pos hn).ne'
  unfold depthSum
  rw [mul_div_assoc, div_mul_cancel₀ _ h]

theorem δ_depthSum {n : ℝ} (hn : 1 < n) (s₀ s : ℝ) :
    δ n (depthSum n s₀ s) = δ n s₀ * δ n s := by
  unfold δ
  rw [depthSum_mul hn, Int.floor_intCast, neg_add, zpow_add₀ two_ne_zero]

theorem depthSum_le {n : ℝ} (hn : 1 < n) (s₀ s : ℝ) : depthSum n s₀ s ≤ s₀ + s := by
  have hL := log_ratio_pos hn
  unfold depthSum
  rw [div_le_iff₀ hL]
  have e1 : s₀ * Real.log n / Real.log 2 = s₀ * (Real.log n / Real.log 2) := by ring
  have e2 : s * Real.log n / Real.log 2 = s * (Real.log n / Real.log 2) := by ring
  have h1 : (⌊s₀ * Real.log n / Real.log 2⌋ : ℝ) ≤ s₀ * (Real.log n / Real.log 2) :=
    (Int.floor_le _).trans (le_of_eq e1)
  have h2 : (⌊s * Real.log n / Real.log 2⌋ : ℝ) ≤ s * (Real.log n / Real.log 2) :=
    (Int.floor_le _).trans (le_of_eq e2)
  push_cast
  nlinarith

theorem le_depthSum {n : ℝ} (hn : 1 < n) (s₀ s : ℝ) :
    s₀ + s - 2 / (Real.log n / Real.log 2) ≤ depthSum n s₀ s := by
  have hL := log_ratio_pos hn
  unfold depthSum
  rw [le_div_iff₀ hL, sub_mul, div_mul_cancel₀ _ hL.ne']
  have e1 : s₀ * Real.log n / Real.log 2 = s₀ * (Real.log n / Real.log 2) := by ring
  have e2 : s * Real.log n / Real.log 2 = s * (Real.log n / Real.log 2) := by ring
  have h1 : s₀ * (Real.log n / Real.log 2) < (⌊s₀ * Real.log n / Real.log 2⌋ : ℝ) + 1 :=
    (le_of_eq e1.symm).trans_lt (Int.lt_floor_add_one _)
  have h2 : s * (Real.log n / Real.log 2) < (⌊s * Real.log n / Real.log 2⌋ : ℝ) + 1 :=
    (le_of_eq e2.symm).trans_lt (Int.lt_floor_add_one _)
  push_cast
  nlinarith

theorem depthSum_nonneg {n : ℝ} (hn : 1 < n) {s₀ s : ℝ} (hs₀ : 0 ≤ s₀) (hs : 0 ≤ s) :
    0 ≤ depthSum n s₀ s := by
  have hL := log_ratio_pos hn
  unfold depthSum
  apply div_nonneg _ hL.le
  have h1 : 0 ≤ ⌊s₀ * Real.log n / Real.log 2⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hs₀ (Real.log_pos hn).le)
      (Real.log_pos one_lt_two).le)
  have h2 : 0 ≤ ⌊s * Real.log n / Real.log 2⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hs (Real.log_pos hn).le)
      (Real.log_pos one_lt_two).le)
  exact_mod_cast add_nonneg h1 h2

theorem δ_pos (n r : ℝ) : 0 < δ n r := by
  unfold δ; positivity

theorem δ_zero (n : ℝ) : δ n 0 = 1 := by
  simp [δ]

/-! ## The observation identity -/

/-- The single-world observation at the summed depth, of the encoded incidence, is the
encoded observation of the world at depth `s`, provided the planar velocities are small
and the hidden scale is `θ = B * δ n s₀`. -/
theorem observation_encLine {W : ℕ} (γ : Fin W) {a b θ o B : ℝ} {n : ℝ} (hn : 1 < n)
    (s₀ s : ℝ) (hθ : θ = B * δ n s₀) (p : Incidence)
    (hv₁ : |a * p.1.2 3| < 1 / 2) (hv₂ : |b * p.1.2 4| < 1 / 2) :
    Submission.Obl.k4_joint_homogenization.Observation n (depthSum n s₀ s) 0
        (encLine W γ a b θ o p.1, p.2) =
      encObs a b o (obs B (δ n s) p) := by
  have hfl : ∀ c : ℝ, |c| < 1 / 2 → ⌊(c + 1 / 2) / (2 : ℝ) ^ (-(⌊(0 : ℝ) * Real.log n /
      Real.log 2⌋ : ℤ))⌋ = 0 := by
    intro c hc
    simp only [zero_mul, zero_div, Int.floor_zero, neg_zero, zpow_zero, div_one]
    rw [Int.floor_eq_iff]
    rw [abs_lt] at hc
    constructor <;> push_cast <;> linarith
  have hδ0 := δ_pos n s₀
  have hδs := δ_pos n s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · show (WithLp.toLp 2 ![p.2, (encCoeff a b θ o p.1.2) 0 + p.2 * (encCoeff a b θ o p.1.2) 3,
      (encCoeff a b θ o p.1.2) 1 + p.2 * (encCoeff a b θ o p.1.2) 4] :
        EuclideanSpace ℝ (Fin 3)) = baseMap a b o (baseObs p)
    ext i
    fin_cases i <;> simp [baseMap, baseObs, encCoeff, x] <;> ring
  · show ⌊((encCoeff a b θ o p.1.2) 2 + p.2 * (encCoeff a b θ o p.1.2) 5) /
      δ n (depthSum n s₀ s)⌋ = ⌊B * (x p.1 p.2) 3 / δ n s⌋
    rw [δ_depthSum hn, hθ]
    congr 1
    simp only [encCoeff, x]
    simp
    field_simp
  · funext j
    fin_cases j
    · show ⌊(encCoeff a b θ o p.1.2) 3 / (2 : ℝ) ^ (-(⌊(0 : ℝ) * Real.log n /
        Real.log 2⌋ : ℤ))⌋ = 0
      exact hfl _ hv₁
    · show ⌊(encCoeff a b θ o p.1.2) 4 / (2 : ℝ) ^ (-(⌊(0 : ℝ) * Real.log n /
        Real.log 2⌋ : ℤ))⌋ = 0
      exact hfl _ hv₂

/-! ## Regions -/

/-- The planar region of world with offset `o` and half-width `ρ`. -/
def region (o ρ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) := {z | |z 1 - z 0 / 2 - o| ≤ ρ}

theorem measurableSet_region (o ρ : ℝ) : MeasurableSet (region o ρ) := by
  unfold region
  exact measurableSet_le (by fun_prop) measurable_const

theorem baseMap_mem_region {a b o ρ : ℝ} (z : EuclideanSpace ℝ (Fin 3))
    (h : |a * z 1| ≤ ρ) : baseMap a b o z ∈ region o ρ := by
  have e : (baseMap a b o z) 1 - (baseMap a b o z) 0 / 2 - o = a * z 1 := by
    simp [baseMap]
  show |(baseMap a b o z) 1 - (baseMap a b o z) 0 / 2 - o| ≤ ρ
  rw [e]
  exact h

theorem region_disjoint {o o' ρ ρ' : ℝ} (h : ρ + ρ' < |o - o'|) :
    Disjoint (region o ρ) (region o' ρ') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  change |z 1 - z 0 / 2 - o| ≤ ρ at hz
  change |z 1 - z 0 / 2 - o'| ≤ ρ' at hz'
  have : |o - o'| ≤ |z 1 - z 0 / 2 - o| + |z 1 - z 0 / 2 - o'| := by
    calc |o - o'| = |(z 1 - z 0 / 2 - o') - (z 1 - z 0 / 2 - o)| := by ring_nf
      _ ≤ |z 1 - z 0 / 2 - o'| + |z 1 - z 0 / 2 - o| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
