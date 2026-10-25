-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/Parallelogram.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# Two flat coefficients against a transverse pair

The upper collision bound of paper Lemma 7.5 (`re:parallel-strips`, display
`re:collision-upper`): if two vectors `r, s` have wedge at least `Δ`, and two independent
coefficients have a law putting mass at most `φ` on every window `[x - h, x + h]`, then
`α r + β s + ζ` lies in the square `|·|_∞ ≤ h` with probability at most `(10 + 8D)/Δ · φ²`,
where `D` bounds the larger of the two vectors. We first condition on `α` (it is confined by the
wedge with `s`) and then on `β`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

noncomputable section

/-- The planar wedge (determinant) of two vectors. -/
def wedge (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem wedge_self (p : ℝ × ℝ) : wedge p p = 0 := by unfold wedge; ring

theorem wedge_comm (p q : ℝ × ℝ) : wedge p q = -wedge q p := by unfold wedge; ring

theorem wedge_add_left (p p' q : ℝ × ℝ) : wedge (p + p') q = wedge p q + wedge p' q := by
  unfold wedge; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem wedge_sub_left (p p' q : ℝ × ℝ) : wedge (p - p') q = wedge p q - wedge p' q := by
  unfold wedge; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem wedge_smul_left (c : ℝ) (p q : ℝ × ℝ) : wedge (c • p) q = c * wedge p q := by
  unfold wedge; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

variable {α : Type*} [Fintype α]

/-- The mass of a finite law `(w, val)` in a set of values. -/
def lawMass (w : α → ℝ) (val : α → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] : ℝ :=
  ∑ a, w a * (if val a ∈ S then 1 else 0)

theorem lawMass_nonneg {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (val : α → ℝ) (S : Set ℝ)
    [DecidablePred (· ∈ S)] : 0 ≤ lawMass w val S :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (by split_ifs <;> norm_num)

/-- Flatness at windows of radius `h` controls every closed interval. -/
theorem lawMass_Icc_le {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (val : α → ℝ) {h φ : ℝ} (hh : 0 < h)
    (hflat : ∀ x, lawMass w val (Set.Icc (x - h) (x + h)) ≤ φ) (c ρ : ℝ) (hρ : 0 ≤ ρ) :
    lawMass w val (Set.Icc (c - ρ) (c + ρ)) ≤ (ρ / h + 1) * φ := by
  classical
  set K := ⌊ρ / h⌋₊ with hK
  have hφ : 0 ≤ φ := le_trans (lawMass_nonneg hw val _) (hflat 0)
  -- every point of the interval lies in one of the `K + 1` windows
  have hcov : ∀ t ∈ Set.Icc (c - ρ) (c + ρ), ∃ k ∈ Finset.range (K + 1),
      t ∈ Set.Icc ((c - ρ + h * (2 * k + 1)) - h) ((c - ρ + h * (2 * k + 1)) + h) := by
    intro t ht
    have h0 : 0 ≤ (t - (c - ρ)) / (2 * h) := div_nonneg (by linarith [ht.1]) (by positivity)
    refine ⟨⌊(t - (c - ρ)) / (2 * h)⌋₊, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.floor_mono
      rw [div_le_div_iff₀ (by positivity) hh]
      nlinarith [ht.2]
    · have f1 := Nat.floor_le h0
      have f2 := Nat.lt_floor_add_one ((t - (c - ρ)) / (2 * h))
      rw [le_div_iff₀ (by positivity)] at f1
      rw [div_lt_iff₀ (by positivity)] at f2
      constructor <;> nlinarith
  calc lawMass w val (Set.Icc (c - ρ) (c + ρ))
      ≤ ∑ k ∈ Finset.range (K + 1),
          lawMass w val (Set.Icc ((c - ρ + h * (2 * k + 1)) - h) ((c - ρ + h * (2 * k + 1)) + h)) := by
        unfold lawMass
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hw a)
        split_ifs with ha
        · obtain ⟨k, hk, hk'⟩ := hcov _ ha
          calc (1 : ℝ) = if val a ∈ Set.Icc ((c - ρ + h * (2 * k + 1)) - h)
                ((c - ρ + h * (2 * k + 1)) + h) then 1 else 0 := by rw [ite_eq_left hk']
            _ ≤ ∑ k ∈ Finset.range (K + 1), if val a ∈ Set.Icc ((c - ρ + h * (2 * k + 1)) - h)
                ((c - ρ + h * (2 * k + 1)) + h) then (1 : ℝ) else 0 :=
              Finset.single_le_sum (f := fun k : ℕ => if val a ∈ Set.Icc
                ((c - ρ + h * (2 * k + 1)) - h) ((c - ρ + h * (2 * k + 1)) + h) then (1 : ℝ) else 0)
                (fun k _ => by split_ifs <;> norm_num) hk
        · exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
    _ ≤ ∑ _k ∈ Finset.range (K + 1), φ := Finset.sum_le_sum fun k _ => hflat _
    _ = (K + 1) * φ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (ρ / h + 1) * φ := by
        gcongr
        exact Nat.floor_le (div_nonneg hρ hh.le)


theorem pair_numeric {Δ D S1 Sinf W : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hW : Δ ≤ W)
    (hS1 : S1 ≤ 2 * Sinf) (hWS : W ≤ 2 * Sinf ^ 2) (hSD : Sinf ≤ 2 * D) (hS1n : 0 ≤ S1) :
    (S1 / W + 1) * (1 / Sinf + 1) ≤ (10 + 8 * D) / Δ := by
  have hWpos : 0 < W := lt_of_lt_of_le hΔ hW
  have hSpos : 0 < Sinf := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hShalf : Δ / 2 ≤ Sinf := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hD : 0 ≤ D := by linarith
  have t1 : S1 / W * (1 / Sinf) ≤ 2 / Δ := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hΔ]
    nlinarith
  have t2 : S1 / W ≤ 4 * D / Δ := by
    rw [div_le_div_iff₀ hWpos hΔ]
    nlinarith
  have t3 : 1 / Sinf ≤ 2 / Δ := by
    rw [div_le_div_iff₀ hSpos hΔ]
    linarith
  have t4 : (1 : ℝ) ≤ 1 / Δ := by rw [le_div_iff₀ hΔ]; linarith
  have e : (S1 / W + 1) * (1 / Sinf + 1) = S1 / W * (1 / Sinf) + S1 / W + 1 / Sinf + 1 := by ring
  rw [e]
  have e2 : (10 + 8 * D) / Δ = 2 / Δ + 4 * D / Δ + 2 / Δ + 1 / Δ + (5 + 4 * D) / Δ := by ring
  rw [e2]
  have : 0 ≤ (5 + 4 * D) / Δ := by positivity
  linarith

/-- **Two transverse coefficients** (the collision upper bound in paper Lemma 7.5). -/
theorem pair_collision_le {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (val : α → ℝ) {h φ Δ D : ℝ}
    (hh : 0 < h) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hflat : ∀ x, lawMass w val (Set.Icc (x - h) (x + h)) ≤ φ)
    (r s ζ : ℝ × ℝ) (hW : Δ ≤ |wedge r s|) (hrs : max |r.1| |r.2| ≤ max |s.1| |s.2|)
    (hsD : max |s.1| |s.2| ≤ 2 * D) :
    ∑ x, ∑ y, w x * w y * (if |(val x • r + val y • s + ζ).1| ≤ h ∧
      |(val x • r + val y • s + ζ).2| ≤ h then 1 else 0) ≤ (10 + 8 * D) / Δ * φ ^ 2 := by
  classical
  set Sinf := max |s.1| |s.2| with hSinf
  set S1 := |s.1| + |s.2| with hS1
  set W := wedge r s with hWdef
  have hφ : 0 ≤ φ := le_trans (lawMass_nonneg hw val _) (hflat 0)
  have hWpos : 0 < |W| := lt_of_lt_of_le hΔ hW
  have hWne : W ≠ 0 := abs_pos.mp hWpos
  have hSpos : 0 < Sinf := by
    by_contra hneg
    push Not at hneg
    have h1 : s.1 = 0 := abs_eq_zero.mp (le_antisymm (le_trans (le_max_left _ _) hneg) (abs_nonneg _))
    have h2 : s.2 = 0 := abs_eq_zero.mp (le_antisymm (le_trans (le_max_right _ _) hneg) (abs_nonneg _))
    apply hWne
    rw [hWdef, wedge, h1, h2]; ring
  -- the first coefficient is confined by the wedge with `s`
  set c₁ := -(wedge ζ s) / W
  set ρ₁ := h * S1 / |W|
  -- the second coefficient is confined by the largest coordinate of `s`
  let c₂ : ℝ → ℝ := fun v => if |s.2| ≤ |s.1| then -(v * r.1 + ζ.1) / s.1 else -(v * r.2 + ζ.2) / s.2
  set ρ₂ := h / Sinf
  have hconf : ∀ x y, (|(val x • r + val y • s + ζ).1| ≤ h ∧ |(val x • r + val y • s + ζ).2| ≤ h) →
      val x ∈ Set.Icc (c₁ - ρ₁) (c₁ + ρ₁) ∧ val y ∈ Set.Icc (c₂ (val x) - ρ₂) (c₂ (val x) + ρ₂) := by
    intro x y ⟨h1, h2⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    constructor
    · -- wedge of the small vector with `s`
      have hw' : |val x * W + wedge ζ s| ≤ h * S1 := by
        have e : val x * W + wedge ζ s = (val x * r.1 + val y * s.1 + ζ.1) * s.2 -
            (val x * r.2 + val y * s.2 + ζ.2) * s.1 := by
          rw [hWdef]; unfold wedge; ring
        rw [e]
        calc |(val x * r.1 + val y * s.1 + ζ.1) * s.2 - (val x * r.2 + val y * s.2 + ζ.2) * s.1|
            ≤ |(val x * r.1 + val y * s.1 + ζ.1) * s.2| + |(val x * r.2 + val y * s.2 + ζ.2) * s.1| :=
              abs_sub _ _
          _ = |val x * r.1 + val y * s.1 + ζ.1| * |s.2| + |val x * r.2 + val y * s.2 + ζ.2| * |s.1| := by
              rw [abs_mul, abs_mul]
          _ ≤ h * |s.2| + h * |s.1| := by gcongr
          _ = h * S1 := by rw [hS1]; ring
      have key : |val x - c₁| ≤ ρ₁ := by
        have e : val x - c₁ = (val x * W + wedge ζ s) / W := by
          simp only [c₁]; field_simp; ring
        rw [e, abs_div, div_le_div_iff_of_pos_right hWpos]
        simpa using hw'
      rw [abs_le] at key
      constructor <;> linarith
    · have key : |val y - c₂ (val x)| ≤ ρ₂ := by
        simp only [c₂]
        split_ifs with hc
        · have hs1 : Sinf = |s.1| := by rw [hSinf]; exact max_eq_left hc
          have hs1pos : 0 < |s.1| := hs1 ▸ hSpos
          have hs1ne : s.1 ≠ 0 := abs_pos.mp hs1pos
          have e : val y - -(val x * r.1 + ζ.1) / s.1 = (val x * r.1 + val y * s.1 + ζ.1) / s.1 := by
            field_simp; ring
          rw [e, abs_div, show ρ₂ = h / |s.1| by rw [← hs1]]
          exact div_le_div_of_nonneg_right h1 (abs_nonneg _)
        · push Not at hc
          have hs2 : Sinf = |s.2| := by rw [hSinf]; exact max_eq_right hc.le
          have hs2pos : 0 < |s.2| := hs2 ▸ hSpos
          have hs2ne : s.2 ≠ 0 := abs_pos.mp hs2pos
          have e : val y - -(val x * r.2 + ζ.2) / s.2 = (val x * r.2 + val y * s.2 + ζ.2) / s.2 := by
            field_simp; ring
          rw [e, abs_div, show ρ₂ = h / |s.2| by rw [← hs2]]
          exact div_le_div_of_nonneg_right h2 (abs_nonneg _)
      rw [abs_le] at key
      constructor <;> linarith
  have hρ₁ : 0 ≤ ρ₁ := by positivity
  have hρ₂ : 0 ≤ ρ₂ := by positivity
  have inner : ∀ x, ∑ y, w y * (if val y ∈ Set.Icc (c₂ (val x) - ρ₂) (c₂ (val x) + ρ₂) then 1 else 0)
      ≤ (ρ₂ / h + 1) * φ := fun x => lawMass_Icc_le hw val hh hflat _ _ hρ₂
  calc ∑ x, ∑ y, w x * w y * (if |(val x • r + val y • s + ζ).1| ≤ h ∧
        |(val x • r + val y • s + ζ).2| ≤ h then 1 else 0)
      ≤ ∑ x, w x * (if val x ∈ Set.Icc (c₁ - ρ₁) (c₁ + ρ₁) then 1 else 0) *
          ∑ y, w y * (if val y ∈ Set.Icc (c₂ (val x) - ρ₂) (c₂ (val x) + ρ₂) then 1 else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hev : |(val x • r + val y • s + ζ).1| ≤ h ∧ |(val x • r + val y • s + ζ).2| ≤ h
        · obtain ⟨hx, hy⟩ := hconf x y hev
          rw [ite_eq_left hev, ite_eq_left hx, ite_eq_left hy]
          exact le_of_eq (by ring)
        · rw [ite_eq_right hev, mul_zero]
          exact mul_nonneg (mul_nonneg (hw x) (by split_ifs <;> norm_num))
            (mul_nonneg (hw y) (by split_ifs <;> norm_num))
    _ ≤ ∑ x, w x * (if val x ∈ Set.Icc (c₁ - ρ₁) (c₁ + ρ₁) then 1 else 0) * ((ρ₂ / h + 1) * φ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (inner x) (mul_nonneg (hw x) (by split_ifs <;> norm_num))
    _ = lawMass w val (Set.Icc (c₁ - ρ₁) (c₁ + ρ₁)) * ((ρ₂ / h + 1) * φ) := by
        rw [lawMass, Finset.sum_mul]
    _ ≤ ((ρ₁ / h + 1) * φ) * ((ρ₂ / h + 1) * φ) := by
        gcongr
        exact lawMass_Icc_le hw val hh hflat _ _ hρ₁
    _ = ((S1 / |W| + 1) * (1 / Sinf + 1)) * φ ^ 2 := by
        simp only [ρ₁, ρ₂]
        field_simp
    _ ≤ (10 + 8 * D) / Δ * φ ^ 2 := by
        gcongr
        refine pair_numeric hΔ hΔ1 hW ?_ ?_ hsD (by positivity)
        · rw [hS1, hSinf]
          have := le_max_left |s.1| |s.2|
          have := le_max_right |s.1| |s.2|
          linarith
        · rw [hWdef, wedge]
          have hr1 : |r.1| ≤ Sinf := le_trans (le_max_left _ _) hrs
          have hr2 : |r.2| ≤ Sinf := le_trans (le_max_right _ _) hrs
          have hs1 : |s.1| ≤ Sinf := le_max_left _ _
          have hs2 : |s.2| ≤ Sinf := le_max_right _ _
          calc |r.1 * s.2 - r.2 * s.1| ≤ |r.1 * s.2| + |r.2 * s.1| := abs_sub _ _
            _ = |r.1| * |s.2| + |r.2| * |s.1| := by rw [abs_mul, abs_mul]
            _ ≤ Sinf * Sinf + Sinf * Sinf := by gcongr
            _ = 2 * Sinf ^ 2 := by ring

end

end Submission.Obl.k4_retained_edge_planar_rigidity
