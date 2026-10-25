-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Path, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Path.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Path.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Path.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/Path.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Common

/-!
# Nested path coverage

Residual incidences at the final level also belong to packets at every earlier
level. The inclusions here use the original assignments and original measures.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The finite data of a path, before imposing its geometric and mass bounds. -/
structure PathData (W : ℕ) where
  r : ℕ → ℝ
  T : ℕ → ℕ
  nw : ℕ → ℝ
  κ : ℝ
  C : ℕ
  lev : Fin C → ℕ
  par : Fin C → Fin C
  γ : Fin C → Fin W
  j : Fin C → ℕ
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  u : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set (ℕ × (Fin 6 → ℝ))
  F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)

/-- The frozen path predicate, with its data packed into one structure. -/
def PathData.Valid {W : ℕ} (p : PathData W) (Nk L : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ)
    (Mp Dp : ℕ) (σ : ℝ) : Prop :=
  path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ p.r p.T p.nw p.κ
    p.C p.lev p.par p.γ p.j p.c p.u p.Q p.R p.A p.F p.lst

/-- Repeated parent inclusions retain the full assignment, world, and incidences. -/
theorem ancestor_of_parent {β Γ α X : Type*} (lev : β → ℕ) (par : β → β)
    (γ : β → Γ) (A : β → Set α) (F : β → Set X)
    (hparent : ∀ b, 0 < lev b → lev (par b) + 1 = lev b ∧
      γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b))
    (b : β) (i : ℕ) (hi : i ≤ lev b) :
    ∃ a, lev a = i ∧ γ a = γ b ∧ A b ⊆ A a ∧ F b ⊆ F a := by
  generalize hn : lev b = n at hi
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases heq : i = n
    · exact ⟨b, hn.trans heq.symm, rfl, Subset.rfl, Subset.rfl⟩
    · have hlt : i < n := lt_of_le_of_ne hi heq
      obtain ⟨hlev, hγ, hA, hF⟩ := hparent b (by omega)
      obtain ⟨a, hai, haγ, haA, haF⟩ :=
        ih (lev (par b)) (by omega) (par b) rfl (by omega)
      exact ⟨a, hai, haγ.trans hγ, hA.trans haA, hF.trans haF⟩

/-- Final-level coverage propagates to every earlier level of a nested path. -/
theorem residual_covered_at_level {β Γ α X : Type*} (lev : β → ℕ) (par : β → β)
    (γ : β → Γ) (A : β → Set α) (F : β → Set X)
    (hparent : ∀ b, 0 < lev b → lev (par b) + 1 = lev b ∧
      γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b))
    (H : Γ → Set X) (last i : ℕ) (hi : i ≤ last)
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = last ∧ γ b = w ∧ p ∈ F b}) :
    ∀ w, H w ⊆ {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b} := by
  intro w p hp
  obtain ⟨b, hlast, hγ, hb⟩ := hH w hp
  obtain ⟨a, hlev, haγ, _, hF⟩ :=
    ancestor_of_parent lev par γ A F hparent b i (by omega)
  exact ⟨a, hlev, haγ.trans hγ, hF hb⟩

/-- A finite packet cover bounds residual mass without changing the prior. -/
theorem residual_mass_le_sum {β Γ X : Type*} [Fintype β] [DecidableEq Γ]
    [MeasurableSpace X]
    (μ : Γ → Measure X) (lev : β → ℕ) (γ : β → Γ) (F : β → Set X)
    (H : Γ → Set X) (i : ℕ)
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b}) (w : Γ) :
    μ w (H w) ≤ ∑ b, if lev b = i ∧ γ b = w then μ w (H w ∩ F b) else 0 := by
  classical
  let f : β → Set X := fun b => if lev b = i ∧ γ b = w then H w ∩ F b else ∅
  have hcover : H w ⊆ ⋃ b, f b := by
    intro p hp
    obtain ⟨b, hlev, hγ, hb⟩ := hH w hp
    exact mem_iUnion.mpr ⟨b, by simp [f, hlev, hγ, hp, hb]⟩
  calc
    μ w (H w) ≤ μ w (⋃ b, f b) := measure_mono hcover
    _ ≤ ∑ b, μ w (f b) := measure_iUnion_fintype_le _ _
    _ = _ := by simp [f, apply_ite]

/-- Regroup a finite packet mixture by its world. -/
theorem sum_packet_mixture {β Γ : Type*} [Fintype β] [Fintype Γ] [DecidableEq Γ]
    (lev : β → ℕ) (γ : β → Γ) (i : ℕ) (weight : Γ → ENNReal)
    (mass : Γ → β → ENNReal) :
    (∑ w, weight w * ∑ b, if lev b = i ∧ γ b = w then mass w b else 0) =
      ∑ b, if lev b = i then weight (γ b) * mass (γ b) b else 0 := by
  classical
  calc
    _ = ∑ b, ∑ w, if lev b = i ∧ γ b = w then weight w * mass w b else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : lev b = i <;> simp [hb]

/-- Summing over worlds preserves the original mixture weights. -/
theorem weighted_residual_mass_le_sum {β Γ X : Type*} [Fintype β] [Fintype Γ]
    [DecidableEq Γ] [MeasurableSpace X] (μ : Γ → Measure X) (ω : Γ → ℝ)
    (lev : β → ℕ) (γ : β → Γ) (F : β → Set X) (H : Γ → Set X) (i : ℕ)
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b}) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≤
      ∑ b, if lev b = i then ENNReal.ofReal (ω (γ b)) * μ (γ b) (H (γ b) ∩ F b)
        else 0 := by
  classical
  calc
    _ ≤ ∑ w, ENNReal.ofReal (ω w) *
        ∑ b, if lev b = i ∧ γ b = w then μ w (H w ∩ F b) else 0 := by
      exact Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (residual_mass_le_sum μ lev γ F H i hH w) zero_le
    _ = _ := sum_packet_mixture lev γ i _ _

/-- A substantial mixture contains a packet with a substantial fraction of its
full reference mass. No probability measure or posterior is renormalized. -/
theorem exists_packet_relative_mass {β : Type*} [Fintype β]
    (weight reference selected : β → ENNReal) {a : ℝ} (ha : 0 < a)
    (hreference : ∑ b, weight b * reference b ≤ 1)
    (hselected : ENNReal.ofReal a ≤ ∑ b, weight b * selected b) :
    ∃ b, 0 < weight b ∧ ENNReal.ofReal (a / 2) * reference b < selected b := by
  classical
  have hlt : (∑ b, weight b * (ENNReal.ofReal (a / 2) * reference b)) <
      ∑ b, weight b * selected b := by
    calc
      _ = ENNReal.ofReal (a / 2) * ∑ b, weight b * reference b := by
        simp_rw [mul_left_comm (weight _) (ENNReal.ofReal (a / 2))]
        rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (a / 2) := by
        simpa using mul_le_mul_of_nonneg_left hreference (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal (a / 2))
      _ < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff ha).mpr (by linarith)
      _ ≤ _ := hselected
  obtain ⟨b, _, hb⟩ := Finset.exists_lt_of_sum_lt hlt
  refine ⟨b, ?_, ?_⟩
  · by_contra hnot
    have hz : weight b = 0 := le_antisymm (le_of_not_gt hnot) zero_le
    simp [hz] at hb
  · by_contra hnot
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (zero_le : (0 : ENNReal) ≤ weight b))) hb

/-- Full assignments may repeat in different time blocks, but are disjoint
inside any one block. Their total prior mass is bounded by the block count. -/
theorem sum_assignment_mass_le_blocks {β α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (s : Finset β)
    (A : β → Set α) (j : β → ℕ) (q : ℕ)
    (hj : ∀ b ∈ s, j b < q) (hA : ∀ b ∈ s, MeasurableSet (A b))
    (hdisj : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → j b = j b' → Disjoint (A b) (A b')) :
    ∑ b ∈ s, ν (A b) ≤ (q : ENNReal) := by
  classical
  have hblock (n : ℕ) : (∑ b ∈ s with j b = n, ν (A b)) ≤ 1 := by
    have hd : (↑(s.filter (fun b => j b = n)) : Set β).PairwiseDisjoint A := by
      intro b hb b' hb' hne
      obtain ⟨hbs, hb⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb's, hb'⟩ := Finset.mem_filter.mp hb'
      exact hdisj b hbs b' hb's hne (hb.trans hb'.symm)
    rw [← measure_biUnion_finset hd (fun b hb => hA b (Finset.mem_filter.mp hb).1)]
    exact (measure_mono (subset_univ _)).trans_eq measure_univ
  calc
    _ = ∑ n ∈ Finset.range q, ∑ b ∈ s with j b = n, ν (A b) :=
      (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_range.mpr (hj b hb))
        (fun b => ν (A b))).symm
    _ ≤ ∑ _n ∈ Finset.range q, (1 : ENNReal) :=
      Finset.sum_le_sum fun n _ => hblock n
    _ = (q : ENNReal) := by simp

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.parent (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (hb : 0 < p.lev b) :
    p.lev (p.par b) + 1 = p.lev b ∧ p.γ (p.par b) = p.γ b ∧
      p.A b ⊆ p.A (p.par b) ∧ p.F b ⊆ p.F (p.par b) := by
  rcases h.2.2.2.2.2.2.2 b with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp⟩
  have hp := hp hb
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

theorem PathData.Valid.covered_at_level (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (i : ℕ) (hi : i < m)
    (hH : ∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) :
    ∀ w, H w ⊆ {q | ∃ b, p.lev b = i ∧ p.γ b = w ∧ q ∈ p.F b} :=
  residual_covered_at_level p.lev p.par p.γ p.A p.F h.parent H (m - 1) i
    (by omega) hH

/-- A saturated packet carries positive incidence mass. -/
theorem PathData.Valid.packet_mass_pos (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) :
    0 < ((ν (p.γ b)).prod volume) (p.F b) := by
  rcases h.2.2.2.2.2.2.2 b with
    ⟨_, _, hdet, _, _, _, _, _, _, _, _, _, _, hmass, _⟩
  apply lt_of_lt_of_le _ hmass
  apply ENNReal.ofReal_pos.mpr
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hNk _) (abs_pos.mpr hdet))
    (mul_pos (by positivity) hκ)

/-- No packet of a saturated path can have a zero full trajectory assignment. -/
theorem PathData.Valid.assignment_mass_pos (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) : 0 < ν (p.γ b) (p.A b) := by
  by_contra hnot
  have hzero : ν (p.γ b) (p.A b) = 0 := le_antisymm (le_of_not_gt hnot) zero_le
  rcases h.2.2.2.2.2.2.2 b with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF, _⟩
  have hsub : p.F b ⊆ p.A b ×ˢ Set.univ := by
    intro q hq
    exact ⟨(hF q hq).2.1, mem_univ _⟩
  have hbound : ((ν (p.γ b)).prod volume) (p.F b) ≤ 0 := by
    calc
      _ ≤ ((ν (p.γ b)).prod volume) (p.A b ×ˢ Set.univ) := measure_mono hsub
      _ = 0 := by simp [Measure.prod_prod, hzero]
  exact (not_lt_of_ge hbound) (h.packet_mass_pos hNk b)

/-- Incidence saturation also supplies the lower full-prior assignment bound:
the block duration cancels before any conditioning takes place. -/
theorem PathData.Valid.assignment_mass_bounds (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) :
    ENNReal.ofReal (Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / p.κ) ≤
      ν (p.γ b) (p.A b) ∧
    ν (p.γ b) (p.A b) ≤
      ENNReal.ofReal (p.κ * Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det|) := by
  rcases h.2.2.2.2.2.2.2 b with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF, hmass, hupper, _⟩
  refine ⟨?_, hupper⟩
  let q : ℝ := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  have hsub : p.F b ⊆ p.A b ×ˢ Icc
      ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
      (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
    intro z hz
    exact ⟨(hF z hz).2.1, (hF z hz).2.2.1⟩
  have hprod : ((ν (p.γ b)).prod volume) (p.F b) ≤
      ν (p.γ b) (p.A b) * ENNReal.ofReal q := by
    calc
      _ ≤ ((ν (p.γ b)).prod volume) (p.A b ×ˢ Icc
          ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
          (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))) := measure_mono hsub
      _ = _ := by
        rw [Measure.prod_prod, Real.volume_Icc]
        congr 2
        dsimp [q]
        ring
  have hfactor : ENNReal.ofReal (Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / p.κ) *
      ENNReal.ofReal q = ENNReal.ofReal
        (Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [q]
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hcancel (z : ENNReal) : (z * ENNReal.ofReal q) * (ENNReal.ofReal q)⁻¹ = z := by
    rw [mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, mul_one]
  calc
    _ = (_ * ENNReal.ofReal q) * (ENNReal.ofReal q)⁻¹ := (hcancel _).symm
    _ ≤ (ν (p.γ b) (p.A b) * ENNReal.ofReal q) * (ENNReal.ofReal q)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      rw [hfactor]
      exact hmass.trans hprod
    _ = _ := hcancel _

/-- The exact spatial Jacobian divided by the full assignment mass has the
profile normalization predicted by saturation. -/
theorem PathData.Valid.density_normalization_bound
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk) (b : Fin p.C) :
    ENNReal.ofReal |(p.Q b).det| / ν (p.γ b) (p.A b) ≤
      ENNReal.ofReal (p.κ * Nk ^ f (p.r (p.lev b))) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  have hdet : 0 < |(p.Q b).det| := abs_pos.mpr (h.2.2.2.2.2.2.2 b).2.2.1
  have hfloor : 0 < Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / p.κ := by positivity
  calc
    _ ≤ ENNReal.ofReal |(p.Q b).det| /
        ENNReal.ofReal (Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / p.κ) := by
      exact mul_le_mul_of_nonneg_left
        (ENNReal.inv_le_inv.mpr (h.assignment_mass_bounds hNk b).1) zero_le
    _ = ENNReal.ofReal (|(p.Q b).det| /
        (Nk ^ (-f (p.r (p.lev b))) * |(p.Q b).det| / p.κ)) :=
      (ENNReal.ofReal_div_of_pos hfloor).symm
    _ = _ := by
      congr 1
      rw [Real.rpow_neg hNk.le]
      field_simp

theorem PathData.Valid.assignment_mass_sum_le (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (i : ℕ) (w : Fin W) :
    (∑ b, if p.lev b = i ∧ p.γ b = w then ν w (p.A b) else 0) ≤
      ((2 ^ p.T i : ℕ) : ENNReal) := by
  classical
  have := hν w
  let ids : Finset (Fin p.C) := Finset.univ.filter (fun b => p.lev b = i ∧ p.γ b = w)
  have hbound := sum_assignment_mass_le_blocks (ν w) ids p.A p.j (2 ^ p.T i)
    (fun b hb => by
      have hlev := (Finset.mem_filter.mp hb).2.1
      simpa [hlev] using (h.2.2.2.2.2.2.2 b).2.1)
    (fun b _ => by
      rcases h.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, hA, _⟩
      exact hA)
    (fun b hb b' hb' hne hj => by
      obtain ⟨hi, hw⟩ := (Finset.mem_filter.mp hb).2
      obtain ⟨hi', hw'⟩ := (Finset.mem_filter.mp hb').2
      exact h.2.2.2.2.2.2.1 b b' hne (hi.trans hi'.symm) (hw.trans hw'.symm) hj)
  simpa [ids, Finset.sum_filter] using hbound

/-- The full assignment times the old block length has total mixture mass at
most one, even though assignments at different times may overlap. -/
theorem PathData.Valid.full_reference_mass_le_one
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hsum : ∑ w, ω w = 1) (i : ℕ) :
    (∑ b, (if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) else 0) *
      (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b))) ≤ 1 := by
  classical
  have hbudget : (∑ b, if p.lev b = i then
      ENNReal.ofReal (ω (p.γ b)) * ν (p.γ b) (p.A b) else 0) ≤
        ((2 ^ p.T i : ℕ) : ENNReal) := by
    calc
      _ = ∑ w, ENNReal.ofReal (ω w) *
          ∑ b, if p.lev b = i ∧ p.γ b = w then ν w (p.A b) else 0 :=
        (sum_packet_mixture p.lev p.γ i _ _).symm
      _ ≤ ∑ w, ENNReal.ofReal (ω w) * ((2 ^ p.T i : ℕ) : ENNReal) :=
        Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left (h.assignment_mass_sum_le hν i w) zero_le
      _ = (∑ w, ENNReal.ofReal (ω w)) * ((2 ^ p.T i : ℕ) : ENNReal) :=
        (Finset.sum_mul _ _ _).symm
      _ = ((2 ^ p.T i : ℕ) : ENNReal) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hsum]
        simp
  have hcast : ((2 ^ p.T i : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ p.T i) := by
    norm_cast
  calc
    _ = ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) *
        ∑ b, if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) * ν (p.γ b) (p.A b)
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : p.lev b = i <;> simp [hb, mul_left_comm]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ((2 ^ p.T i : ℕ) : ENNReal) :=
      mul_le_mul_of_nonneg_left hbudget zero_le
    _ = 1 := by
      rw [hcast, ENNReal.ofReal_inv_of_pos (by positivity)]
      exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- At each earlier depth a substantial final residual fills a packet by a
fixed fraction of its full original assignment times its time length. -/
theorem PathData.Valid.exists_dense_packet
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b})
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w))
    (i : ℕ) (hi : i < m) :
    ∃ b, p.lev b = i ∧ 0 < ω (p.γ b) ∧
      ENNReal.ofReal ((p.κ⁻¹ / 4) / (2 : ℝ) ^ p.T i) * ν (p.γ b) (p.A b) <
        ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
  classical
  let weight : Fin p.C → ENNReal :=
    fun b => if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) else 0
  let reference : Fin p.C → ENNReal :=
    fun b => ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)
  let selected : Fin p.C → ENNReal :=
    fun b => ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b)
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  have hselected : ENNReal.ofReal (p.κ⁻¹ / 2) ≤ ∑ b, weight b * selected b := by
    calc
      _ ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w) := hmass
      _ ≤ ∑ b, if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) * selected b else 0 :=
        weighted_residual_mass_le_sum (fun w => (ν w).prod volume) ω
          p.lev p.γ p.F H i (h.covered_at_level H i hi hH)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        simp [weight, ite_mul]
  obtain ⟨b, hw, hb⟩ := exists_packet_relative_mass weight reference selected
    (a := p.κ⁻¹ / 2) (by positivity) (h.full_reference_mass_le_one hν hω hsum i) hselected
  have hlev : p.lev b = i := by
    by_contra hne
    simp [weight, hne] at hw
  refine ⟨b, hlev, ENNReal.ofReal_pos.mp (by simpa [weight, hlev] using hw), ?_⟩
  change ENNReal.ofReal (p.κ⁻¹ / 2 / 2) *
    (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)) < _ at hb
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hb
  convert hb using 1
  congr 2
  ring

end ValidPath

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
