/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/DiscrepancyGroups.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/DiscrepancyGroups.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DiscrepancyBasics

set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric MeasureTheory

/-- The data of one discrepancy-matching problem: a finite pair law, source and witness
sheet labels with a common coordinate label, matching base points in the real half ball,
near-source values and per-label base densities. -/
structure DiscSetup (ι Λ Ω : Type*) [MeasurableSpace Ω] where
  Pm : Measure Ω
  lab : ι → Λ
  φ : ι → EuclideanSpace ℂ (Fin 3) → ℂ
  src : Ω → ι
  wit : Ω → ι
  x : Ω → EuclideanSpace ℝ (Fin 3)
  w : Ω → ℝ
  Δ : ℝ
  ρ : Λ → ℝ
  finite : IsFiniteMeasure Pm
  sheet : ∀ i, IsMatchSheet (φ i)
  src_meas : ∀ i, MeasurableSet {p | src p = i}
  wit_meas : ∀ i, MeasurableSet {p | wit p = i}
  x_meas : Measurable x
  lab_eq : ∀ p, lab (src p) = lab (wit p)
  x_mem : ∀ p, ‖x p‖ ≤ 1 / 2
  Δ_pos : 0 < Δ
  near_src : ∀ p, ‖φ (src p) (emb (x p)) - (w p : ℂ)‖ ≤ Δ
  near_wit : ∀ p, ‖φ (wit p) (emb (x p)) - (w p : ℂ)‖ ≤ Δ
  ρ_nonneg : ∀ l, 0 ≤ ρ l
  dens_src : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    Pm {p | src p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U
  dens_wit : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    Pm {p | wit p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U

/-- Group labels: dyadic scale, coordinate label, source cube and witness cube. -/
abbrev GLabel (Λ : Type*) (J : JetData) :=
  ℕ × Λ × (↥J.V × Fin J.q → ℤ) × (↥J.V × Fin J.q → ℤ)

section Groups

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ)

/-- The group label of a source/witness label pair. -/
noncomputable def groupLabel (i i' : ι) : GLabel Λ J :=
  (discScale M₀ (sheetDisc S.φ i i'), S.lab i,
    sheetCube J S.φ M₀ (discScale M₀ (sheetDisc S.φ i i')) i,
    sheetCube J S.φ M₀ (discScale M₀ (sheetDisc S.φ i i')) i')

/-- The pairs of one discrepancy group. -/
def grp (g : GLabel Λ J) : Set Ω :=
  {p | M₀ ≤ sheetDisc S.φ (S.src p) (S.wit p) ∧ groupLabel J S M₀ (S.src p) (S.wit p) = g}

/-- The finitely many labels of nonempty groups. -/
noncomputable def groupLabels : Finset (GLabel Λ J) := by
  classical
  exact (Finset.univ.filter (fun ii : ι × ι => M₀ ≤ sheetDisc S.φ ii.1 ii.2)).image
    (fun ii => groupLabel J S M₀ ii.1 ii.2)

lemma measurableSet_grp (g : GLabel Λ J) : MeasurableSet (grp J S M₀ g) := by
  classical
  have : grp J S M₀ g = ⋃ ii ∈ (Finset.univ.filter (fun ii : ι × ι =>
      M₀ ≤ sheetDisc S.φ ii.1 ii.2 ∧ groupLabel J S M₀ ii.1 ii.2 = g)),
      ({p | S.src p = ii.1} ∩ {p | S.wit p = ii.2}) := by
    ext p
    simp only [grp, mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_inter_iff, exists_prop, Prod.exists]
    constructor
    · intro h
      exact ⟨S.src p, S.wit p, h, rfl, rfl⟩
    · rintro ⟨i, i', h, rfl, rfl⟩
      exact h
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun ii _ => (S.src_meas ii.1).inter (S.wit_meas ii.2))

lemma disjoint_grp {g g' : GLabel Λ J} (h : g ≠ g') :
    Disjoint (grp J S M₀ g) (grp J S M₀ g') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  exact h (hp.2.symm.trans hp'.2)

lemma bad_subset_iUnion_grp :
    {p | M₀ ≤ sheetDisc S.φ (S.src p) (S.wit p)} ⊆
      ⋃ g ∈ groupLabels J S M₀, grp J S M₀ g := by
  classical
  intro p hp
  simp only [mem_iUnion, exists_prop]
  refine ⟨groupLabel J S M₀ (S.src p) (S.wit p), ?_, hp, rfl⟩
  simp only [groupLabels, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  exact ⟨S.src p, S.wit p, hp, rfl⟩

end Groups

section GroupFacts

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ)

lemma mem_grp_spec {g : GLabel Λ J} {p : Ω} (hp : p ∈ grp J S M₀ g) (hM₀ : 0 < M₀) :
    M₀ * 2 ^ g.1 ≤ sheetDisc S.φ (S.src p) (S.wit p) ∧
      sheetDisc S.φ (S.src p) (S.wit p) < M₀ * 2 ^ (g.1 + 1) ∧
      S.lab (S.src p) = g.2.1 ∧ sheetCube J S.φ M₀ g.1 (S.src p) = g.2.2.1 ∧
      sheetCube J S.φ M₀ g.1 (S.wit p) = g.2.2.2 := by
  obtain ⟨hd, hg⟩ := hp
  subst hg
  have := discScale_spec hM₀ hd
  exact ⟨this.1, this.2, rfl, rfl, rfl⟩

/-- Sheets in the same cube are close on the real half ball. -/
lemma close_of_cube_eq {k : ℕ} {i i' : ι} (hM₀ : 0 < M₀)
    (h : sheetCube J S.φ M₀ k i = sheetCube J S.φ M₀ k i') (y : EuclideanSpace ℝ (Fin 3))
    (hy : ‖y‖ ≤ 1 / 2) : ‖S.φ i (emb y) - S.φ i' (emb y)‖ < M₀ * 2 ^ k / 2 := by
  obtain ⟨v, hv, j, hj, hle⟩ := (J.spec _ _ (S.sheet i) (S.sheet i')).1 y hy
  have hs : 0 < J.c * (M₀ * 2 ^ k) / 2 := by have := J.hc; positivity
  have hfl := congrFun h (⟨v, hv⟩, ⟨j, hj⟩)
  simp only [sheetCube] at hfl
  have hlt := abs_sub_lt_of_floor_eq hs hfl
  have hc := J.hc
  have : J.c * ‖S.φ i (emb y) - S.φ i' (emb y)‖ < J.c * (M₀ * 2 ^ k / 2) := by
    calc _ ≤ _ := hle
      _ < J.c * (M₀ * 2 ^ k) / 2 := hlt
      _ = _ := by ring
  exact lt_of_mul_lt_mul_left this hc.le

/-- Sheets in the same cube are close on the real unit ball. -/
lemma close_unit_of_cube_eq {k : ℕ} {i i' : ι} (hM₀ : 0 < M₀)
    (h : sheetCube J S.φ M₀ k i = sheetCube J S.φ M₀ k i') (y : EuclideanSpace ℝ (Fin 3))
    (hy : ‖y‖ ≤ 1) : ‖S.φ i (emb y) - S.φ i' (emb y)‖ ≤ J.C₂ * (M₀ * 2 ^ k / 2) :=
  (J.spec _ _ (S.sheet i) (S.sheet i')).2.2 _ (by positivity)
    (fun y' hy' => (close_of_cube_eq J S M₀ hM₀ h y' hy').le) y hy

/-- A pair whose half-ball discrepancy is below `A` is within `C₂ A` on the unit ball. -/
lemma close_unit_of_disc {i i' : ι} {A : ℝ} (hA : 0 < A) (hd : sheetDisc S.φ i i' ≤ A)
    (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ ≤ 1) :
    ‖S.φ i (emb y) - S.φ i' (emb y)‖ ≤ J.C₂ * A :=
  (J.spec _ _ (S.sheet i) (S.sheet i')).2.2 A hA
    (fun y' hy' => (le_sheetDisc S.sheet i i' hy').trans hd) y hy

/-- The integer radius of witness-cube neighborhoods. -/
noncomputable def cubeRadius : ℕ := ⌊4 * (∑ j ∈ Finset.range J.q, J.B j) / J.c⌋₊ + 1

lemma int_abs_le_of_le {n : ℤ} {X : ℝ} (hX : 0 ≤ X) (h : |(n : ℝ)| ≤ X + 1) :
    |n| ≤ (⌊X⌋₊ + 1 : ℕ) := by
  have h1 : ((|n| : ℤ) : ℝ) ≤ X + 1 := by push_cast; exact h
  have h2 : ((|n| - 1 : ℤ) : ℝ) ≤ X := by push_cast; push_cast at h1; linarith
  have h3 : |n| - 1 ≤ (⌊X⌋₊ : ℤ) := by
    by_cases hn : |n| - 1 ≤ 0
    · have : (0 : ℤ) ≤ (⌊X⌋₊ : ℤ) := Nat.cast_nonneg _
      omega
    · push Not at hn
      have hnn : (0 : ℤ) ≤ |n| - 1 := hn.le
      have := Nat.le_floor (n := (|n| - 1).toNat) (a := X) (by
        rw [show (((|n| - 1).toNat : ℕ) : ℝ) = ((|n| - 1 : ℤ) : ℝ) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]]
        exact h2)
      have : ((|n| - 1).toNat : ℤ) ≤ (⌊X⌋₊ : ℤ) := by exact_mod_cast this
      rw [Int.toNat_of_nonneg hnn] at this
      exact this
  push_cast
  linarith

/-- Witness cubes are bounded neighbors of source cubes. -/
lemma cube_neighbor {g : GLabel Λ J} {p : Ω} (hp : p ∈ grp J S M₀ g) (hM₀ : 0 < M₀)
    (vj : ↥J.V × Fin J.q) : |g.2.2.2 vj - g.2.2.1 vj| ≤ (cubeRadius J : ℤ) := by
  obtain ⟨hlo, hhi, -, hc₁, hc₂⟩ := mem_grp_spec J S M₀ hp hM₀
  set k := g.1
  set D := sheetDisc S.φ (S.src p) (S.wit p)
  have hMk : 0 < M₀ * 2 ^ k := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le hMk hlo
  obtain ⟨⟨v, hv⟩, ⟨j, hj⟩⟩ := vj
  have hup := (J.spec _ _ (S.sheet (S.src p)) (S.sheet (S.wit p))).2.1 D hDpos
    (fun y hy => le_sheetDisc S.sheet _ _ hy) v hv j
  have hc := J.hc
  set s := J.c * (M₀ * 2 ^ k) / 2 with hs_def
  have hs : 0 < s := by positivity
  have hBj : J.B j ≤ ∑ j ∈ Finset.range J.q, J.B j :=
    Finset.single_le_sum (fun j _ => (J.hB j).le) (Finset.mem_range.mpr hj)
  set X := 4 * (∑ j ∈ Finset.range J.q, J.B j) / J.c with hX_def
  have hX : 0 ≤ X := by
    have : 0 ≤ ∑ j ∈ Finset.range J.q, J.B j := Finset.sum_nonneg (fun j _ => (J.hB j).le)
    positivity
  have hkey : |sheetJet (S.φ (S.wit p)) v j - sheetJet (S.φ (S.src p)) v j| ≤ X * s := by
    rw [abs_sub_comm]
    calc _ ≤ J.B j * D := hup
      _ ≤ J.B j * (M₀ * 2 ^ (k + 1)) := mul_le_mul_of_nonneg_left hhi.le (J.hB j).le
      _ ≤ (∑ j ∈ Finset.range J.q, J.B j) * (M₀ * 2 ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hBj (by positivity)
      _ = X * s := by rw [hX_def, hs_def, pow_succ]; field_simp; ring
  have := abs_floor_sub_le hs hkey
  have hcube : g.2.2.2 (⟨v, hv⟩, ⟨j, hj⟩) - g.2.2.1 (⟨v, hv⟩, ⟨j, hj⟩) =
      ⌊sheetJet (S.φ (S.wit p)) v j / s⌋ - ⌊sheetJet (S.φ (S.src p)) v j / s⌋ := by
    rw [← hc₁, ← hc₂]
    rfl
  rw [hcube]
  exact int_abs_le_of_le hX this

/-- A group lies in the band of any of its source sheets. -/
lemma grp_subset_band {g : GLabel Λ J} {p₀ : Ω} (hp₀ : p₀ ∈ grp J S M₀ g) (hM₀ : 0 < M₀)
    (hΔ : S.Δ ≤ M₀) :
    grp J S M₀ g ⊆ {p | S.lab (S.src p) = S.lab (S.src p₀) ∧
      ‖S.φ (S.src p₀) (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ g.1)} := by
  intro p hp
  obtain ⟨-, -, hl, hc, -⟩ := mem_grp_spec J S M₀ hp hM₀
  obtain ⟨-, -, hl₀, hc₀, -⟩ := mem_grp_spec J S M₀ hp₀ hM₀
  refine ⟨hl.trans hl₀.symm, ?_⟩
  have hclose := close_of_cube_eq J S M₀ hM₀ (hc₀.trans hc.symm) (S.x p) (S.x_mem p)
  have hnear := S.near_src p
  have hk : M₀ ≤ M₀ * 2 ^ g.1 := le_mul_of_one_le_right hM₀.le (one_le_pow₀ (by norm_num))
  calc ‖S.φ (S.src p₀) (emb (S.x p)) - (S.w p : ℂ)‖
      ≤ ‖S.φ (S.src p₀) (emb (S.x p)) - S.φ (S.src p) (emb (S.x p))‖ +
        ‖S.φ (S.src p) (emb (S.x p)) - (S.w p : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M₀ * 2 ^ g.1 / 2 + S.Δ := add_le_add hclose.le hnear
    _ ≤ 2 * (M₀ * 2 ^ g.1) := by linarith

end GroupFacts

section HeavyLight

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ) (θ : Λ → ℝ)

/-- Source labels of positive group mass at least `θ`. -/
noncomputable def heavySrc (g : GLabel Λ J) : Finset ι :=
  Finset.univ.filter (fun i => ENNReal.ofReal (θ g.2.1) ≤ S.Pm (grp J S M₀ g ∩ {p | S.src p = i}))

/-- Witness labels of group mass at least `θ`. -/
noncomputable def heavyWit (g : GLabel Λ J) : Finset ι :=
  Finset.univ.filter (fun i => ENNReal.ofReal (θ g.2.1) ≤ S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}))

/-- Source labels occurring in a group. -/
noncomputable def srcSet (g : GLabel Λ J) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (grp J S M₀ g ∩ {p | S.src p = i}).Nonempty)

/-- Witness labels occurring in a group. -/
noncomputable def witSet (g : GLabel Λ J) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (grp J S M₀ g ∩ {p | S.wit p = i}).Nonempty)

/-- The retained core of a group: both labels heavy. -/
def core (g : GLabel Λ J) : Set Ω :=
  grp J S M₀ g ∩ {p | S.src p ∈ heavySrc J S M₀ θ g ∧ S.wit p ∈ heavyWit J S M₀ θ g}

lemma measurableSet_core (g : GLabel Λ J) : MeasurableSet (core J S M₀ θ g) := by
  apply (measurableSet_grp J S M₀ g).inter
  have h1 : {p | S.src p ∈ heavySrc J S M₀ θ g} =
      ⋃ i ∈ heavySrc J S M₀ θ g, {p | S.src p = i} := by
    ext p; simp
  have h2 : {p | S.wit p ∈ heavyWit J S M₀ θ g} =
      ⋃ i ∈ heavyWit J S M₀ θ g, {p | S.wit p = i} := by
    ext p; simp
  have : {p | S.src p ∈ heavySrc J S M₀ θ g ∧ S.wit p ∈ heavyWit J S M₀ θ g} =
      {p | S.src p ∈ heavySrc J S M₀ θ g} ∩ {p | S.wit p ∈ heavyWit J S M₀ θ g} := rfl
  rw [this, h1, h2]
  exact (Finset.measurableSet_biUnion _ (fun i _ => S.src_meas i)).inter
    (Finset.measurableSet_biUnion _ (fun i _ => S.wit_meas i))

lemma grp_src_sum (g : GLabel Λ J) (T : Finset ι) :
    S.Pm (⋃ i ∈ T, grp J S M₀ g ∩ {p | S.src p = i}) =
      ∑ i ∈ T, S.Pm (grp J S M₀ g ∩ {p | S.src p = i}) := by
  apply measure_biUnion_finset
  · intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro p hp hp'
    exact hii' (hp.2.symm.trans hp'.2)
  · intro i _
    exact (measurableSet_grp J S M₀ g).inter (S.src_meas i)

lemma grp_wit_sum (g : GLabel Λ J) (T : Finset ι) :
    S.Pm (⋃ i ∈ T, grp J S M₀ g ∩ {p | S.wit p = i}) =
      ∑ i ∈ T, S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}) := by
  apply measure_biUnion_finset
  · intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro p hp hp'
    exact hii' (hp.2.symm.trans hp'.2)
  · intro i _
    exact (measurableSet_grp J S M₀ g).inter (S.wit_meas i)

lemma heavySrc_card_le (g : GLabel Λ J) :
    ((heavySrc J S M₀ θ g).card : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ S.Pm (grp J S M₀ g) := by
  calc ((heavySrc J S M₀ θ g).card : ENNReal) * ENNReal.ofReal (θ g.2.1)
      = ∑ i ∈ heavySrc J S M₀ θ g, ENNReal.ofReal (θ g.2.1) := by simp
    _ ≤ ∑ i ∈ heavySrc J S M₀ θ g, S.Pm (grp J S M₀ g ∩ {p | S.src p = i}) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
    _ = S.Pm (⋃ i ∈ heavySrc J S M₀ θ g, grp J S M₀ g ∩ {p | S.src p = i}) :=
        (grp_src_sum J S M₀ g _).symm
    _ ≤ S.Pm (grp J S M₀ g) := measure_mono (by
        intro p hp
        simp only [mem_iUnion, exists_prop] at hp
        obtain ⟨i, -, hp, -⟩ := hp
        exact hp)

lemma heavyWit_card_le (g : GLabel Λ J) :
    ((heavyWit J S M₀ θ g).card : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ S.Pm (grp J S M₀ g) := by
  calc ((heavyWit J S M₀ θ g).card : ENNReal) * ENNReal.ofReal (θ g.2.1)
      = ∑ i ∈ heavyWit J S M₀ θ g, ENNReal.ofReal (θ g.2.1) := by simp
    _ ≤ ∑ i ∈ heavyWit J S M₀ θ g, S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
    _ = S.Pm (⋃ i ∈ heavyWit J S M₀ θ g, grp J S M₀ g ∩ {p | S.wit p = i}) :=
        (grp_wit_sum J S M₀ g _).symm
    _ ≤ S.Pm (grp J S M₀ g) := measure_mono (by
        intro p hp
        simp only [mem_iUnion, exists_prop] at hp
        obtain ⟨i, -, hp, -⟩ := hp
        exact hp)

/-- The light part of a group is bounded by `θ` per occurring label. -/
lemma light_le (g : GLabel Λ J) :
    S.Pm (grp J S M₀ g \ core J S M₀ θ g) ≤
      ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card) := by
  classical
  have hsub : grp J S M₀ g \ core J S M₀ θ g ⊆
      (⋃ i ∈ srcSet J S M₀ g \ heavySrc J S M₀ θ g, grp J S M₀ g ∩ {p | S.src p = i}) ∪
      (⋃ i ∈ witSet J S M₀ g \ heavyWit J S M₀ θ g, grp J S M₀ g ∩ {p | S.wit p = i}) := by
    intro p ⟨hp, hpc⟩
    simp only [core, mem_inter_iff, mem_setOf_eq, not_and] at hpc
    by_cases hs : S.src p ∈ heavySrc J S M₀ θ g
    · have hw := hpc hp hs
      right
      simp only [mem_iUnion, exists_prop, Finset.mem_sdiff]
      refine ⟨S.wit p, ⟨?_, hw⟩, hp, rfl⟩
      simp only [witSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, rfl⟩
    · left
      simp only [mem_iUnion, exists_prop, Finset.mem_sdiff]
      refine ⟨S.src p, ⟨?_, hs⟩, hp, rfl⟩
      simp only [srcSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, rfl⟩
  have hlight₁ : ∀ i ∈ srcSet J S M₀ g \ heavySrc J S M₀ θ g,
      S.Pm (grp J S M₀ g ∩ {p | S.src p = i}) ≤ ENNReal.ofReal (θ g.2.1) := by
    intro i hi
    have := (Finset.mem_sdiff.mp hi).2
    simp only [heavySrc, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at this
    exact this.le
  have hlight₂ : ∀ i ∈ witSet J S M₀ g \ heavyWit J S M₀ θ g,
      S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}) ≤ ENNReal.ofReal (θ g.2.1) := by
    intro i hi
    have := (Finset.mem_sdiff.mp hi).2
    simp only [heavyWit, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at this
    exact this.le
  calc S.Pm (grp J S M₀ g \ core J S M₀ θ g)
      ≤ S.Pm (⋃ i ∈ srcSet J S M₀ g \ heavySrc J S M₀ θ g, grp J S M₀ g ∩ {p | S.src p = i}) +
        S.Pm (⋃ i ∈ witSet J S M₀ g \ heavyWit J S M₀ θ g,
          grp J S M₀ g ∩ {p | S.wit p = i}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = (∑ i ∈ srcSet J S M₀ g \ heavySrc J S M₀ θ g, S.Pm (grp J S M₀ g ∩ {p | S.src p = i})) +
        ∑ i ∈ witSet J S M₀ g \ heavyWit J S M₀ θ g, S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}) := by
        rw [grp_src_sum, grp_wit_sum]
    _ ≤ (∑ i ∈ srcSet J S M₀ g \ heavySrc J S M₀ θ g, ENNReal.ofReal (θ g.2.1)) +
        ∑ i ∈ witSet J S M₀ g \ heavyWit J S M₀ θ g, ENNReal.ofReal (θ g.2.1) :=
        add_le_add (Finset.sum_le_sum hlight₁) (Finset.sum_le_sum hlight₂)
    _ ≤ ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [mul_add, mul_comm, mul_comm (((witSet J S M₀ g \ heavyWit J S M₀ θ g).card : ENNReal))]
        apply add_le_add
        · apply mul_le_mul_right
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
        · apply mul_le_mul_right
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset

end HeavyLight

section CoreBound

lemma measurableSet_matchEvents {n₁ n₂ : ℕ} (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (h₁ : ∀ i, IsMatchSheet (f₁ i))
    (h₂ : ∀ i, IsMatchSheet (f₂ i)) (near far : ℝ) :
    MeasurableSet (MatchEvents f₁ f₂ near far) := by
  classical
  let sec : Fin n₁ × Fin n₂ → Set (EuclideanSpace ℝ (Fin 3)) := fun k =>
    (closedBall 0 (1 / 2) ∩
      (fun y : EuclideanSpace ℝ (Fin 3) => ‖f₁ k.1 (emb y) - f₂ k.2 (emb y)‖) ⁻¹' Iic near) ∩
    {_y | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧
      far ≤ ‖f₁ k.1 (emb x) - f₂ k.2 (emb x)‖}
  have hsec : ∀ k, MeasurableSet (sec k) := by
    intro k
    apply MeasurableSet.inter
    · apply IsClosed.measurableSet
      apply ContinuousOn.preimage_isClosed_of_isClosed _ isClosed_closedBall isClosed_Iic
      exact ((continuousOn_sheet_emb (h₁ k.1)).sub (continuousOn_sheet_emb (h₂ k.2))).norm
    · exact MeasurableSet.const _
  have heq : MatchEvents f₁ f₂ near far =
      ⋃ k : Fin n₁ × Fin n₂, {q | q.1 = k} ∩ Prod.snd ⁻¹' (sec k) := by
    ext q
    simp only [MatchEvents, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, sec,
      mem_closedBall, dist_zero_right, mem_Iic]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨q.1, rfl, ⟨h1, h2⟩, h3⟩
    · rintro ⟨k, rfl, ⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun k =>
    ((measurableSet_singleton k).preimage measurable_fst).inter ((hsec k).preimage measurable_snd))

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ) (θ : Λ → ℝ)

lemma exists_of_heavySrc {g : GLabel Λ J} {i : ι} (hθ : 0 < θ g.2.1) (hi : i ∈ heavySrc J S M₀ θ g) :
    ∃ p ∈ grp J S M₀ g, S.src p = i := by
  have h := (Finset.mem_filter.mp hi).2
  have hpos : 0 < S.Pm (grp J S M₀ g ∩ {p | S.src p = i}) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hθ) h
  obtain ⟨p, hp, hpi⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨p, hp, hpi⟩

lemma exists_of_heavyWit {g : GLabel Λ J} {i : ι} (hθ : 0 < θ g.2.1) (hi : i ∈ heavyWit J S M₀ θ g) :
    ∃ p ∈ grp J S M₀ g, S.wit p = i := by
  have h := (Finset.mem_filter.mp hi).2
  have hpos : 0 < S.Pm (grp J S M₀ g ∩ {p | S.wit p = i}) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hθ) h
  obtain ⟨p, hp, hpi⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨p, hp, hpi⟩

/-- The matching hypothesis bounds the retained core of each discrepancy group. -/
theorem core_le {d₀ ε₀ R₀ ε : ℝ} (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀) (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (g : GLabel Λ J) (hM₀ : 0 < M₀) (hθ : 0 < θ g.2.1)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (Γ : ℝ) (hΓ : Γ / θ g.2.1 ≤ (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (d₀ + ε))
    (hband : ∀ i, S.lab i = g.2.1 → S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ g.1)} ≤ ENNReal.ofReal Γ) :
    S.Pm (core J S M₀ θ g) ≤ ENNReal.ofReal (S.ρ g.2.1 *
      (max (heavySrc J S M₀ θ g).card (heavyWit J S M₀ θ g).card : ℕ) *
      (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε)) := by
  classical
  haveI := S.finite
  have hΔ := S.Δ_pos
  set k := g.1 with hk
  set Mk := M₀ * 2 ^ k with hMk_def
  set R := Mk / (2 * S.Δ) with hR_def
  set H₁ := heavySrc J S M₀ θ g with hH₁
  set H₂ := heavyWit J S M₀ θ g with hH₂
  by_cases hne : (core J S M₀ θ g).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact zero_le
  obtain ⟨p₀, hp₀g, hp₀s, hp₀w⟩ := hne
  have hn₁ : 0 < H₁.card := Finset.card_pos.mpr ⟨_, hp₀s⟩
  have hn₂ : 0 < H₂.card := Finset.card_pos.mpr ⟨_, hp₀w⟩
  -- numerical facts
  have hMkpos : 0 < Mk := by positivity
  have hM₀Mk : M₀ ≤ Mk := le_mul_of_one_le_right hM₀.le (one_le_pow₀ (by norm_num))
  have hR0 : R₀ ≤ M₀ / (2 * S.Δ) := by rw [le_div_iff₀ (by positivity)]; exact hR
  have hR0R : M₀ / (2 * S.Δ) ≤ R := div_le_div_of_nonneg_right hM₀Mk (by positivity)
  have hRR : R₀ ≤ R := hR0.trans hR0R
  have hRpos : 0 < R := by linarith
  have hR1 : 1 < R := by linarith
  have hRε : 3 * J.C₂ ≤ R ^ ε :=
    hC.trans (Real.rpow_le_rpow (by positivity) hR0R hε.le)
  have hRε1 : 1 ≤ R ^ ε := Real.one_le_rpow hR1.le hε.le
  have hC₂ := J.hC₂
  have hΔM₀ : S.Δ ≤ M₀ := by nlinarith
  -- enumerations of the heavy labels
  let e₁ : ↥H₁ ≃ Fin H₁.card := H₁.equivFin
  let e₂ : ↥H₂ ≃ Fin H₂.card := H₂.equivFin
  let idx₁ : ι → Fin H₁.card := fun i => if h : i ∈ H₁ then e₁ ⟨i, h⟩ else ⟨0, hn₁⟩
  let idx₂ : ι → Fin H₂.card := fun i => if h : i ∈ H₂ then e₂ ⟨i, h⟩ else ⟨0, hn₂⟩
  have hidx₁ : ∀ i (h : i ∈ H₁), (e₁.symm (idx₁ i)).1 = i := by
    intro i h; simp only [idx₁, h, dite_true, Equiv.symm_apply_apply]
  have hidx₂ : ∀ i (h : i ∈ H₂), (e₂.symm (idx₂ i)).1 = i := by
    intro i h; simp only [idx₂, h, dite_true, Equiv.symm_apply_apply]
  let f₁ : Fin H₁.card → EuclideanSpace ℂ (Fin 3) → ℂ := fun a => S.φ (e₁.symm a).1
  let f₂ : Fin H₂.card → EuclideanSpace ℂ (Fin 3) → ℂ := fun b => S.φ (e₂.symm b).1
  let P₁ : Fin H₁.card → MvPolynomial (Fin 4) ℂ := fun a =>
    Classical.choose (S.sheet (e₁.symm a).1).1
  let P₂ : Fin H₂.card → MvPolynomial (Fin 4) ℂ := fun b =>
    Classical.choose (S.sheet (e₂.symm b).1).1
  set i₀ := S.src p₀ with hi₀
  let f₀ : EuclideanSpace ℝ (Fin 3) → ℂ := fun y => S.φ i₀ (emb y)
  -- the cube of the reference
  have hcube₀ : sheetCube J S.φ M₀ k i₀ = g.2.2.1 := (mem_grp_spec J S M₀ hp₀g hM₀).2.2.2.1
  -- the pushforward measure
  let Φ : Ω → (Fin H₁.card × Fin H₂.card) × EuclideanSpace ℝ (Fin 3) :=
    fun p => ((idx₁ (S.src p), idx₂ (S.wit p)), S.x p)
  have hmeas_idx₁ : Measurable (fun p => idx₁ (S.src p)) := by
    apply measurable_to_countable'
    intro a
    have : (fun p => idx₁ (S.src p)) ⁻¹' {a} =
        ⋃ i ∈ Finset.univ.filter (fun i => idx₁ i = a), {p | S.src p = i} := by
      ext p; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ (fun i _ => S.src_meas i)
  have hmeas_idx₂ : Measurable (fun p => idx₂ (S.wit p)) := by
    apply measurable_to_countable'
    intro a
    have : (fun p => idx₂ (S.wit p)) ⁻¹' {a} =
        ⋃ i ∈ Finset.univ.filter (fun i => idx₂ i = a), {p | S.wit p = i} := by
      ext p; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ (fun i _ => S.wit_meas i)
  have hΦ : Measurable Φ := (hmeas_idx₁.prodMk hmeas_idx₂).prodMk S.x_meas
  let μ := Measure.map Φ (S.Pm.restrict (core J S M₀ θ g))
  haveI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  have hmc := measurableSet_core J S M₀ θ g
  have hμuniv : μ univ = S.Pm (core J S M₀ θ g) := by
    rw [Measure.map_apply hΦ MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
  -- heavy sources share the reference cube; heavy witnesses are close
  have hsrc_cube : ∀ a : Fin H₁.card, sheetCube J S.φ M₀ k (e₁.symm a).1 = g.2.2.1 := by
    intro a
    obtain ⟨p, hp, hpi⟩ := exists_of_heavySrc J S M₀ θ hθ (e₁.symm a).2
    rw [← hpi]
    exact (mem_grp_spec J S M₀ hp hM₀).2.2.2.1
  have hlab₁ : ∀ a : Fin H₁.card, S.lab (e₁.symm a).1 = g.2.1 := by
    intro a
    obtain ⟨p, hp, hpi⟩ := exists_of_heavySrc J S M₀ θ hθ (e₁.symm a).2
    rw [← hpi]
    exact (mem_grp_spec J S M₀ hp hM₀).2.2.1
  have hlab₂ : ∀ b : Fin H₂.card, S.lab (e₂.symm b).1 = g.2.1 := by
    intro b
    obtain ⟨p, hp, hpi⟩ := exists_of_heavyWit J S M₀ θ hθ (e₂.symm b).2
    rw [← hpi, ← S.lab_eq p]
    exact (mem_grp_spec J S M₀ hp hM₀).2.2.1
  have hclose₁ : ∀ a (y : EuclideanSpace ℝ (Fin 3)), ‖y‖ ≤ 1 →
      ‖f₁ a (emb y) - f₀ y‖ ≤ J.C₂ * (Mk / 2) := by
    intro a y hy
    exact close_unit_of_cube_eq J S M₀ hM₀ ((hsrc_cube a).trans hcube₀.symm) y hy
  have hclose₂ : ∀ b (y : EuclideanSpace ℝ (Fin 3)), ‖y‖ ≤ 1 →
      ‖f₂ b (emb y) - f₀ y‖ ≤ J.C₂ * (2 * Mk) + J.C₂ * (Mk / 2) := by
    intro b y hy
    obtain ⟨p, hp, hpi⟩ := exists_of_heavyWit J S M₀ θ hθ (e₂.symm b).2
    obtain ⟨-, hhi, -, hc₁, -⟩ := mem_grp_spec J S M₀ hp hM₀
    have h1 : ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖ ≤ J.C₂ * (2 * Mk) := by
      apply close_unit_of_disc J S (by positivity) _ y hy
      have : M₀ * 2 ^ (k + 1) = 2 * Mk := by rw [hMk_def, pow_succ]; ring
      linarith
    have h2 : ‖S.φ (S.src p) (emb y) - f₀ y‖ ≤ J.C₂ * (Mk / 2) :=
      close_unit_of_cube_eq J S M₀ hM₀ (hc₁.trans hcube₀.symm) y hy
    calc ‖f₂ b (emb y) - f₀ y‖
        = ‖(S.φ (S.src p) (emb y) - f₀ y) - (S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y))‖ := by
          simp only [f₂, ← hpi]; congr 1; ring
      _ ≤ ‖S.φ (S.src p) (emb y) - f₀ y‖ +
          ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖ := norm_sub_le _ _
      _ ≤ J.C₂ * (Mk / 2) + J.C₂ * (2 * Mk) := add_le_add h2 h1
      _ = _ := by ring
  -- cardinality bounds
  have hgrp_le : S.Pm (grp J S M₀ g) ≤ ENNReal.ofReal Γ :=
    (measure_mono (grp_subset_band J S M₀ hp₀g hM₀ hΔM₀)).trans
      (hband i₀ (mem_grp_spec J S M₀ hp₀g hM₀).2.2.1)
  have hcard : ∀ n : ℕ, (n : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ S.Pm (grp J S M₀ g) →
      (n : ℝ) ≤ R ^ (d₀ + ε) := by
    intro n hn
    have h1 : (n : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ ENNReal.ofReal Γ := hn.trans hgrp_le
    have h2 : ENNReal.ofReal (n * θ g.2.1) ≤ ENNReal.ofReal Γ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]; exact h1
    by_cases hΓpos : 0 ≤ Γ
    swap
    · push Not at hΓpos
      rw [ENNReal.ofReal_of_nonpos hΓpos.le] at h1
      have hn0 : n = 0 := by
        by_contra hn0
        have : (0 : ENNReal) < (n : ENNReal) * ENNReal.ofReal (θ g.2.1) :=
          ENNReal.mul_pos (by exact_mod_cast hn0) (ENNReal.ofReal_pos.mpr hθ).ne'
        exact absurd h1 (not_le.mpr this)
      rw [hn0, Nat.cast_zero]
      exact Real.rpow_nonneg hRpos.le _
    have h4 : (n : ℝ) * θ g.2.1 ≤ Γ := (ENNReal.ofReal_le_ofReal_iff hΓpos).mp h2
    have h5 : (n : ℝ) ≤ Γ / θ g.2.1 := by rw [le_div_iff₀ hθ]; exact h4
    exact h5.trans hΓ
  have hn₁R := hcard _ (heavySrc_card_le J S M₀ θ g)
  have hn₂R := hcard _ (heavyWit_card_le J S M₀ θ g)
  rw [← hμuniv]
  apply hmb R Mk ε hRR hMkpos hε hεε₀ H₁.card H₂.card f₁ f₂ P₁ P₂ f₀ (S.ρ g.2.1) μ hn₁R hn₂R
  · -- source sheets
    intro a
    obtain ⟨hP, hdeg, hroot⟩ := Classical.choose_spec (S.sheet (e₁.symm a).1).1
    refine ⟨hP, hdeg, (S.sheet (e₁.symm a).1).2.1, hroot, fun y hy => ⟨?_, ?_⟩⟩
    · exact (S.sheet (e₁.symm a).1).2.2 y hy
    · calc _ ≤ J.C₂ * (Mk / 2) := hclose₁ a y hy
        _ ≤ Mk * R ^ ε := by nlinarith
  · -- witness sheets
    intro b
    obtain ⟨hP, hdeg, hroot⟩ := Classical.choose_spec (S.sheet (e₂.symm b).1).1
    refine ⟨hP, hdeg, (S.sheet (e₂.symm b).1).2.1, hroot, fun y hy => ⟨?_, ?_⟩⟩
    · exact (S.sheet (e₂.symm b).1).2.2 y hy
    · calc _ ≤ J.C₂ * (2 * Mk) + J.C₂ * (Mk / 2) := hclose₂ b y hy
        _ ≤ Mk * R ^ ε := by nlinarith
  · exact S.ρ_nonneg _
  · intro a U hU
    have hset : MeasurableSet {q : (Fin H₁.card × Fin H₂.card) × EuclideanSpace ℝ (Fin 3) |
        q.1.1 = a ∧ q.2 ∈ U} :=
      ((measurableSet_singleton a).preimage (measurable_fst.comp measurable_fst)).inter
        (hU.preimage measurable_snd)
    rw [Measure.map_apply hΦ hset, Measure.restrict_apply (hΦ hset)]
    have hd := S.dens_src (e₁.symm a).1 U hU
    rw [hlab₁ a] at hd
    apply le_trans (measure_mono _) hd
    rintro p ⟨⟨hpa, hpU⟩, hpc⟩
    refine ⟨?_, hpU⟩
    have := hidx₁ (S.src p) hpc.2.1
    simp only [Φ] at hpa
    rw [hpa] at this
    exact this.symm
  · intro b U hU
    have hset : MeasurableSet {q : (Fin H₁.card × Fin H₂.card) × EuclideanSpace ℝ (Fin 3) |
        q.1.2 = b ∧ q.2 ∈ U} :=
      ((measurableSet_singleton b).preimage (measurable_snd.comp measurable_fst)).inter
        (hU.preimage measurable_snd)
    rw [Measure.map_apply hΦ hset, Measure.restrict_apply (hΦ hset)]
    have hd := S.dens_wit (e₂.symm b).1 U hU
    rw [hlab₂ b] at hd
    apply le_trans (measure_mono _) hd
    rintro p ⟨⟨hpb, hpU⟩, hpc⟩
    refine ⟨?_, hpU⟩
    have := hidx₂ (S.wit p) hpc.2.2
    simp only [Φ] at hpb
    rw [hpb] at this
    exact this.symm
  · -- the core is carried by discrepancy events
    have hev := measurableSet_matchEvents f₁ f₂ (fun a => S.sheet _) (fun b => S.sheet _)
      (Mk * R ^ (-1 + ε)) (Mk * R ^ (-ε))
    rw [Measure.map_apply hΦ hev.compl, Measure.restrict_apply (hΦ hev.compl)]
    convert measure_empty (μ := S.Pm)
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro hnot hpc
    apply hnot
    obtain ⟨hpg, hps, hpw⟩ := hpc
    have hs : f₁ (idx₁ (S.src p)) = S.φ (S.src p) := by simp only [f₁, hidx₁ _ hps]
    have hw : f₂ (idx₂ (S.wit p)) = S.φ (S.wit p) := by simp only [f₂, hidx₂ _ hpw]
    obtain ⟨hlo, -, -, -, -⟩ := mem_grp_spec J S M₀ hpg hM₀
    refine ⟨S.x_mem p, ?_, ?_⟩
    · simp only [Φ, hs, hw]
      have hnear : ‖S.φ (S.src p) (emb (S.x p)) - S.φ (S.wit p) (emb (S.x p))‖ ≤ 2 * S.Δ := by
        calc _ = ‖(S.φ (S.src p) (emb (S.x p)) - (S.w p : ℂ)) -
              (S.φ (S.wit p) (emb (S.x p)) - (S.w p : ℂ))‖ := by congr 1; ring
          _ ≤ _ := norm_sub_le _ _
          _ ≤ S.Δ + S.Δ := add_le_add (S.near_src p) (S.near_wit p)
          _ = 2 * S.Δ := by ring
      have hval : Mk * R ^ (-1 + ε) = 2 * S.Δ * R ^ ε := by
        rw [Real.rpow_add hRpos, Real.rpow_neg_one, hR_def]
        field_simp
      rw [hval]
      calc _ ≤ 2 * S.Δ := hnear
        _ ≤ 2 * S.Δ * R ^ ε := le_mul_of_one_le_right (by positivity) hRε1
    · simp only [Φ, hs, hw]
      have hlt : Mk * R ^ (-ε) < sheetDisc S.φ (S.src p) (S.wit p) := by
        have : R ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hR1 (by linarith)
        calc Mk * R ^ (-ε) < Mk * 1 := mul_lt_mul_of_pos_left this hMkpos
          _ = Mk := mul_one _
          _ ≤ _ := hlo
      obtain ⟨y, hy, hlt'⟩ := exists_lt_sheetDisc _ _ hlt
      exact ⟨y, hy, hlt'.le⟩

end CoreBound

section Final

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ) (θ : Λ → ℝ)

lemma rpow_neg_le_of_le {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 ≤ ε) :
    b ^ (-ε) ≤ a ^ (-ε) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.le.trans hab)]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha ε) (Real.rpow_le_rpow ha.le hab hε)

/-- Per group: the group mass is at most twice its light part. -/
lemma grp_le_light {d₀ ε₀ R₀ ε : ℝ} (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀) (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (g : GLabel Λ J) (hM₀ : 0 < M₀) (hθ : 0 < θ g.2.1)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (hρ : S.ρ g.2.1 * (M₀ / (2 * S.Δ)) ^ (-ε) ≤ θ g.2.1 / 2)
    (Γ : ℝ) (hΓ : Γ / θ g.2.1 ≤ (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (d₀ + ε))
    (hband : ∀ i, S.lab i = g.2.1 → S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ g.1)} ≤ ENNReal.ofReal Γ) :
    S.Pm (grp J S M₀ g) ≤
      2 * (ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card)) := by
  haveI := S.finite
  have hΔ := S.Δ_pos
  set m := S.Pm (grp J S M₀ g)
  have hmfin : m ≠ ⊤ := measure_ne_top _ _
  set n := max (heavySrc J S M₀ θ g).card (heavyWit J S M₀ θ g).card
  have hcore := core_le J S M₀ θ hmb hR₀ hε hεε₀ g hM₀ hθ hR hC Γ hΓ hband
  have hR0pos : 0 < M₀ / (2 * S.Δ) := by positivity
  have hRk : M₀ / (2 * S.Δ) ≤ M₀ * 2 ^ g.1 / (2 * S.Δ) :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_right hM₀.le (one_le_pow₀ (by norm_num)))
      (by positivity)
  have hpow := rpow_neg_le_of_le hR0pos hRk hε.le
  have hn : (n : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ m := by
    rcases max_choice (heavySrc J S M₀ θ g).card (heavyWit J S M₀ θ g).card with h | h
    · rw [show n = _ from h]; exact heavySrc_card_le J S M₀ θ g
    · rw [show n = _ from h]; exact heavyWit_card_le J S M₀ θ g
  have hcore' : S.Pm (core J S M₀ θ g) ≤ m / 2 := by
    refine hcore.trans ?_
    have h1 : S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε) ≤ (n : ℝ) * θ g.2.1 / 2 := by
      have := S.ρ_nonneg g.2.1
      calc S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε)
          ≤ S.ρ g.2.1 * (n : ℝ) * (M₀ / (2 * S.Δ)) ^ (-ε) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (n : ℝ) * (S.ρ g.2.1 * (M₀ / (2 * S.Δ)) ^ (-ε)) := by ring
        _ ≤ (n : ℝ) * (θ g.2.1 / 2) := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ = (n : ℝ) * θ g.2.1 / 2 := by ring
    calc ENNReal.ofReal (S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε))
        ≤ ENNReal.ofReal ((n : ℝ) * θ g.2.1 / 2) := ENNReal.ofReal_le_ofReal h1
      _ = (n : ENNReal) * ENNReal.ofReal (θ g.2.1) / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      _ ≤ m / 2 := by gcongr
  have hlight := light_le J S M₀ θ g
  have hsplit : m ≤ S.Pm (core J S M₀ θ g) + S.Pm (grp J S M₀ g \ core J S M₀ θ g) := by
    calc m ≤ S.Pm (core J S M₀ θ g ∪ (grp J S M₀ g \ core J S M₀ θ g)) := by
          apply measure_mono
          intro p hp
          by_cases hc : p ∈ core J S M₀ θ g
          · exact Or.inl hc
          · exact Or.inr ⟨hp, hc⟩
      _ ≤ _ := measure_union_le _ _
  set L := ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card)
  have h2 : m / 2 + m / 2 ≤ m / 2 + L := by
    rw [ENNReal.add_halves]
    exact hsplit.trans (add_le_add hcore' hlight)
  have h3 : m / 2 ≤ L := (ENNReal.add_le_add_iff_left (ENNReal.div_ne_top hmfin (by norm_num))).mp h2
  calc m = 2 * (m / 2) := (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
    _ ≤ 2 * L := by gcongr

/-- The labels of groups containing a given source label. -/
noncomputable def srcLabelsOf (kmax : ℕ) (i : ι) : Finset (GLabel Λ J) :=
  (Finset.range (kmax + 1)).biUnion (fun k =>
    (Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
      Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
        (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
      (fun Q => (k, S.lab i, sheetCube J S.φ M₀ k i, Q)))

/-- The labels of groups containing a given witness label. -/
noncomputable def witLabelsOf (kmax : ℕ) (i : ι) : Finset (GLabel Λ J) :=
  (Finset.range (kmax + 1)).biUnion (fun k =>
    (Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
      Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
        (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
      (fun Q => (k, S.lab i, Q, sheetCube J S.φ M₀ k i)))

lemma card_box (a : ↥J.V × Fin J.q → ℤ) :
    (Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
      Finset.Icc (a vj - cubeRadius J) (a vj + cubeRadius J))).card =
      (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) := by
  rw [Fintype.card_piFinset]
  have h : ∀ vj : ↥J.V × Fin J.q,
      (Finset.Icc (a vj - cubeRadius J) (a vj + cubeRadius J)).card = 2 * cubeRadius J + 1 := by
    intro vj; rw [Int.card_Icc]; omega
  simp only [h, Finset.prod_const, Finset.card_univ]

lemma card_srcLabelsOf_le (kmax : ℕ) (i : ι) :
    (srcLabelsOf J S M₀ kmax i).card ≤
      (kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) := by
  calc _ ≤ ∑ k ∈ Finset.range (kmax + 1), ((Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
        Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
          (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
        (fun Q => (k, S.lab i, sheetCube J S.φ M₀ k i, Q))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (kmax + 1),
        (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) := by
        apply Finset.sum_le_sum
        intro k _
        exact Finset.card_image_le.trans (card_box J _).le
    _ = _ := by simp

lemma card_witLabelsOf_le (kmax : ℕ) (i : ι) :
    (witLabelsOf J S M₀ kmax i).card ≤
      (kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) := by
  calc _ ≤ ∑ k ∈ Finset.range (kmax + 1), ((Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
        Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
          (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
        (fun Q => (k, S.lab i, Q, sheetCube J S.φ M₀ k i))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (kmax + 1),
        (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) := by
        apply Finset.sum_le_sum
        intro k _
        exact Finset.card_image_le.trans (card_box J _).le
    _ = _ := by simp

lemma mem_srcLabelsOf {kmax : ℕ} (hM₀ : 0 < M₀)
    (hrange : ∀ i i', sheetDisc S.φ i i' < M₀ * 2 ^ (kmax + 1))
    {g : GLabel Λ J} {i : ι} (hi : i ∈ srcSet J S M₀ g) : g ∈ srcLabelsOf J S M₀ kmax i := by
  classical
  simp only [srcSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨p, hp, hpi⟩ := hi
  have hspec := mem_grp_spec J S M₀ hp hM₀
  have hk : g.1 ≤ kmax := by
    have hg := hp.2
    rw [← hg]
    exact discScale_le hM₀ hp.1 (hrange _ _)
  simp only [srcLabelsOf, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨g.1, by omega, g.2.2.2, fun vj => ?_, ?_⟩
  · have hn := cube_neighbor J S M₀ hp hM₀ vj
    rw [hpi] at hspec
    rw [hspec.2.2.2.1]
    constructor <;> linarith [abs_le.mp hn]
  · rw [← hpi, hspec.2.2.1, hspec.2.2.2.1]

lemma mem_witLabelsOf {kmax : ℕ} (hM₀ : 0 < M₀)
    (hrange : ∀ i i', sheetDisc S.φ i i' < M₀ * 2 ^ (kmax + 1))
    {g : GLabel Λ J} {i : ι} (hi : i ∈ witSet J S M₀ g) : g ∈ witLabelsOf J S M₀ kmax i := by
  classical
  simp only [witSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨p, hp, hpi⟩ := hi
  have hspec := mem_grp_spec J S M₀ hp hM₀
  have hk : g.1 ≤ kmax := by
    have hg := hp.2
    rw [← hg]
    exact discScale_le hM₀ hp.1 (hrange _ _)
  simp only [witLabelsOf, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨g.1, by omega, g.2.2.1, fun vj => ?_, ?_⟩
  · have hn := cube_neighbor J S M₀ hp hM₀ vj
    rw [hpi] at hspec
    rw [hspec.2.2.2.2]
    constructor <;> linarith [abs_le.mp hn]
  · rw [← hpi, ← S.lab_eq p, hspec.2.2.1, hspec.2.2.2.2]

lemma lab_of_mem_srcSet {g : GLabel Λ J} {i : ι} (hM₀ : 0 < M₀) (hi : i ∈ srcSet J S M₀ g) :
    S.lab i = g.2.1 := by
  classical
  simp only [srcSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨p, hp, hpi⟩ := hi
  rw [← hpi]
  exact (mem_grp_spec J S M₀ hp hM₀).2.2.1

lemma lab_of_mem_witSet {g : GLabel Λ J} {i : ι} (hM₀ : 0 < M₀) (hi : i ∈ witSet J S M₀ g) :
    S.lab i = g.2.1 := by
  classical
  simp only [witSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨p, hp, hpi⟩ := hi
  rw [← hpi, ← S.lab_eq p]
  exact (mem_grp_spec J S M₀ hp hM₀).2.2.1

lemma sum_theta_srcSet_le {kmax : ℕ} (hM₀ : 0 < M₀) (hθ0 : ∀ l, 0 ≤ θ l)
    (hrange : ∀ i i', sheetDisc S.φ i i' < M₀ * 2 ^ (kmax + 1)) :
    ∑ g ∈ groupLabels J S M₀, θ g.2.1 * ((srcSet J S M₀ g).card : ℝ) ≤
      (((kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) *
        ∑ i : ι, θ (S.lab i) := by
  classical
  calc ∑ g ∈ groupLabels J S M₀, θ g.2.1 * ((srcSet J S M₀ g).card : ℝ)
      = ∑ g ∈ groupLabels J S M₀, ∑ i : ι, if i ∈ srcSet J S M₀ g then θ (S.lab i) else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.sum_congr rfl (fun i hi => by rw [lab_of_mem_srcSet J S M₀ hM₀ hi])]
        simp [mul_comm]
    _ = ∑ i : ι, ∑ g ∈ groupLabels J S M₀, if i ∈ srcSet J S M₀ g then θ (S.lab i) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ i : ι, θ (S.lab i) *
        (((kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (hθ0 _)
        have hsub : (groupLabels J S M₀).filter (fun g => i ∈ srcSet J S M₀ g) ⊆
            srcLabelsOf J S M₀ kmax i := by
          intro g hg
          exact mem_srcLabelsOf J S M₀ hM₀ hrange (Finset.mem_filter.mp hg).2
        exact_mod_cast (Finset.card_le_card hsub).trans (card_srcLabelsOf_le J S M₀ kmax i)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma sum_theta_witSet_le {kmax : ℕ} (hM₀ : 0 < M₀) (hθ0 : ∀ l, 0 ≤ θ l)
    (hrange : ∀ i i', sheetDisc S.φ i i' < M₀ * 2 ^ (kmax + 1)) :
    ∑ g ∈ groupLabels J S M₀, θ g.2.1 * ((witSet J S M₀ g).card : ℝ) ≤
      (((kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) *
        ∑ i : ι, θ (S.lab i) := by
  classical
  calc ∑ g ∈ groupLabels J S M₀, θ g.2.1 * ((witSet J S M₀ g).card : ℝ)
      = ∑ g ∈ groupLabels J S M₀, ∑ i : ι, if i ∈ witSet J S M₀ g then θ (S.lab i) else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.sum_congr rfl (fun i hi => by rw [lab_of_mem_witSet J S M₀ hM₀ hi])]
        simp [mul_comm]
    _ = ∑ i : ι, ∑ g ∈ groupLabels J S M₀, if i ∈ witSet J S M₀ g then θ (S.lab i) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ i : ι, θ (S.lab i) *
        (((kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (hθ0 _)
        have hsub : (groupLabels J S M₀).filter (fun g => i ∈ witSet J S M₀ g) ⊆
            witLabelsOf J S M₀ kmax i := by
          intro g hg
          exact mem_witLabelsOf J S M₀ hM₀ hrange (Finset.mem_filter.mp hg).2
        exact_mod_cast (Finset.card_le_card hsub).trans (card_witLabelsOf_le J S M₀ kmax i)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

/-- **Discrepancy mass bound.** Pairs whose source and witness sheets differ by at least
`M₀` somewhere on the real half ball have total mass at most
`4 (kmax + 1) (2 r + 1)^N ∑ᵢ θ (lab i)`, with `r, N` depending only on the jet constants. -/
theorem discrepancy_mass_le {d₀ ε₀ R₀ ε : ℝ} (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀) (hθ : ∀ l, 0 < θ l)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (hρ : ∀ l, S.ρ l * (M₀ / (2 * S.Δ)) ^ (-ε) ≤ θ l / 2)
    (Γ : Λ → ℕ → ℝ) (hΓ : ∀ l (k : ℕ), Γ l k / θ l ≤ (M₀ * 2 ^ k / (2 * S.Δ)) ^ (d₀ + ε))
    (hband : ∀ i (k : ℕ), S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤ ENNReal.ofReal (Γ (S.lab i) k))
    (kmax : ℕ) (hrange : ∀ i i', sheetDisc S.φ i i' < M₀ * 2 ^ (kmax + 1)) :
    S.Pm {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
        M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖} ≤
      ENNReal.ofReal (4 * ((kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q)) *
        ∑ i : ι, θ (S.lab i)) := by
  classical
  set X : ℕ := (kmax + 1) * (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q)
  have hθ0 : ∀ l, 0 ≤ θ l := fun l => (hθ l).le
  have hsub : {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
        M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖} ⊆
      ⋃ g ∈ groupLabels J S M₀, grp J S M₀ g := by
    intro p ⟨y, hy, hle⟩
    exact bad_subset_iUnion_grp J S M₀ (hle.trans (le_sheetDisc S.sheet _ _ hy))
  have hunion : S.Pm (⋃ g ∈ groupLabels J S M₀, grp J S M₀ g) =
      ∑ g ∈ groupLabels J S M₀, S.Pm (grp J S M₀ g) := by
    apply measure_biUnion_finset
    · intro g _ g' _ hgg'
      exact disjoint_grp J S M₀ hgg'
    · intro g _
      exact measurableSet_grp J S M₀ g
  have hs := sum_theta_srcSet_le J S M₀ θ hM₀ hθ0 hrange
  have hw := sum_theta_witSet_le J S M₀ θ hM₀ hθ0 hrange
  have hgrp : ∀ g ∈ groupLabels J S M₀, S.Pm (grp J S M₀ g) ≤
      ENNReal.ofReal (2 * (θ g.2.1 * (srcSet J S M₀ g).card + θ g.2.1 * (witSet J S M₀ g).card)) := by
    intro g _
    refine (grp_le_light J S M₀ θ hmb hR₀ hε hεε₀ g hM₀ (hθ _) hR hC (hρ _)
      (Γ g.2.1 g.1) (hΓ _ _) ?_).trans (le_of_eq ?_)
    · intro i hi
      rw [← hi]; exact hband i g.1
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add
        (mul_nonneg (hθ0 _) (Nat.cast_nonneg _)) (mul_nonneg (hθ0 _) (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul (hθ0 _), ENNReal.ofReal_mul (hθ0 _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, mul_add]
  calc _ ≤ S.Pm (⋃ g ∈ groupLabels J S M₀, grp J S M₀ g) := measure_mono hsub
    _ = ∑ g ∈ groupLabels J S M₀, S.Pm (grp J S M₀ g) := hunion
    _ ≤ ∑ g ∈ groupLabels J S M₀, ENNReal.ofReal
        (2 * (θ g.2.1 * (srcSet J S M₀ g).card + θ g.2.1 * (witSet J S M₀ g).card)) :=
        Finset.sum_le_sum hgrp
    _ = ENNReal.ofReal (∑ g ∈ groupLabels J S M₀,
        2 * (θ g.2.1 * (srcSet J S M₀ g).card + θ g.2.1 * (witSet J S M₀ g).card)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro g _
        have := hθ0 g.2.1
        positivity
    _ ≤ ENNReal.ofReal (4 * X * ∑ i : ι, θ (S.lab i)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have : (4 : ℝ) * X * ∑ i : ι, θ (S.lab i) =
            2 * ((X : ℝ) * ∑ i : ι, θ (S.lab i) + (X : ℝ) * ∑ i : ι, θ (S.lab i)) := by ring
        rw [this]
        gcongr
    _ = _ := by simp only [X]; push_cast; ring_nf

end Final

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
