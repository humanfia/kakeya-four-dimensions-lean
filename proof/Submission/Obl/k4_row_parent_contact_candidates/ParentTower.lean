/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ParentTower.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.RowParent
import Submission.Obl.k4_row_parent_contact_candidates.TowerPruning

/-!
# The tower of descendants of a parent

Fix a parent label `Q` at depth `r` and finitely many deeper depths `s j`.
The descendants of `Q` at these depths form a finite label tower with boxes
`B × I` and reference weights `q ν(A)`. This file verifies the hypotheses of
`TowerPruning` for it from the atlases and the nesting of the prepared model:
descendant budgets, generic ancestor relations, coverage of the parent box and
uniqueness of ancestors.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

open PreparedModel

variable {α : Type} [MeasurableSpace α]

section Tower

variable (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
  {M : ℕ} (s : Fin M → ℝ)

/-- Descendants of `Q` at depth `s j`. -/
abbrev TowerLabel := Σ j : Fin M, {i : Fin (a.n k (s j)) //
  i ∈ descSet (a.A k (s j)) (a.j k (s j)) (a.A k r Q) (a.T k r) (a.j k r Q)}

variable {p a k r Q s}

/-- Level of a tower label. -/
def towerLv (x : TowerLabel a k r Q s) : ℕ := (x.1 : ℕ)

/-- Incidence box of a tower label. -/
def towerBox (x : TowerLabel a k r Q s) : Set (α × ℝ) :=
  a.B k (s x.1) x.2.1 ×ˢ a.block k (s x.1) x.2.1

/-- Prior set of a tower label. -/
def towerPrior (x : TowerLabel a k r Q s) : Set α := a.A k (s x.1) x.2.1

/-- Time block of a tower label. -/
def towerBlock (x : TowerLabel a k r Q s) : Set ℝ := a.block k (s x.1) x.2.1

/-- Reference weight of a tower label. -/
def towerWeight (x : TowerLabel a k r Q s) : ℝ≥0∞ :=
  ENNReal.ofReal (a.q k (s x.1)) * a.nu k (a.A k (s x.1) x.2.1)

/-- Ancestor relation in the tower. -/
def towerAnc (x y : TowerLabel a k r Q s) : Prop :=
  towerLv x < towerLv y ∧ towerPrior y ⊆ towerPrior x ∧ towerBlock y ⊆ towerBlock x

/-- Dyadic endpoints of all levels of the tower. -/
def towerPoints (a : PreparedModel α) (k : ℕ) {M : ℕ} (s : Fin M → ℝ) : Set ℝ :=
  ⋃ j : Fin M, dyadicPoints (a.T k (s j))

theorem towerPoints_countable : (towerPoints a k s).Countable :=
  countable_iUnion fun _ => dyadicPoints_countable _

/-- Two labels of the same depth either coincide or meet only on a null set:
disjoint priors in the same block, or distinct blocks meeting at an endpoint. -/
theorem same_depth_meet {R s₀ : ℝ} (hat : a.AtlasAt p R k s₀) {i i' : Fin (a.n k s₀)}
    (hne : i ≠ i') {l : α} (hl : l ∈ a.A k s₀ i) (hl' : l ∈ a.A k s₀ i') {t : ℝ}
    (ht : t ∈ a.block k s₀ i) (ht' : t ∈ a.block k s₀ i') :
    t ∈ dyadicPoints (a.T k s₀) := by
  by_cases hj : a.j k s₀ i = a.j k s₀ i'
  · exact absurd hl' (Set.disjoint_left.mp (hat.disjoint i i' hne hj) hl)
  · exact mem_dyadicPoints_of_mem_inter hj ht ht'

/-- Sums over the tower labels of one level, as sums over descendants of `Q`. -/
theorem sum_tower_level (f : TowerLabel a k r Q s → ℝ≥0∞) (jj : Fin M)
    (Φ : TowerLabel a k r Q s → Prop) [DecidablePred Φ] :
    ∑ y ∈ Finset.univ.filter (fun y => towerLv y = (jj : ℕ) ∧ Φ y), f y =
      ∑ i ∈ Finset.univ.filter (fun i => Φ ⟨jj, i⟩), f ⟨jj, i⟩ := by
  classical
  have hinj : Set.InjOn (fun i => (⟨jj, i⟩ : TowerLabel a k r Q s))
      (Finset.univ.filter (fun i => Φ ⟨jj, i⟩) : Set _) := by
    intro i _ i' _ h
    simpa using h
  rw [← Finset.sum_image hinj]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hy, hΦ⟩
    rcases y with ⟨j', i⟩
    have : j' = jj := Fin.ext hy
    subst this
    exact ⟨i, hΦ, rfl⟩
  · rintro ⟨i, hΦ, rfl⟩
    exact ⟨rfl, hΦ⟩

open Classical in
/-- Descendant budget inside the tower. -/
theorem tower_desc_budget {R : ℝ} (hat : ∀ jj : Fin M, a.AtlasAt p R k (s jj))
    (x : TowerLabel a k r Q s) (j : ℕ) (_hj : towerLv x < j) :
    ∑ y ∈ Finset.univ.filter (fun y => towerLv y = j ∧ towerAnc x y), towerWeight y ≤
      towerWeight x := by
  classical
  by_cases hjM : j < M
  · set jj : Fin M := ⟨j, hjM⟩
    have e := sum_tower_level (towerWeight (a := a) (k := k) (r := r) (Q := Q) (s := s)) jj
      (fun y => towerAnc x y)
    simp only [jj] at e
    rw [e]
    calc ∑ i ∈ Finset.univ.filter (fun i => towerAnc x ⟨jj, i⟩), towerWeight ⟨jj, i⟩
        = ∑ i ∈ (Finset.univ.filter (fun i => towerAnc x ⟨jj, i⟩)).map
            (Function.Embedding.subtype _), ENNReal.ofReal (2 ^ (-(a.T k (s jj) : ℤ)) : ℝ) *
              a.nu k (a.A k (s jj) i) := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ i ∈ descSet (a.A k (s jj)) (a.j k (s jj)) (towerPrior x) (a.T k (s x.1))
            (a.j k (s x.1) x.2.1), ENNReal.ofReal (2 ^ (-(a.T k (s jj) : ℤ)) : ℝ) *
              a.nu k (a.A k (s jj) i) := by
          apply Finset.sum_le_sum_of_subset
          intro i hi
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coe_subtype] at hi
          obtain ⟨i', hanc, rfl⟩ := hi
          exact mem_descSet.mpr ⟨hanc.2.1, hanc.2.2⟩
      _ ≤ ENNReal.ofReal (2 ^ (-(a.T k (s x.1) : ℤ)) : ℝ) * a.nu k (towerPrior x) :=
          sum_desc_le (a.nu k) (a.A k (s jj)) (a.j k (s jj)) (hat jj).measurable_A
            (hat jj).disjoint (towerPrior x) (a.T k (s x.1)) (a.j k (s x.1) x.2.1)
      _ = towerWeight x := rfl
  · have : Finset.univ.filter (fun y : TowerLabel a k r Q s => towerLv y = j ∧ towerAnc x y) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro hy
      exact absurd (hy ▸ y.1.2) hjM
    rw [this, Finset.sum_empty]
    exact zero_le

/-- Root budget: all tower labels of one level weigh at most the parent. -/
theorem tower_root_budget {R : ℝ} (hat : ∀ jj : Fin M, a.AtlasAt p R k (s jj)) (j : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : TowerLabel a k r Q s => towerLv y = j), towerWeight y ≤
      ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q) := by
  classical
  by_cases hjM : j < M
  · set jj : Fin M := ⟨j, hjM⟩
    have e := sum_tower_level (towerWeight (a := a) (k := k) (r := r) (Q := Q) (s := s)) jj
      (fun _ => True)
    simp only [and_true, jj] at e
    rw [e]
    calc ∑ i ∈ Finset.univ.filter (fun _ => True), towerWeight (⟨jj, i⟩ : TowerLabel a k r Q s)
        = ∑ i ∈ (Finset.univ.filter (fun _ => True)).map (Function.Embedding.subtype _),
            ENNReal.ofReal (2 ^ (-(a.T k (s jj) : ℤ)) : ℝ) * a.nu k (a.A k (s jj) i) := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ i ∈ descSet (a.A k (s jj)) (a.j k (s jj)) (a.A k r Q) (a.T k r) (a.j k r Q),
            ENNReal.ofReal (2 ^ (-(a.T k (s jj) : ℤ)) : ℝ) * a.nu k (a.A k (s jj) i) := by
          apply Finset.sum_le_sum_of_subset
          intro i hi
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coe_subtype] at hi
          obtain ⟨i', rfl⟩ := hi
          exact i'.2
      _ ≤ ENNReal.ofReal (2 ^ (-(a.T k r : ℤ)) : ℝ) * a.nu k (a.A k r Q) :=
          sum_desc_le (a.nu k) (a.A k (s jj)) (a.j k (s jj)) (hat jj).measurable_A
            (hat jj).disjoint (a.A k r Q) (a.T k r) (a.j k r Q)
      _ = ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q) := rfl
  · have : Finset.univ.filter (fun y : TowerLabel a k r Q s => towerLv y = j) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hy
      exact absurd (hy ▸ y.1.2) hjM
    rw [this, Finset.sum_empty]
    exact zero_le

/-- A dyadic block is not contained in the countable set of endpoints. -/
theorem exists_mem_block_not_dyadic (T : ℕ) (j : Fin (2 ^ T)) (E : Set ℝ) (hE : E.Countable) :
    ∃ t ∈ interval T j, t ∉ E := by
  by_contra h
  push Not at h
  have hsub : interval T j ⊆ E := fun t ht => h t ht
  have h1 : volume (interval T j) = 0 := measure_mono_null hsub (hE.measure_zero _)
  rw [interval_eq] at h1
  rw [Real.volume_Icc] at h1
  have : (0 : ℝ) < (2 : ℝ) ^ (-(T : ℤ)) := by positivity
  simp only [ENNReal.ofReal_eq_zero] at h1
  linarith

/-- Generic incidences see only nested labels of the tower. -/
theorem tower_generic {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)} {K : ℝ≥0∞}
    (hμ : μ ≤ K • ν.prod volume) {R : ℝ} (hat : ∀ jj : Fin M, a.AtlasAt p R k (s jj))
    (hnest : ∀ j j' : Fin M, j < j' → ∀ i : Fin (a.n k (s j')), ∃ h : Fin (a.n k (s j)),
      a.A k (s j') i ⊆ a.A k (s j) h ∧ a.block k (s j') i ⊆ a.block k (s j) h)
    (G : Set (α × ℝ)) :
    ∀ᵐ z ∂μ, z ∈ G → ∀ x y : TowerLabel a k r Q s, z ∈ towerBox x → z ∈ towerBox y →
      (towerLv x < towerLv y → towerAnc x y) ∧ (towerLv x = towerLv y → x = y) := by
  have hnull : ∀ᵐ z ∂μ, z.2 ∉ towerPoints a k s := by
    rw [ae_iff]
    simp only [not_not]
    have : {z : α × ℝ | z.2 ∈ towerPoints a k s} = univ ×ˢ towerPoints a k s := by
      ext z; simp
    rw [this]
    apply le_antisymm _ zero_le
    calc μ (univ ×ˢ towerPoints a k s) ≤ (K • ν.prod volume) (univ ×ˢ towerPoints a k s) := hμ _
      _ = 0 := by
          rw [Measure.smul_apply, Measure.prod_prod,
            (towerPoints_countable (a := a) (k := k) (s := s)).measure_zero, mul_zero, smul_zero]
  filter_upwards [hnull] with z hz _ x y hx hy
  have hpts : ∀ jj : Fin M, z.2 ∉ dyadicPoints (a.T k (s jj)) := by
    intro jj hjj
    exact hz (mem_iUnion.mpr ⟨jj, hjj⟩)
  obtain ⟨hxB, hxI⟩ := hx
  obtain ⟨hyB, hyI⟩ := hy
  constructor
  · intro hlt
    obtain ⟨h, hAh, hIh⟩ := hnest x.1 y.1 hlt y.2.1
    have hzA : z.1 ∈ a.A k (s x.1) h := hAh ((hat y.1).B_sub_A _ hyB)
    have hzI : z.2 ∈ a.block k (s x.1) h := hIh hyI
    by_cases hhx : h = x.2.1
    · subst hhx
      exact ⟨hlt, hAh, hIh⟩
    · exact absurd (same_depth_meet (hat x.1) hhx hzA ((hat x.1).B_sub_A _ hxB) hzI hxI)
        (hpts x.1)
  · intro heq
    rcases x with ⟨jx, ix, hix⟩
    rcases y with ⟨jy, iy, hiy⟩
    have hj : jx = jy := Fin.ext heq
    subst hj
    by_cases hii : ix = iy
    · subst hii; rfl
    · exact absurd (same_depth_meet (hat jx) hii ((hat jx).B_sub_A _ hxB)
        ((hat jx).B_sub_A _ hyB) hxI hyI) (hpts jx)

/-- Inside the parent box every level of the tower covers generically. -/
theorem tower_cover {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)} {K : ℝ≥0∞}
    (hμ : μ ≤ K • ν.prod volume) {R : ℝ} (hatr : a.AtlasAt p R k r)
    (hat : ∀ jj : Fin M, a.AtlasAt p R k (s jj))
    (hcov : ∀ jj : Fin M, ∀ᵐ z ∂μ, ∃ i, z.1 ∈ a.B k (s jj) i ∧ z.2 ∈ a.block k (s jj) i)
    (hnestr : ∀ jj : Fin M, ∀ i : Fin (a.n k (s jj)), ∃ h : Fin (a.n k r),
      a.A k (s jj) i ⊆ a.A k r h ∧ a.block k (s jj) i ⊆ a.block k r h)
    {G : Set (α × ℝ)} (hG : G ⊆ a.A k r Q ×ˢ a.block k r Q) :
    ∀ᵐ z ∂μ, z ∈ G → ∀ j < M, ∃ x : TowerLabel a k r Q s, towerLv x = j ∧ z ∈ towerBox x := by
  have h := fun jj : Fin M => ae_desc_cover hμ (a.A k (s jj)) (a.B k (s jj)) (a.j k (s jj))
    (hat jj).B_sub_A (hcov jj) (a.A k r) (a.j k r) hatr.disjoint (hnestr jj) Q
  rw [← ae_all_iff] at h
  filter_upwards [h] with z hz hzG j hj
  obtain ⟨hzA, hzI⟩ := hG hzG
  obtain ⟨i, hi, hiB, hiI⟩ := hz ⟨j, hj⟩ hzA hzI
  exact ⟨⟨⟨j, hj⟩, i, hi⟩, rfl, hiB, hiI⟩

/-- Ancestors in the tower are unique at each level. -/
theorem tower_anc_unique {R : ℝ} (hat : ∀ jj : Fin M, a.AtlasAt p R k (s jj))
    (x y y' : TowerLabel a k r Q s) (hy : towerAnc y x) (hy' : towerAnc y' x)
    (hlv : towerLv y = towerLv y') (hne : (towerBox x).Nonempty) : y = y' := by
  obtain ⟨⟨l, t⟩, hlB, _⟩ := hne
  obtain ⟨t', ht', ht'E⟩ := exists_mem_block_not_dyadic (a.T k (s x.1)) (a.j k (s x.1) x.2.1)
    (towerPoints a k s) towerPoints_countable
  have hlA : l ∈ a.A k (s x.1) x.2.1 := (hat x.1).B_sub_A _ hlB
  rcases y with ⟨jy, iy, hiy⟩
  rcases y' with ⟨jy', iy', hiy'⟩
  have hj : jy = jy' := Fin.ext hlv
  subst hj
  by_cases hii : iy = iy'
  · subst hii; rfl
  · exfalso
    have hl1 : l ∈ a.A k (s jy) iy := hy.2.1 hlA
    have hl2 : l ∈ a.A k (s jy) iy' := hy'.2.1 hlA
    have ht1 : t' ∈ a.block k (s jy) iy := hy.2.2 ht'
    have ht2 : t' ∈ a.block k (s jy) iy' := hy'.2.2 ht'
    exact ht'E (mem_iUnion.mpr ⟨jy, same_depth_meet (hat jy) hii hl1 hl2 ht1 ht2⟩)

end Tower

end

end Submission.Obl.k4_row_parent_contact_candidates
