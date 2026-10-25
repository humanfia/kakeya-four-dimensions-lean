-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.Tucker.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.Statements

/-!
# Tucker's lemma on the grid (Freund–Todd argument)

Simplices are finite sets of integer points lying in a common closed orthant whose absolute-value
vectors form a chain with all coordinate gaps at most `1` (the Kuhn triangulation of each orthant
box in `|x|`-coordinates). `sgnSupp σ` is the set of signed coordinates `(i, b)` used by points of
`σ` (`b = true` for positive coordinates). A simplex is *happy* if `sgnSupp σ ⊆ lab '' σ`.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod

namespace Tucker

variable {n : ℕ}

/-- `x` and `y` lie in a common simplex. -/
def Compat (x y : Fin n → ℤ) : Prop :=
  (∀ i, 0 ≤ x i * y i) ∧ ((∀ i, |x i| ≤ |y i|) ∨ (∀ i, |y i| ≤ |x i|)) ∧
    ∀ i, |x i| ≤ |y i| + 1 ∧ |y i| ≤ |x i| + 1

def IsSimplex (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ ∀ x ∈ σ, ∀ y ∈ σ, Compat x y

/-- Signed support of a point. -/
def ptSupp (x : Fin n → ℤ) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun p => x p.1 ≠ 0 ∧ (p.2 = true ↔ 0 < x p.1))

/-- Signed support of a set of points. -/
def sgnSupp (σ : Finset (Fin n → ℤ)) : Finset (Fin n × Bool) := σ.biUnion ptSupp

def flipL (ℓ : Fin n × Bool) : Fin n × Bool := (ℓ.1, !ℓ.2)

/-- `σ` lies in a boundary face of the cube `[-m, m]^n`. -/
def IsBdry (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop := ∃ i, ∀ x ∈ σ, |x i| = (m : ℤ)

def grid (n m : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(m : ℤ)) m)

theorem mem_grid {m : ℕ} {x : Fin n → ℤ} : x ∈ grid n m ↔ ∀ i, |x i| ≤ (m : ℤ) := by
  simp [grid, Fintype.mem_piFinset, abs_le]


/-! ## Combinatorial lemmas (part A) -/

theorem isSimplex_of_subset {σ τ : Finset (Fin n → ℤ)} (h : IsSimplex σ) (hτ : τ ⊆ σ)
    (hne : τ.Nonempty) : IsSimplex τ :=
  ⟨hne, fun x hx y hy => h.2 x (hτ hx) y (hτ hy)⟩

theorem sgnSupp_mono {σ τ : Finset (Fin n → ℤ)} (h : σ ⊆ τ) : sgnSupp σ ⊆ sgnSupp τ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem abs_sub_le_one_of_mem {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) {x y : Fin n → ℤ}
    (hx : x ∈ σ) (hy : y ∈ σ) (i : Fin n) : |x i - y i| ≤ 1 := by
  obtain ⟨h1, -, h3⟩ := h.2 x hx y hy
  have h1 := h1 i
  obtain ⟨h3, h4⟩ := h3 i
  rw [abs_le]
  rcases mul_nonneg_iff.1 h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at h3 h4
    constructor <;> linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h3 h4
    constructor <;> linarith

/-! ### Helper API for part A -/

namespace TA

theorem compat_symm {x y : Fin n → ℤ} (h : Compat x y) : Compat y x :=
  ⟨fun i => by rw [mul_comm]; exact h.1 i, h.2.1.symm, fun i => (h.2.2 i).symm⟩

theorem compat_self (x : Fin n → ℤ) : Compat x x :=
  ⟨fun i => mul_self_nonneg _, Or.inl fun _ => le_rfl, fun _ => ⟨by linarith, by linarith⟩⟩

/-- Total weight `∑ |x i|`. -/
def wt (x : Fin n → ℤ) : ℤ := ∑ i, |x i|

theorem wt_le_wt {x y : Fin n → ℤ} (h : ∀ i, |x i| ≤ |y i|) : wt x ≤ wt y :=
  Finset.sum_le_sum fun i _ => h i

theorem eq_of_abs_eq_of_mul_nonneg {a c : ℤ} (h1 : 0 ≤ a * c) (h2 : |a| = |c|) : a = c := by
  rcases mul_nonneg_iff.1 h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rwa [abs_of_nonneg ha, abs_of_nonneg hb] at h2
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h2; linarith

theorem eq_of_abs_eq {x y : Fin n → ℤ} (h1 : ∀ i, 0 ≤ x i * y i) (h2 : ∀ i, |x i| = |y i|) :
    x = y := funext fun i => eq_of_abs_eq_of_mul_nonneg (h1 i) (h2 i)

theorem abs_le_of_wt_le {x y : Fin n → ℤ} (h : Compat x y) (hw : wt x ≤ wt y) :
    ∀ i, |x i| ≤ |y i| := by
  rcases h.2.1 with h' | h'
  · exact h'
  · have heq : ∑ i, |y i| = ∑ i, |x i| := le_antisymm (Finset.sum_le_sum fun i _ => h' i) hw
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h' i)).1 heq
    intro i
    exact (this i (Finset.mem_univ i)).ge

theorem eq_of_compat_of_wt_eq {x y : Fin n → ℤ} (h : Compat x y) (hw : wt x = wt y) : x = y :=
  eq_of_abs_eq h.1 fun i =>
    le_antisymm (abs_le_of_wt_le h hw.le i) (abs_le_of_wt_le (compat_symm h) hw.ge i)

theorem exists_top {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) :
    ∃ T ∈ σ, ∀ x ∈ σ, ∀ i, |x i| ≤ |T i| := by
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image σ wt h.1
  exact ⟨T, hT, fun x hx => abs_le_of_wt_le (h.2 x hx T hT) (hmax x hx)⟩

theorem exists_bot {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) :
    ∃ B ∈ σ, ∀ x ∈ σ, ∀ i, |B i| ≤ |x i| := by
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image σ wt h.1
  exact ⟨B, hB, fun x hx => abs_le_of_wt_le (h.2 B hB x hx) (hmin x hx)⟩

theorem mem_ptSupp {x : Fin n → ℤ} {i : Fin n} {b : Bool} :
    (i, b) ∈ ptSupp x ↔ x i ≠ 0 ∧ (b = true ↔ 0 < x i) := by
  simp only [ptSupp, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_sgnSupp {σ : Finset (Fin n → ℤ)} {p : Fin n × Bool} :
    p ∈ sgnSupp σ ↔ ∃ x ∈ σ, p ∈ ptSupp x := by
  simp only [sgnSupp, Finset.mem_biUnion]

theorem pos_iff_of_mul_pos {a c : ℤ} (h : 0 < a * c) : (0 < a ↔ 0 < c) := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h' => absurd h' (not_lt.2 h1.le), fun h' => absurd h' (not_lt.2 h2.le)⟩

theorem ne_zero_of_mul_pos_right {a c : ℤ} (h : 0 < a * c) : c ≠ 0 := by
  rintro rfl; rw [mul_zero] at h; exact lt_irrefl 0 h

theorem mul_pos_of_pos_iff {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) (h : 0 < a ↔ 0 < c) :
    0 < a * c := by
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · have : ¬ 0 < c := fun h' => absurd (h.2 h') (not_lt.2 ha'.le)
    exact mul_pos_of_neg_of_neg ha' (lt_of_le_of_ne (not_lt.1 this) hc)
  · exact mul_pos ha' (h.1 ha')

/-- `q` has the sign pattern of `T`: nonzero coordinates of `q` are nonzero in `T`, with the same
sign. -/
def Sg (T q : Fin n → ℤ) : Prop := ∀ i, q i ≠ 0 → 0 < q i * T i

theorem sg_self (T : Fin n → ℤ) : Sg T T := fun _ hi => mul_self_pos.2 hi

theorem sg_mul_nonneg {T p q : Fin n → ℤ} (hp : Sg T p) (hq : Sg T q) (i : Fin n) :
    0 ≤ p i * q i := by
  by_cases hpi : p i = 0
  · rw [hpi, zero_mul]
  by_cases hqi : q i = 0
  · rw [hqi, mul_zero]
  have h1 := hp i hpi
  have h2 := hq i hqi
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h1 with ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨c, d⟩ | ⟨c, d⟩
  · exact (mul_pos a c).le
  · exact absurd b (not_lt.2 d.le)
  · exact absurd d (not_lt.2 b.le)
  · exact (mul_pos_of_neg_of_neg a c).le

theorem sg_eq_of_abs {T p q : Fin n → ℤ} (hp : Sg T p) (hq : Sg T q) (h : ∀ i, |p i| = |q i|) :
    p = q := eq_of_abs_eq (sg_mul_nonneg hp hq) h

theorem sg_zero {T q : Fin n → ℤ} (hq : Sg T q) {i : Fin n} (hT : T i = 0) : q i = 0 := by
  by_contra hne
  have := hq i hne
  rw [hT, mul_zero] at this
  exact lt_irrefl 0 this

theorem sg_update {T p : Fin n → ℤ} (hp : Sg T p) {j : Fin n} {v : ℤ} (hv : v ≠ 0 → 0 < v * T j) :
    Sg T (Function.update p j v) := by
  intro i hi
  by_cases hij : i = j
  · rw [hij, Function.update_self] at hi ⊢
    exact hv hi
  · rw [Function.update_of_ne hij] at hi ⊢
    exact hp i hi

theorem ptSupp_subset_iff {T q : Fin n → ℤ} : ptSupp q ⊆ ptSupp T ↔ Sg T q := by
  constructor
  · intro hsub i hqi
    have hmem : (i, decide (0 < q i)) ∈ ptSupp q := by
      rw [mem_ptSupp]; exact ⟨hqi, by simp⟩
    have := hsub hmem
    rw [mem_ptSupp] at this
    obtain ⟨hTi, hb⟩ := this
    simp only [decide_eq_true_eq] at hb
    exact mul_pos_of_pos_iff hqi hTi hb
  · intro hs
    rintro ⟨i, b⟩ hp
    rw [mem_ptSupp] at hp ⊢
    obtain ⟨hqi, hb⟩ := hp
    have := hs i hqi
    exact ⟨ne_zero_of_mul_pos_right this, hb.trans (pos_iff_of_mul_pos this)⟩

theorem card_ptSupp (x : Fin n → ℤ) :
    (ptSupp x).card = (Finset.univ.filter (fun i => x i ≠ 0)).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · rintro ⟨i, b⟩ hp
    rw [mem_ptSupp] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp.1
  · rintro ⟨i, b⟩ hp ⟨i', b'⟩ hp' hii
    simp only at hii
    subst hii
    rw [mem_ptSupp] at hp hp'
    have : (b = true) ↔ (b' = true) := hp.2.trans hp'.2.symm
    cases b <;> cases b' <;> simp_all
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨(i, decide (0 < x i)), ?_, rfl⟩
    rw [mem_ptSupp]
    exact ⟨hi, by simp⟩

theorem isSimplex_insert_iff {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) {q : Fin n → ℤ} :
    IsSimplex (insert q σ) ↔ ∀ x ∈ σ, Compat q x := by
  constructor
  · intro hq x hx
    exact hq.2 q (Finset.mem_insert_self q σ) x (Finset.mem_insert_of_mem hx)
  · intro hq
    refine ⟨Finset.insert_nonempty q σ, ?_⟩
    intro x hx y hy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact compat_self _
    · exact hq y hy
    · exact compat_symm (hq x hx)
    · exact h.2 x hx y hy

theorem sgnSupp_insert (q : Fin n → ℤ) (σ : Finset (Fin n → ℤ)) :
    sgnSupp (insert q σ) = ptSupp q ∪ sgnSupp σ := by
  simp only [sgnSupp, Finset.biUnion_insert]

theorem card_ne_eq (y z : Fin n → ℤ) (h1 : ∀ i, |y i| ≤ |z i|) (h2 : ∀ i, |z i| ≤ |y i| + 1) :
    ((Finset.univ.filter (fun i => |y i| ≠ |z i|)).card : ℤ) = wt z - wt y := by
  rw [Finset.natCast_card_filter]
  unfold wt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have := h1 i
  have := h2 i
  split_ifs with hne <;> omega

section frame

variable {σ : Finset (Fin n → ℤ)} {T B : Fin n → ℤ}

theorem sg_of_mem (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    {x : Fin n → ℤ} (hx : x ∈ σ) : Sg T x := by
  intro i hxi
  have h1 := (h.2 x hx T hT).1 i
  have h2 := hTm x hx i
  have hTi : T i ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h2
    exact hxi (abs_nonpos_iff.1 h2)
  rcases lt_or_gt_of_ne hxi with hx' | hx' <;> rcases lt_or_gt_of_ne hTi with hT' | hT'
  · exact mul_pos_of_neg_of_neg hx' hT'
  · exact absurd h1 (not_le.2 (mul_neg_of_neg_of_pos hx' hT'))
  · exact absurd h1 (not_le.2 (mul_neg_of_pos_of_neg hx' hT'))
  · exact mul_pos hx' hT'

theorem sgnSupp_eq_ptSupp (h : IsSimplex σ) (hT : T ∈ σ)
    (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|) : sgnSupp σ = ptSupp T := by
  apply Finset.Subset.antisymm
  · intro p hp
    rw [mem_sgnSupp] at hp
    obtain ⟨x, hx, hp⟩ := hp
    exact ptSupp_subset_iff.2 (sg_of_mem h hT hTm hx) hp
  · intro p hp
    exact mem_sgnSupp.2 ⟨T, hT, hp⟩

theorem compat_of_sg (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    {q x : Fin n → ℤ} (hq : Sg T q) (hx : x ∈ σ)
    (hcmp : (∀ i, |q i| ≤ |x i|) ∨ (∀ i, |x i| ≤ |q i|))
    (hb : ∀ i, |q i| ≤ |x i| + 1 ∧ |x i| ≤ |q i| + 1) : Compat q x :=
  ⟨sg_mul_nonneg hq (sg_of_mem h hT hTm hx), hcmp, hb⟩

theorem tight_mem_iff (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    {q : Fin n → ℤ} :
    (IsSimplex (insert q σ) ∧ sgnSupp (insert q σ) = sgnSupp σ) ↔
      (Sg T q ∧ ∀ x ∈ σ, Compat q x) := by
  rw [isSimplex_insert_iff h, sgnSupp_insert, Finset.union_eq_right,
    sgnSupp_eq_ptSupp h hT hTm, ptSupp_subset_iff]
  exact and_comm

theorem D_subset_S (hBT : ∀ i, |B i| ≤ |T i|) :
    Finset.univ.filter (fun i => |B i| ≠ |T i|) ⊆ Finset.univ.filter (fun i => T i ≠ 0) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro h0
  apply hi
  have := hBT i
  rw [h0, abs_zero] at this ⊢
  exact le_antisymm this (abs_nonneg _)

theorem card_le_wt (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) :
    (σ.card : ℤ) ≤ wt T - wt B + 1 := by
  have hc : σ.card ≤ (Finset.Icc (wt B) (wt T)).card := by
    apply Finset.card_le_card_of_injOn wt
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨wt_le_wt (hBm x hx), wt_le_wt (hTm x hx)⟩
    · intro x hx y hy hxy
      exact eq_of_compat_of_wt_eq (h.2 x hx y hy) hxy
  rw [Int.card_Icc] at hc
  have : wt B ≤ wt T := wt_le_wt (hBm T hT)
  omega

/-- The basic counting facts for a simplex with top `T` and bottom `B`. -/
theorem frame_card (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hB : B ∈ σ) (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) :
    (sgnSupp σ).card = (Finset.univ.filter (fun i => T i ≠ 0)).card ∧
    ((Finset.univ.filter (fun i => |B i| ≠ |T i|)).card : ℤ) = wt T - wt B ∧
    (σ.card : ℤ) ≤ wt T - wt B + 1 ∧
    Finset.univ.filter (fun i => |B i| ≠ |T i|) ⊆ Finset.univ.filter (fun i => T i ≠ 0) := by
  refine ⟨?_, card_ne_eq B T (hBm T hT) (fun i => ((h.2 T hT B hB).2.2 i).1),
    card_le_wt h hT hTm hBm, D_subset_S (hBm T hT)⟩
  rw [sgnSupp_eq_ptSupp h hT hTm, card_ptSupp]

/-- If `|σ| ≥ |sgnSupp σ| + 1`, every used coordinate varies between bottom and top. -/
theorem D_full (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hB : B ∈ σ) (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) (hc : (sgnSupp σ).card + 1 ≤ σ.card) :
    ∀ i, T i ≠ 0 → |B i| ≠ |T i| := by
  obtain ⟨h1, h2, h3, h4⟩ := frame_card h hT hTm hB hBm
  have heq : Finset.univ.filter (fun i => |B i| ≠ |T i|) =
      Finset.univ.filter (fun i => T i ≠ 0) :=
    Finset.eq_of_subset_of_card_le h4 (by omega)
  intro i hi
  have : i ∈ Finset.univ.filter (fun i => |B i| ≠ |T i|) := by
    rw [heq]; simpa using hi
  simpa using this

end frame

end TA

/-- A simplex has at most `|sgnSupp σ| + 1` vertices. -/
theorem card_le_sgnSupp_card_succ {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) :
    σ.card ≤ (sgnSupp σ).card + 1 := by
  obtain ⟨T, hT, hTm⟩ := TA.exists_top h
  obtain ⟨B, hB, hBm⟩ := TA.exists_bot h
  obtain ⟨h1, h2, h3, h4⟩ := TA.frame_card h hT hTm hB hBm
  have h5 := Finset.card_le_card h4
  omega

theorem sgnSupp_eq_empty_iff {σ : Finset (Fin n → ℤ)} : sgnSupp σ = ∅ ↔ ∀ x ∈ σ, x = 0 := by
  constructor
  · intro h x hx
    funext i
    by_contra hne
    have : (i, decide (0 < x i)) ∈ sgnSupp σ :=
      TA.mem_sgnSupp.2 ⟨x, hx, TA.mem_ptSupp.2 ⟨hne, by simp⟩⟩
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨i, b⟩ hp
    rw [TA.mem_sgnSupp] at hp
    obtain ⟨x, hx, hp⟩ := hp
    rw [TA.mem_ptSupp, h x hx] at hp
    exact hp.1 rfl

namespace TA

section frame2

variable {σ : Finset (Fin n → ℤ)} {T B : Fin n → ℤ}

theorem image_wt_subset (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) :
    σ.image wt ⊆ Finset.Icc (wt B) (wt T) := by
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  rw [Finset.mem_Icc]
  exact ⟨wt_le_wt (hBm x hx), wt_le_wt (hTm x hx)⟩

theorem card_image_wt (h : IsSimplex σ) : (σ.image wt).card = σ.card :=
  Finset.card_image_of_injOn fun x hx y hy hxy => eq_of_compat_of_wt_eq (h.2 x hx y hy) hxy

theorem all_levels (h : IsSimplex σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) (hc : (σ.card : ℤ) = wt T - wt B + 1) :
    ∀ v, wt B ≤ v → v ≤ wt T → ∃ x ∈ σ, wt x = v := by
  have heq : σ.image wt = Finset.Icc (wt B) (wt T) := by
    apply Finset.eq_of_subset_of_card_le (image_wt_subset hTm hBm)
    rw [Int.card_Icc, card_image_wt h]
    omega
  intro v hv1 hv2
  have : v ∈ σ.image wt := by rw [heq, Finset.mem_Icc]; exact ⟨hv1, hv2⟩
  rw [Finset.mem_image] at this
  exact this

theorem one_missing_level (h : IsSimplex σ) (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hB : B ∈ σ) (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|) (hc : (σ.card : ℤ) = wt T - wt B) :
    ∃ l, wt B < l ∧ l < wt T ∧ (∀ x ∈ σ, wt x ≠ l) ∧
      ∀ v, wt B ≤ v → v ≤ wt T → v ≠ l → ∃ x ∈ σ, wt x = v := by
  have hsub := image_wt_subset hTm hBm
  have hsd : (Finset.Icc (wt B) (wt T) \ σ.image wt).card = 1 := by
    have := Finset.card_sdiff_add_card_eq_card hsub
    rw [Int.card_Icc, card_image_wt h] at this
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hsd
  have hlmem : l ∈ Finset.Icc (wt B) (wt T) \ σ.image wt := by
    rw [hl]; exact Finset.mem_singleton_self l
  rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image] at hlmem
  obtain ⟨⟨hl1, hl2⟩, hl3⟩ := hlmem
  have hl3' : ∀ x ∈ σ, wt x ≠ l := fun x hx hxl => hl3 ⟨x, hx, hxl⟩
  have hother : ∀ v, wt B ≤ v → v ≤ wt T → v ≠ l → ∃ x ∈ σ, wt x = v := by
    intro v hv1 hv2 hvl
    by_contra hcon
    have : v ∈ Finset.Icc (wt B) (wt T) \ σ.image wt := by
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image]
      exact ⟨⟨hv1, hv2⟩, hcon⟩
    rw [hl, Finset.mem_singleton] at this
    exact hvl this
  exact ⟨l, lt_of_le_of_ne hl1 (fun h' => hl3' B hB h'),
    lt_of_le_of_ne hl2 (fun h' => hl3' T hT h'.symm), hl3', hother⟩

end frame2

theorem sign_facts {t : ℤ} (ht : t ≠ 0) :
    |t + t.sign| = |t| + 1 ∧ 0 < (t + t.sign) * t ∧ |t - t.sign| = |t| - 1 ∧
      (t - t.sign ≠ 0 → 0 < (t - t.sign) * t) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [Int.sign_eq_neg_one_of_neg hneg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg (by linarith)]; ring
    · exact mul_pos_of_neg_of_neg (by linarith) hneg
    · rw [abs_of_neg hneg, abs_of_nonpos (by linarith)]; ring
    · intro hne
      exact mul_pos_of_neg_of_neg (by omega) hneg
  · rw [Int.sign_eq_one_of_pos hpos]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos (by linarith)]
    · exact mul_pos (by linarith) hpos
    · rw [abs_of_pos hpos, abs_of_nonneg (by linarith)]
    · intro hne
      exact mul_pos (by omega) hpos

/-- Tight case where some used coordinate `i₀` is constant on `σ`. -/
theorem tight_case_two {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} {T B : Fin n → ℤ}
    (h : IsSimplex σ) (hg : σ ⊆ grid n m)
    (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hB : B ∈ σ) (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|)
    {i₀ : Fin n} (hi₀ : T i₀ ≠ 0) (hBi₀ : |B i₀| = |T i₀|)
    (huniq : ∀ i, T i ≠ 0 → i ≠ i₀ → |B i| ≠ |T i|)
    (hlev : ∀ v, wt B ≤ v → v ≤ wt T → ∃ x ∈ σ, wt x = v) :
    ∃ q₁ q₂ : Fin n → ℤ, q₁ ≠ q₂ ∧ ∀ q, (q ∈ grid n m ∧ q ∉ σ ∧ IsSimplex (insert q σ) ∧
      sgnSupp (insert q σ) = sgnSupp σ) ↔ (q = q₁ ∨ (q = q₂ ∧ ¬ IsBdry m σ)) := by
  have hTB : ∀ i, |T i| ≤ |B i| + 1 := fun i => ((h.2 T hT B hB).2.2 i).1
  have hBT : ∀ i, |B i| ≤ |T i| := hBm T hT
  have hTB' : ∀ i, T i ≠ 0 → i ≠ i₀ → |T i| = |B i| + 1 := fun i h1 h2 => by
    have := huniq i h1 h2; have := hTB i; have := hBT i; omega
  have hsgB : Sg T B := sg_of_mem h hT hTm hB
  have hsgT : Sg T T := sg_self T
  have hTg : ∀ i, |T i| ≤ (m : ℤ) := mem_grid.1 (hg hT)
  have hBg : ∀ i, |B i| ≤ (m : ℤ) := mem_grid.1 (hg hB)
  obtain ⟨e1, e2, e3, e4⟩ := sign_facts hi₀
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : Fin n → ℤ, q₁ = Function.update B i₀ (T i₀ - (T i₀).sign) :=
    ⟨_, rfl⟩
  obtain ⟨q₂, hq₂⟩ : ∃ q₂ : Fin n → ℤ, q₂ = Function.update T i₀ (T i₀ + (T i₀).sign) :=
    ⟨_, rfl⟩
  have a₁ : |q₁ i₀| = |T i₀| - 1 := by rw [hq₁, Function.update_self]; exact e3
  have a₁' : ∀ i, i ≠ i₀ → |q₁ i| = |B i| := fun i hi => by
    rw [hq₁, Function.update_of_ne hi]
  have a₂ : |q₂ i₀| = |T i₀| + 1 := by rw [hq₂, Function.update_self]; exact e1
  have a₂' : ∀ i, i ≠ i₀ → |q₂ i| = |T i| := fun i hi => by
    rw [hq₂, Function.update_of_ne hi]
  have hsg₁ : Sg T q₁ := by rw [hq₁]; exact sg_update hsgB e4
  have hsg₂ : Sg T q₂ := by rw [hq₂]; exact sg_update hsgT (fun _ => e2)
  have hbdry : IsBdry m σ ↔ |T i₀| = m := by
    constructor
    · rintro ⟨i, hi⟩
      have h1 := hi T hT
      have h2 := hi B hB
      have hTi : T i ≠ 0 := by
        intro h0; rw [h0, abs_zero] at h1; omega
      by_cases hii : i = i₀
      · rw [← hii]; exact h1
      · exact absurd (h2.trans h1.symm) (huniq i hTi hii)
    · intro hc
      refine ⟨i₀, fun x hx => le_antisymm ((hTm x hx i₀).trans hc.le) ?_⟩
      rw [← hc, ← hBi₀]; exact hBm x hx i₀
  have hT0 : 1 ≤ |T i₀| := by
    have := abs_pos.2 hi₀; omega
  refine ⟨q₁, q₂, ?_, fun q => ⟨?_, ?_⟩⟩
  · intro heq
    have := a₁
    rw [heq, a₂] at this
    omega
  · -- any coface is `q₁` or `q₂`
    rintro ⟨hqg, hqσ, hsimp, hss⟩
    obtain ⟨hsg, hcomp⟩ := (tight_mem_iff h hT hTm).1 ⟨hsimp, hss⟩
    have hqT := hcomp T hT
    have hqB := hcomp B hB
    rcases hqT.2.1 with hle | hge
    · rcases hqB.2.1 with hle' | hge'
      · -- below the bottom
        left
        by_cases hq0 : |q i₀| = |B i₀|
        · exfalso
          apply hqσ
          have : q = B := by
            apply sg_eq_of_abs hsg hsgB
            intro i
            by_cases hi : i = i₀
            · rw [hi]; exact hq0
            by_cases hTi : T i = 0
            · rw [sg_zero hsg hTi, sg_zero hsgB hTi]
            · have h1 := hTB' i hTi hi
              have h2 := (hqT.2.2 i).2
              have h3 := hle' i
              omega
          rw [this]; exact hB
        · apply sg_eq_of_abs hsg hsg₁
          intro i
          by_cases hi : i = i₀
          · rw [hi, a₁]
            have h2 := (hqT.2.2 i₀).2
            have h3 := hle' i₀
            omega
          · rw [a₁' i hi]
            by_cases hTi : T i = 0
            · rw [sg_zero hsg hTi, sg_zero hsgB hTi]
            · have h1 := hTB' i hTi hi
              have h2 := (hqT.2.2 i).2
              have h3 := hle' i
              omega
      · -- between bottom and top: impossible
        exfalso
        obtain ⟨x, hx, hwx⟩ := hlev (wt q) (wt_le_wt hge') (wt_le_wt hle)
        apply hqσ
        rw [eq_of_compat_of_wt_eq (hcomp x hx) hwx.symm]
        exact hx
    · -- above the top
      right
      have hq2 : q = q₂ := by
        by_cases hq0 : |q i₀| = |T i₀|
        · exfalso
          apply hqσ
          have : q = T := by
            apply sg_eq_of_abs hsg hsgT
            intro i
            by_cases hi : i = i₀
            · rw [hi]; exact hq0
            by_cases hTi : T i = 0
            · rw [sg_zero hsg hTi, hTi]
            · have h1 := hTB' i hTi hi
              have h2 := (hqB.2.2 i).1
              have h3 := hge i
              omega
          rw [this]; exact hT
        · apply sg_eq_of_abs hsg hsg₂
          intro i
          by_cases hi : i = i₀
          · rw [hi, a₂]
            have h2 := (hqB.2.2 i₀).1
            have h3 := hge i₀
            omega
          · rw [a₂' i hi]
            by_cases hTi : T i = 0
            · rw [sg_zero hsg hTi, hTi]
            · have h1 := hTB' i hTi hi
              have h2 := (hqB.2.2 i).1
              have h3 := hge i
              omega
      refine ⟨hq2, ?_⟩
      rw [hbdry]
      intro hc
      have := mem_grid.1 hqg i₀
      rw [hq2, a₂] at this
      omega
  · -- `q₁` and (off the boundary) `q₂` are cofaces
    rintro (rfl | ⟨rfl, hnb⟩)
    · refine ⟨?_, ?_, (tight_mem_iff h hT hTm).2 ⟨hsg₁, fun x hx => ?_⟩⟩
      · rw [mem_grid]
        intro i
        by_cases hi : i = i₀
        · rw [hi, a₁]; have := hTg i₀; omega
        · rw [a₁' i hi]; exact hBg i
      · intro hq
        have := hBm _ hq i₀
        rw [a₁] at this
        omega
      · refine compat_of_sg h hT hTm hsg₁ hx (Or.inl fun i => ?_) fun i => ?_
        · by_cases hi : i = i₀
          · rw [hi, a₁]; have := hBm x hx i₀; omega
          · rw [a₁' i hi]; exact hBm x hx i
        · by_cases hi : i = i₀
          · rw [hi, a₁]
            have := hBm x hx i₀; have := hTm x hx i₀
            exact ⟨by omega, by omega⟩
          · rw [a₁' i hi]
            have := hBm x hx i; have := hTm x hx i; have := hTB i
            exact ⟨by omega, by omega⟩
    · have hlt : |T i₀| < m := by
        rw [hbdry] at hnb; have := hTg i₀; omega
      refine ⟨?_, ?_, (tight_mem_iff h hT hTm).2 ⟨hsg₂, fun x hx => ?_⟩⟩
      · rw [mem_grid]
        intro i
        by_cases hi : i = i₀
        · rw [hi, a₂]; omega
        · rw [a₂' i hi]; exact hTg i
      · intro hq
        have := hTm _ hq i₀
        rw [a₂] at this
        omega
      · refine compat_of_sg h hT hTm hsg₂ hx (Or.inr fun i => ?_) fun i => ?_
        · by_cases hi : i = i₀
          · rw [hi, a₂]; have := hTm x hx i₀; omega
          · rw [a₂' i hi]; exact hTm x hx i
        · by_cases hi : i = i₀
          · rw [hi, a₂]
            have := hBm x hx i₀; have := hTm x hx i₀
            exact ⟨by omega, by omega⟩
          · rw [a₂' i hi]
            have := hBm x hx i; have := hTm x hx i; have := hTB i
            exact ⟨by omega, by omega⟩

end TA

namespace TA

/-- Tight case where every used coordinate varies on `σ`: exactly one level is missing. -/
theorem tight_case_one {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} {T B : Fin n → ℤ}
    (h : IsSimplex σ) (hg : σ ⊆ grid n m)
    (hT : T ∈ σ) (hTm : ∀ x ∈ σ, ∀ i, |x i| ≤ |T i|)
    (hB : B ∈ σ) (hBm : ∀ x ∈ σ, ∀ i, |B i| ≤ |x i|)
    (hD : ∀ i, T i ≠ 0 → |B i| ≠ |T i|)
    {l : ℤ} (hl1 : wt B < l) (hl2 : l < wt T) (hl3 : ∀ x ∈ σ, wt x ≠ l)
    (hl4 : ∀ v, wt B ≤ v → v ≤ wt T → v ≠ l → ∃ x ∈ σ, wt x = v) :
    ¬ IsBdry m σ ∧ ∃ q₁ q₂ : Fin n → ℤ, q₁ ≠ q₂ ∧ ∀ q, (q ∈ grid n m ∧ q ∉ σ ∧
      IsSimplex (insert q σ) ∧ sgnSupp (insert q σ) = sgnSupp σ) ↔ (q = q₁ ∨ q = q₂) := by
  have hTB : ∀ i, |T i| ≤ |B i| + 1 := fun i => ((h.2 T hT B hB).2.2 i).1
  have hBT : ∀ i, |B i| ≤ |T i| := hBm T hT
  have hTB' : ∀ i, T i ≠ 0 → |T i| = |B i| + 1 := fun i h1 => by
    have := hD i h1; have := hTB i; have := hBT i; omega
  have hsgB : Sg T B := sg_of_mem h hT hTm hB
  have hsgT : Sg T T := sg_self T
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    have h1 := hi T hT
    have h2 := hi B hB
    have hTi : T i ≠ 0 := by
      intro h0; rw [h0, abs_zero] at h1; omega
    exact hD i hTi (h2.trans h1.symm)
  obtain ⟨xm, hxm, hwxm⟩ := hl4 (l - 1) (by omega) (by omega) (by omega)
  obtain ⟨xp, hxp, hwxp⟩ := hl4 (l + 1) (by omega) (by omega) (by omega)
  have hmp : ∀ i, |xm i| ≤ |xp i| := abs_le_of_wt_le (h.2 xm hxm xp hxp) (by omega)
  have hpm : ∀ i, |xp i| ≤ |xm i| + 1 := fun i => ((h.2 xp hxp xm hxm).2.2 i).1
  have hsgm : Sg T xm := sg_of_mem h hT hTm hxm
  have hsgp : Sg T xp := sg_of_mem h hT hTm hxp
  have hpg : ∀ i, |xp i| ≤ (m : ℤ) := mem_grid.1 (hg hxp)
  have hA := card_ne_eq xm xp hmp hpm
  have hA2 : (Finset.univ.filter (fun i => |xm i| ≠ |xp i|)).card = 2 := by omega
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.1 hA2
  have hmemA : ∀ c, c ∈ Finset.univ.filter (fun i => |xm i| ≠ |xp i|) ↔ |xm c| ≠ |xp c| := by
    intro c; simp
  have ha : |xm a| ≠ |xp a| := (hmemA a).1 (by rw [hAeq]; simp)
  have hb : |xm b| ≠ |xp b| := (hmemA b).1 (by rw [hAeq]; simp)
  -- the candidate cofaces
  have hcof : ∀ c, |xm c| ≠ |xp c| →
      (Function.update xm c (xp c) ∈ grid n m ∧ Function.update xm c (xp c) ∉ σ ∧
        IsSimplex (insert (Function.update xm c (xp c)) σ) ∧
        sgnSupp (insert (Function.update xm c (xp c)) σ) = sgnSupp σ) := by
    intro c hc
    obtain ⟨q, hq⟩ : ∃ q, q = Function.update xm c (xp c) := ⟨_, rfl⟩
    rw [← hq]
    have ac : |q c| = |xp c| := by rw [hq, Function.update_self]
    have ac' : ∀ i, i ≠ c → |q i| = |xm i| := fun i hi => by
      rw [hq, Function.update_of_ne hi]
    have hsgq : Sg T q := by rw [hq]; exact sg_update hsgm (hsgp c)
    have hge : ∀ i, |xm i| ≤ |q i| := fun i => by
      by_cases hi : i = c
      · rw [hi, ac]; exact hmp c
      · rw [ac' i hi]
    have hle : ∀ i, |q i| ≤ |xp i| := fun i => by
      by_cases hi : i = c
      · rw [hi, ac]
      · rw [ac' i hi]; exact hmp i
    have hwq : wt q = l := by
      have h1 := card_ne_eq xm q hge (fun i => (hle i).trans (hpm i))
      have h2 : Finset.univ.filter (fun i => |xm i| ≠ |q i|) = {c} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hne
          by_contra hic
          exact hne (ac' i hic).symm
        · rintro rfl
          rw [ac]; exact hc
      rw [h2, Finset.card_singleton] at h1
      omega
    refine ⟨?_, ?_, (tight_mem_iff h hT hTm).2 ⟨hsgq, fun x hx => ?_⟩⟩
    · rw [mem_grid]; exact fun i => (hle i).trans (hpg i)
    · intro hqσ; exact hl3 q hqσ hwq
    · refine compat_of_sg h hT hTm hsgq hx ?_ fun i => ?_
      · rcases lt_or_gt_of_ne (hl3 x hx) with hlt | hgt
        · right
          intro i
          exact (abs_le_of_wt_le (h.2 x hx xm hxm) (by omega) i).trans (hge i)
        · left
          intro i
          exact (hle i).trans (abs_le_of_wt_le (h.2 xp hxp x hx) (by omega) i)
      · have h1 := hTm x hx i
        have h2 := hBm x hx i
        have h3 := hTB i
        have h4 := hBm xm hxm i
        have h5 := hTm xp hxp i
        have h6 := hge i
        have h7 := hle i
        exact ⟨by omega, by omega⟩
  -- uniqueness
  have huniq : ∀ q, (q ∈ grid n m ∧ q ∉ σ ∧ IsSimplex (insert q σ) ∧
      sgnSupp (insert q σ) = sgnSupp σ) →
      ∃ c, |xm c| ≠ |xp c| ∧ q = Function.update xm c (xp c) := by
    rintro q ⟨_, hqσ, hsimp, hss⟩
    obtain ⟨hsg, hcomp⟩ := (tight_mem_iff h hT hTm).1 ⟨hsimp, hss⟩
    have hqT := hcomp T hT
    have hqB := hcomp B hB
    rcases hqT.2.1 with hle | hge
    · rcases hqB.2.1 with hle' | hge'
      · exfalso
        apply hqσ
        have : q = B := by
          apply sg_eq_of_abs hsg hsgB
          intro i
          by_cases hTi : T i = 0
          · rw [sg_zero hsg hTi, sg_zero hsgB hTi]
          · have h1 := hTB' i hTi
            have h2 := (hqT.2.2 i).2
            have h3 := hle' i
            omega
        rw [this]; exact hB
      · -- between bottom and top
        have hwq : wt q = l := by
          by_contra hne
          obtain ⟨x, hx, hwx⟩ := hl4 (wt q) (wt_le_wt hge') (wt_le_wt hle) hne
          apply hqσ
          rw [eq_of_compat_of_wt_eq (hcomp x hx) hwx.symm]
          exact hx
        have hge2 : ∀ i, |xm i| ≤ |q i| :=
          abs_le_of_wt_le (compat_symm (hcomp xm hxm)) (by omega)
        have hle2 : ∀ i, |q i| ≤ |xp i| := abs_le_of_wt_le (hcomp xp hxp) (by omega)
        have h1 := card_ne_eq xm q hge2 (fun i => (hle2 i).trans (hpm i))
        have h2 : (Finset.univ.filter (fun i => |xm i| ≠ |q i|)).card = 1 := by omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h2
        have hc1 : |xm c| ≠ |q c| := by
          have : c ∈ Finset.univ.filter (fun i => |xm i| ≠ |q i|) := by
            rw [hc]; exact Finset.mem_singleton_self c
          simpa using this
        have hc2 : ∀ i, i ≠ c → |xm i| = |q i| := by
          intro i hi
          by_contra hne
          have : i ∈ Finset.univ.filter (fun i => |xm i| ≠ |q i|) := by simpa using hne
          rw [hc, Finset.mem_singleton] at this
          exact hi this
        refine ⟨c, ?_, ?_⟩
        · have := hge2 c; have := hle2 c; omega
        · apply sg_eq_of_abs hsg (sg_update hsgm (hsgp c))
          intro i
          by_cases hi : i = c
          · rw [hi, Function.update_self]
            have := hge2 c; have := hle2 c; have := hpm c; omega
          · rw [Function.update_of_ne hi]
            exact (hc2 i hi).symm
    · exfalso
      apply hqσ
      have : q = T := by
        apply sg_eq_of_abs hsg hsgT
        intro i
        by_cases hTi : T i = 0
        · rw [sg_zero hsg hTi, hTi]
        · have h1 := hTB' i hTi
          have h2 := (hqB.2.2 i).1
          have h3 := hge i
          omega
      rw [this]; exact hT
  refine ⟨Function.update xm a (xp a), Function.update xm b (xp b), ?_, fun q => ⟨?_, ?_⟩⟩
  · intro heq
    have := congrFun heq a
    rw [Function.update_self, Function.update_of_ne hab] at this
    exact ha (by rw [this])
  · intro hq
    obtain ⟨c, hc, rfl⟩ := huniq q hq
    have : c ∈ Finset.univ.filter (fun i => |xm i| ≠ |xp i|) := (hmemA c).2 hc
    rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact hcof a ha
    · exact hcof b hb

end TA

open Classical in
/-- Tight simplices (`|σ| = |sgnSupp σ|`) have two cofaces with the same signed support, or one
if they lie in the boundary of the cube. -/
theorem tight_cofaces_card {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ)
    (hg : σ ⊆ grid n m) (ht : σ.card = (sgnSupp σ).card) :
    ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) = sgnSupp σ)).card = if IsBdry m σ then 1 else 2 := by
  classical
  obtain ⟨T, hT, hTm⟩ := TA.exists_top h
  obtain ⟨B, hB, hBm⟩ := TA.exists_bot h
  obtain ⟨h1, h2, h3, h4⟩ := TA.frame_card h hT hTm hB hBm
  by_cases hcase : ∀ i, T i ≠ 0 → |B i| ≠ |T i|
  · have hSD : Finset.univ.filter (fun i => T i ≠ 0) ⊆
        Finset.univ.filter (fun i => |B i| ≠ |T i|) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hcase i hi
    have h5 := Finset.card_le_card hSD
    have hc : (σ.card : ℤ) = TA.wt T - TA.wt B := by
      have := Finset.card_le_card h4
      omega
    obtain ⟨l, hl1, hl2, hl3, hl4⟩ := TA.one_missing_level h hT hTm hB hBm hc
    obtain ⟨hnb, q₁, q₂, hne, hiff⟩ :=
      TA.tight_case_one hm h hg hT hTm hB hBm hcase hl1 hl2 hl3 hl4
    have hif : (if IsBdry m σ then 1 else 2) = 2 := by simp [hnb]
    rw [hif, Finset.card_eq_two]
    refine ⟨q₁, q₂, hne, ?_⟩
    ext q
    rw [Finset.mem_filter, hiff, Finset.mem_insert, Finset.mem_singleton]
  · obtain ⟨i₀, hi₀, hBi₀⟩ : ∃ i₀, T i₀ ≠ 0 ∧ |B i₀| = |T i₀| := by
      by_contra hcon
      apply hcase
      intro i hi hBi
      exact hcon ⟨i, hi, hBi⟩
    have hDsub : Finset.univ.filter (fun i => |B i| ≠ |T i|) ⊆
        (Finset.univ.filter (fun i => T i ≠ 0)).erase i₀ := by
      intro i hi
      rw [Finset.mem_erase]
      refine ⟨?_, h4 hi⟩
      rintro rfl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi hBi₀
    have hi₀S : i₀ ∈ Finset.univ.filter (fun i => T i ≠ 0) := by simpa using hi₀
    have hcard_erase := Finset.card_erase_of_mem hi₀S
    have hS1 : 1 ≤ (Finset.univ.filter (fun i => T i ≠ 0)).card :=
      Finset.card_pos.2 ⟨i₀, hi₀S⟩
    have hDeq := Finset.eq_of_subset_of_card_le hDsub (by omega)
    have huniq : ∀ i, T i ≠ 0 → i ≠ i₀ → |B i| ≠ |T i| := by
      intro i hTi hii
      have : i ∈ (Finset.univ.filter (fun i => T i ≠ 0)).erase i₀ := by
        rw [Finset.mem_erase]; exact ⟨hii, by simpa using hTi⟩
      rw [← hDeq] at this
      simpa using this
    have hc : (σ.card : ℤ) = TA.wt T - TA.wt B + 1 := by
      have := congrArg Finset.card hDeq
      omega
    have hlev := TA.all_levels h hTm hBm hc
    obtain ⟨q₁, q₂, hne, hiff⟩ :=
      TA.tight_case_two hm h hg hT hTm hB hBm hi₀ hBi₀ huniq hlev
    split_ifs with hb
    · rw [Finset.card_eq_one]
      refine ⟨q₁, ?_⟩
      ext q
      rw [Finset.mem_filter, hiff, Finset.mem_singleton]
      simp [hb]
    · rw [Finset.card_eq_two]
      refine ⟨q₁, q₂, hne, ?_⟩
      ext q
      rw [Finset.mem_filter, hiff, Finset.mem_insert, Finset.mem_singleton]
      simp [hb]

open Classical in
/-- Loose simplices (`|σ| = |sgnSupp σ| + 1`) have exactly one coface adding a new signed
coordinate `(j, b)` whose index `j` is unused. -/
theorem loose_cofaces_card {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ)
    (hg : σ ⊆ grid n m) (hl : σ.card = (sgnSupp σ).card + 1) (j : Fin n) (b : Bool)
    (hj1 : (j, true) ∉ sgnSupp σ) (hj2 : (j, false) ∉ sgnSupp σ) :
    ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) = insert (j, b) (sgnSupp σ))).card = 1 := by
  classical
  obtain ⟨T, hT, hTm⟩ := TA.exists_top h
  obtain ⟨B, hB, hBm⟩ := TA.exists_bot h
  have hD := TA.D_full h hT hTm hB hBm hl.ge
  have hTB : ∀ i, |T i| ≤ |B i| + 1 := fun i => ((h.2 T hT B hB).2.2 i).1
  have hBT : ∀ i, |B i| ≤ |T i| := hBm T hT
  have hTB' : ∀ i, T i ≠ 0 → |T i| = |B i| + 1 := fun i h1 => by
    have := hD i h1; have := hTB i; have := hBT i; omega
  have hss := TA.sgnSupp_eq_ptSupp h hT hTm
  have hTj : T j = 0 := by
    by_contra hne
    by_cases hp : 0 < T j
    · apply hj1; rw [hss, TA.mem_ptSupp]; exact ⟨hne, by simp [hp]⟩
    · apply hj2; rw [hss, TA.mem_ptSupp]; exact ⟨hne, by simp [hp]⟩
  have hxj : ∀ x ∈ σ, x j = 0 := fun x hx => by
    have := hTm x hx j
    rw [hTj, abs_zero] at this
    exact abs_nonpos_iff.1 this
  have hBj : B j = 0 := hxj B hB
  have hTg : ∀ i, |T i| ≤ (m : ℤ) := mem_grid.1 (hg hT)
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Fin n → ℤ, q₀ = Function.update T j (if b then 1 else -1) :=
    ⟨_, rfl⟩
  have a₀ : q₀ j = if b then 1 else -1 := by rw [hq₀, Function.update_self]
  have a₀' : ∀ i, i ≠ j → q₀ i = T i := fun i hi => by rw [hq₀, Function.update_of_ne hi]
  have habs₀ : |q₀ j| = 1 := by rw [a₀]; cases b <;> simp
  rw [Finset.card_eq_one]
  refine ⟨q₀, ?_⟩
  ext q
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, _, hsimp, hsupp⟩
    have hcomp := (TA.isSimplex_insert_iff h).1 hsimp
    rw [TA.sgnSupp_insert, hss] at hsupp
    have hjb : (j, b) ∈ ptSupp q := by
      have : (j, b) ∈ ptSupp q ∪ ptSupp T := by
        rw [hsupp]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_union.1 this with h' | h'
      · exact h'
      · exfalso; rw [TA.mem_ptSupp, hTj] at h'; exact h'.1 rfl
    rw [TA.mem_ptSupp] at hjb
    have hother : ∀ i, i ≠ j → q i ≠ 0 → 0 < q i * T i := by
      intro i hij hqi
      have hmem : (i, decide (0 < q i)) ∈ ptSupp q ∪ ptSupp T :=
        Finset.mem_union_left _ (TA.mem_ptSupp.2 ⟨hqi, by simp⟩)
      rw [hsupp, Finset.mem_insert] at hmem
      rcases hmem with h' | h'
      · exact absurd (congrArg Prod.fst h') hij
      · rw [TA.mem_ptSupp] at h'
        obtain ⟨hTi, hb'⟩ := h'
        simp only [decide_eq_true_eq] at hb'
        exact TA.mul_pos_of_pos_iff hqi hTi hb'
    have hqT := hcomp T hT
    have hqB := hcomp B hB
    have hge : ∀ i, |T i| ≤ |q i| := by
      rcases hqT.2.1 with hle | hge
      · exfalso
        have := hle j
        rw [hTj, abs_zero] at this
        exact hjb.1 (abs_nonpos_iff.1 this)
      · exact hge
    funext i
    by_cases hij : i = j
    · rw [hij, a₀]
      have h1 := (hqB.2.2 j).1
      rw [hBj, abs_zero] at h1
      have h2 : |q j| = 1 := by
        have := abs_pos.2 hjb.1; omega
      cases b
      · have : ¬ 0 < q j := fun hp => absurd (hjb.2.2 hp) (by simp)
        simp
        rcases abs_cases (q j) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
      · have : 0 < q j := hjb.2.1 rfl
        simp
        rcases abs_cases (q j) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    · rw [a₀' i hij]
      by_cases hTi : T i = 0
      · rw [hTi]
        by_contra hqi
        have := hother i hij hqi
        rw [hTi, mul_zero] at this
        exact lt_irrefl 0 this
      · have h1 := hTB' i hTi
        have h2 := (hqB.2.2 i).1
        have h3 := hge i
        exact TA.eq_of_abs_eq_of_mul_nonneg (hqT.1 i) (by omega)
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_grid]
      intro i
      by_cases hij : i = j
      · rw [hij, habs₀]; exact_mod_cast hm
      · rw [a₀' i hij]; exact hTg i
    · intro hq
      have := hxj _ hq
      rw [a₀] at this
      cases b <;> simp at this
    · rw [TA.isSimplex_insert_iff h]
      intro x hx
      refine ⟨fun i => ?_, Or.inr fun i => ?_, fun i => ?_⟩
      · by_cases hij : i = j
        · simp [hij, hxj x hx]
        · rw [a₀' i hij]; exact (h.2 T hT x hx).1 i
      · by_cases hij : i = j
        · rw [hij, hxj x hx, abs_zero]; exact abs_nonneg _
        · rw [a₀' i hij]; exact hTm x hx i
      · by_cases hij : i = j
        · rw [hij, hxj x hx, abs_zero, habs₀]; norm_num
        · rw [a₀' i hij]
          have := hTm x hx i; have := hBm x hx i; have := hTB i
          exact ⟨by omega, by omega⟩
    · rw [TA.sgnSupp_insert, hss]
      ext ⟨i, c⟩
      rw [Finset.mem_union, Finset.mem_insert, TA.mem_ptSupp, TA.mem_ptSupp]
      by_cases hij : i = j
      · rw [hij, a₀, hTj]
        cases b <;> cases c <;> simp
      · rw [a₀' i hij]
        have : (i, c) ≠ (j, b) := fun h' => hij (congrArg Prod.fst h')
        simp only [this, false_or, or_self]

theorem not_isBdry_of_loose {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ)
    (hl : σ.card = (sgnSupp σ).card + 1) : ¬ IsBdry m σ := by
  obtain ⟨T, hT, hTm⟩ := TA.exists_top h
  obtain ⟨B, hB, hBm⟩ := TA.exists_bot h
  have hD := TA.D_full h hT hTm hB hBm hl.ge
  rintro ⟨i, hi⟩
  have h1 := hi T hT
  have h2 := hi B hB
  have hTi : T i ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h1
    omega
  exact hD i hTi (h2.trans h1.symm)

theorem isSimplex_neg {σ : Finset (Fin n → ℤ)} (h : IsSimplex σ) :
    IsSimplex (σ.image (fun x => -x)) := by
  refine ⟨h.1.image _, ?_⟩
  intro x hx y hy
  rw [Finset.mem_image] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨h1, h2, h3⟩ := h.2 x hx y hy
  refine ⟨fun i => ?_, ?_, fun i => ?_⟩
  · simp only [Pi.neg_apply, neg_mul_neg]; exact h1 i
  · simp only [Pi.neg_apply, abs_neg]; exact h2
  · simp only [Pi.neg_apply, abs_neg]; exact h3 i

theorem TA.mem_image_flipL {s : Finset (Fin n × Bool)} {p : Fin n × Bool} :
    p ∈ s.image flipL ↔ flipL p ∈ s := by
  constructor
  · rintro hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simpa [flipL] using hq
  · intro hp
    rw [Finset.mem_image]
    exact ⟨flipL p, hp, by simp [flipL]⟩

theorem sgnSupp_neg (σ : Finset (Fin n → ℤ)) :
    sgnSupp (σ.image (fun x => -x)) = (sgnSupp σ).image flipL := by
  ext ⟨i, b⟩
  rw [TA.mem_sgnSupp, TA.mem_image_flipL, TA.mem_sgnSupp]
  simp only [flipL, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hp⟩
    refine ⟨x, hx, ?_⟩
    rw [TA.mem_ptSupp] at hp ⊢
    simp only [Pi.neg_apply] at hp
    obtain ⟨h1, h2⟩ := hp
    refine ⟨fun h0 => h1 (by rw [h0, neg_zero]), ?_⟩
    cases b <;> simp at h2 ⊢ <;> omega
  · rintro ⟨x, hx, hp⟩
    refine ⟨-x, ⟨x, hx, rfl⟩, ?_⟩
    rw [TA.mem_ptSupp] at hp ⊢
    simp only [Pi.neg_apply]
    obtain ⟨h1, h2⟩ := hp
    refine ⟨fun h0 => h1 (by linarith), ?_⟩
    cases b <;> simp at h2 ⊢ <;> omega

theorem isBdry_neg {m : ℕ} {σ : Finset (Fin n → ℤ)} (h : IsBdry m σ) :
    IsBdry m (σ.image (fun x => -x)) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun y hy => ?_⟩
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simp only [Pi.neg_apply, abs_neg]
  exact hi x hx

theorem neg_subset_grid {m : ℕ} {σ : Finset (Fin n → ℤ)} (h : σ ⊆ grid n m) :
    σ.image (fun x => -x) ⊆ grid n m := by
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_grid]
  intro i
  simp only [Pi.neg_apply, abs_neg]
  exact (mem_grid.1 (h hx)) i

theorem neg_ne_self_of_isBdry {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} (hs : IsSimplex σ)
    (h : IsBdry m σ) : σ.image (fun x => -x) ≠ σ := by
  intro heq
  obtain ⟨i, hi⟩ := h
  obtain ⟨x, hx⟩ := hs.1
  have hnx : -x ∈ σ := by
    rw [← heq]; exact Finset.mem_image_of_mem _ hx
  have h1 := (hs.2 x hx (-x) hnx).1 i
  simp only [Pi.neg_apply] at h1
  have h2 := hi x hx
  have h3 : x i * x i = 0 := le_antisymm (by linarith [h1]) (mul_self_nonneg _)
  rw [mul_self_eq_zero.1 h3, abs_zero] at h2
  omega


/-! ## Assembly (part B) -/

/-! Helpers for the Freund–Todd parity argument: the graph whose vertices are the happy
simplices of the grid; `{0}` has degree `1` and every other vertex has degree `2` unless two
grid points at sup-distance `≤ 1` carry opposite labels. -/

namespace FT

open Classical in
/-- The happy simplices of the grid: `sgnSupp σ ⊆ lab '' σ`. -/
noncomputable def happySet (n m : ℕ) (lab : (Fin n → ℤ) → Fin n × Bool) :
    Finset (Finset (Fin n → ℤ)) :=
  (grid n m).powerset.filter (fun σ => IsSimplex σ ∧ sgnSupp σ ⊆ σ.image lab)

open Classical in
theorem mem_happySet {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool} {σ : Finset (Fin n → ℤ)} :
    σ ∈ happySet n m lab ↔ σ ⊆ grid n m ∧ IsSimplex σ ∧ sgnSupp σ ⊆ σ.image lab := by
  unfold happySet
  rw [Finset.mem_filter, Finset.mem_powerset]

theorem sgnSupp_zero : sgnSupp ({0} : Finset (Fin n → ℤ)) = ∅ :=
  sgnSupp_eq_empty_iff.2 (fun _ hx => Finset.mem_singleton.1 hx)

theorem zero_mem_happySet {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool} :
    ({0} : Finset (Fin n → ℤ)) ∈ happySet n m lab := by
  refine mem_happySet.2 ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [mem_grid]
    intro i
    simp
  · refine ⟨Finset.singleton_nonempty 0, ?_⟩
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    exact ⟨fun i => by simp, Or.inl (fun i => le_refl _), fun i => ⟨by simp, by simp⟩⟩
  · rw [sgnSupp_zero]
    exact Finset.empty_subset _

/-- Adjacency of the Freund–Todd graph on happy simplices. -/
def ftAdj (m : ℕ) (lab : (Fin n → ℤ) → Fin n × Bool) (σ τ : Finset (Fin n → ℤ)) : Prop :=
  σ ≠ τ ∧ ((σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ sgnSupp τ ⊆ σ.image lab) ∨
    (τ ⊆ σ ∧ σ.card = τ.card + 1 ∧ sgnSupp σ ⊆ τ.image lab) ∨
    (IsBdry m σ ∧ τ = σ.image (fun x => -x)))

theorem ftAdj_symm {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool} {σ τ : Finset (Fin n → ℤ)}
    (h : ftAdj m lab σ τ) : ftAdj m lab τ σ := by
  obtain ⟨hne, h1 | h2 | h3⟩ := h
  · exact ⟨Ne.symm hne, Or.inr (Or.inl h1)⟩
  · exact ⟨Ne.symm hne, Or.inl h2⟩
  · obtain ⟨hb, rfl⟩ := h3
    refine ⟨Ne.symm hne, Or.inr (Or.inr ⟨isBdry_neg hb, ?_⟩)⟩
    rw [Finset.image_image]
    simp

/-- The Freund–Todd graph on happy simplices. -/
def ftGraph (m : ℕ) (lab : (Fin n → ℤ) → Fin n × Bool) :
    SimpleGraph {σ // σ ∈ happySet n m lab} where
  Adj a b := ftAdj m lab a.1 b.1
  symm := ⟨fun _ _ h => ftAdj_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- The neighbours of `σ` in the Freund–Todd graph, as a finset of finsets. -/
noncomputable def nbrs (m : ℕ) (lab : (Fin n → ℤ) → Fin n × Bool) (σ : Finset (Fin n → ℤ)) :
    Finset (Finset (Fin n → ℤ)) :=
  (happySet n m lab).filter (ftAdj m lab σ)

open Classical in
theorem ftGraph_degree {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    (v : {σ // σ ∈ happySet n m lab}) :
    (ftGraph m lab).degree v = (nbrs m lab v.1).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    unfold nbrs
    rw [Finset.mem_filter]
    exact ⟨a.2, ha.2⟩
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    unfold nbrs at hb
    rw [Finset.mem_filter] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hb.2⟩

open Classical in
theorem nbrs_card_eq {m : ℕ} (hm : 1 ≤ m) {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) :
    (nbrs m lab σ).card =
      ((happySet n m lab).filter
          (fun τ => σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ sgnSupp τ ⊆ σ.image lab)).card +
        ((happySet n m lab).filter
          (fun τ => τ ⊆ σ ∧ σ.card = τ.card + 1 ∧ sgnSupp σ ⊆ τ.image lab)).card +
        ((happySet n m lab).filter
          (fun τ => IsBdry m σ ∧ τ = σ.image (fun x => -x))).card := by
  have hS : IsSimplex σ := (mem_happySet.1 hσ).2.1
  have e : nbrs m lab σ =
      ((happySet n m lab).filter
          (fun τ => σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ sgnSupp τ ⊆ σ.image lab) ∪
        (happySet n m lab).filter
          (fun τ => τ ⊆ σ ∧ σ.card = τ.card + 1 ∧ sgnSupp σ ⊆ τ.image lab)) ∪
        (happySet n m lab).filter
          (fun τ => IsBdry m σ ∧ τ = σ.image (fun x => -x)) := by
    ext τ
    unfold nbrs ftAdj
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hτ, _, h1 | h2 | h3⟩
      · exact Or.inl (Or.inl ⟨hτ, h1⟩)
      · exact Or.inl (Or.inr ⟨hτ, h2⟩)
      · exact Or.inr ⟨hτ, h3⟩
    · rintro ((⟨hτ, h1⟩ | ⟨hτ, h2⟩) | ⟨hτ, h3⟩)
      · refine ⟨hτ, ?_, Or.inl h1⟩
        rintro rfl
        omega
      · refine ⟨hτ, ?_, Or.inr (Or.inl h2)⟩
        rintro rfl
        omega
      · refine ⟨hτ, ?_, Or.inr (Or.inr h3)⟩
        obtain ⟨hb, rfl⟩ := h3
        exact (neg_ne_self_of_isBdry hm hS hb).symm
  have hneg : (σ.image (fun x => -x)).card = σ.card := Finset.card_image_of_injective σ neg_injective
  rw [e, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · rw [Finset.disjoint_filter]
    rintro τ _ ⟨_, h1, _⟩ ⟨_, h2, _⟩
    omega
  · rw [Finset.disjoint_union_left, Finset.disjoint_filter, Finset.disjoint_filter]
    constructor
    · rintro τ _ ⟨_, h1, _⟩ ⟨_, rfl⟩
      omega
    · rintro τ _ ⟨_, h1, _⟩ ⟨_, rfl⟩
      omega

open Classical in
theorem up_card {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) :
    ((happySet n m lab).filter
        (fun τ => σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ sgnSupp τ ⊆ σ.image lab)).card =
      ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) ⊆ σ.image lab)).card := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  have e : (happySet n m lab).filter
        (fun τ => σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ sgnSupp τ ⊆ σ.image lab) =
      ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) ⊆ σ.image lab)).image (fun q => insert q σ) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_image, mem_happySet]
    constructor
    · rintro ⟨⟨hτg, hτS, -⟩, hsub, hcard, hsupp⟩
      obtain ⟨q, hq, rfl⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcard.symm⟩
      exact ⟨q, ⟨hτg (Finset.mem_insert_self q σ), hq, hτS, hsupp⟩, rfl⟩
    · rintro ⟨q, ⟨hqg, hq, hqS, hqsupp⟩, rfl⟩
      exact ⟨⟨Finset.insert_subset hqg hg, hqS,
        hqsupp.trans (Finset.image_subset_image (Finset.subset_insert q σ))⟩,
        Finset.subset_insert q σ, Finset.card_insert_of_notMem hq, hqsupp⟩
  rw [e, Finset.card_image_of_injOn]
  intro q₁ hq₁ q₂ _ heq
  have h1 : q₁ ∉ σ := (Finset.mem_filter.1 (Finset.mem_coe.1 hq₁)).2.1
  have h2 : q₁ ∈ insert q₂ σ := by
    have : q₁ ∈ insert q₁ σ := Finset.mem_insert_self q₁ σ
    simpa only [heq] using this
  rcases Finset.mem_insert.1 h2 with h | h
  · exact h
  · exact absurd h h1

open Classical in
theorem down_card {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) :
    ((happySet n m lab).filter
        (fun τ => τ ⊆ σ ∧ σ.card = τ.card + 1 ∧ sgnSupp σ ⊆ τ.image lab)).card =
      (σ.filter (fun v => (σ.erase v).Nonempty ∧ sgnSupp σ ⊆ (σ.erase v).image lab)).card := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  have e : (happySet n m lab).filter
        (fun τ => τ ⊆ σ ∧ σ.card = τ.card + 1 ∧ sgnSupp σ ⊆ τ.image lab) =
      (σ.filter (fun v => (σ.erase v).Nonempty ∧
        sgnSupp σ ⊆ (σ.erase v).image lab)).image σ.erase := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_image, mem_happySet]
    constructor
    · rintro ⟨⟨_, hτS, -⟩, hsub, hcard, hsupp⟩
      obtain ⟨v, hv, hvτ⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcard.symm⟩
      have hev : σ.erase v = τ := by rw [← hvτ, Finset.erase_insert hv]
      refine ⟨v, ⟨?_, ?_, ?_⟩, hev⟩
      · rw [← hvτ]; exact Finset.mem_insert_self v τ
      · rw [hev]; exact hτS.1
      · rw [hev]; exact hsupp
    · rintro ⟨v, ⟨hv, hne, hsupp⟩, rfl⟩
      exact ⟨⟨(Finset.erase_subset v σ).trans hg,
        isSimplex_of_subset hS (Finset.erase_subset v σ) hne,
        (sgnSupp_mono (Finset.erase_subset v σ)).trans hsupp⟩,
        Finset.erase_subset v σ, (Finset.card_erase_add_one hv).symm, hsupp⟩
  rw [e, Finset.card_image_of_injOn]
  intro v₁ hv₁ v₂ hv₂ heq
  exact Finset.erase_injOn σ (Finset.mem_filter.1 (Finset.mem_coe.1 hv₁)).1
    (Finset.mem_filter.1 (Finset.mem_coe.1 hv₂)).1 heq

open Classical in
theorem anti_card {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    (hanti : ∀ x ∈ grid n m, (∃ i, |x i| = (m : ℤ)) → lab (-x) = flipL (lab x))
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) :
    ((happySet n m lab).filter
        (fun τ => IsBdry m σ ∧ τ = σ.image (fun x => -x))).card =
      if IsBdry m σ then 1 else 0 := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  split_ifs with hb
  · have hmem : σ.image (fun x => -x) ∈ happySet n m lab := by
      refine mem_happySet.2 ⟨neg_subset_grid hg, isSimplex_neg hS, ?_⟩
      rw [sgnSupp_neg, Finset.image_image]
      have : σ.image (lab ∘ fun x => -x) = σ.image (flipL ∘ lab) := by
        apply Finset.image_congr
        intro x hx
        obtain ⟨i, hi⟩ := hb
        exact hanti x (hg hx) ⟨i, hi x hx⟩
      rw [this, ← Finset.image_image]
      exact Finset.image_subset_image hh
    rw [Finset.card_eq_one]
    refine ⟨σ.image (fun x => -x), ?_⟩
    ext τ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, h⟩
      exact h
    · rintro rfl
      exact ⟨hmem, hb, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro τ _ h
    exact hb h.1

open Classical in
theorem tight_up {m : ℕ} (hm : 1 ≤ m) {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) (ht : σ.card = (sgnSupp σ).card) :
    ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) ⊆ σ.image lab)).card = if IsBdry m σ then 1 else 2 := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  have hL : σ.image lab = sgnSupp σ :=
    (Finset.eq_of_subset_of_card_le hh (Finset.card_image_le.trans ht.le)).symm
  rw [← tight_cofaces_card hm hS hg ht]
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [hL]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Finset.Subset.antisymm h3 (sgnSupp_mono (Finset.subset_insert q σ))⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.subset⟩

open Classical in
theorem tight_down {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (ht : σ.card = (sgnSupp σ).card) :
    (σ.filter (fun v => (σ.erase v).Nonempty ∧ sgnSupp σ ⊆ (σ.erase v).image lab)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro v hv ⟨-, h⟩
  have h1 := Finset.card_le_card h
  have h2 : ((σ.erase v).image lab).card ≤ (σ.erase v).card := Finset.card_image_le
  have h3 := Finset.card_erase_add_one hv
  omega

open Classical in
theorem loose_eq_up {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hl : σ.card = (sgnSupp σ).card + 1)
    (hL : σ.image lab = sgnSupp σ) :
    ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) ⊆ σ.image lab)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro q _ ⟨hq, hqS, hsub⟩
  have h1 := card_le_sgnSupp_card_succ hqS
  rw [Finset.card_insert_of_notMem hq] at h1
  have h2 := Finset.card_le_card hsub
  rw [hL] at h2
  omega

open Classical in
theorem loose_eq_down {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hl : σ.card = (sgnSupp σ).card + 1)
    (hL : σ.image lab = sgnSupp σ) :
    (σ.filter (fun v => (σ.erase v).Nonempty ∧ sgnSupp σ ⊆ (σ.erase v).image lab)).card = 2 := by
  have hninj : ¬ Set.InjOn lab σ := by
    rw [← Finset.card_image_iff, hL, hl]
    omega
  simp only [Set.InjOn, not_forall, Finset.mem_coe] at hninj
  obtain ⟨v₁, hv₁, v₂, hv₂, heq, hne⟩ := hninj
  have good : ∀ w ∈ σ, ∀ w' ∈ σ, w ≠ w' → lab w = lab w' →
      (σ.erase w).Nonempty ∧ sgnSupp σ ⊆ (σ.erase w).image lab := by
    intro w hw w' hw' hww' hlab
    refine ⟨⟨w', Finset.mem_erase.2 ⟨Ne.symm hww', hw'⟩⟩, ?_⟩
    rw [← hL]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    by_cases huw : u = w
    · rw [huw]
      exact Finset.mem_image.2 ⟨w', Finset.mem_erase.2 ⟨Ne.symm hww', hw'⟩, hlab.symm⟩
    · exact Finset.mem_image_of_mem lab (Finset.mem_erase.2 ⟨huw, hu⟩)
  rw [Finset.card_eq_two]
  refine ⟨v₁, v₂, hne, ?_⟩
  ext v
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, -, hsub⟩
    by_contra hvv
    rw [not_or] at hvv
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_erase_add_one hv
    have hinj : Set.InjOn lab (σ.erase v) := by
      rw [← Finset.card_image_iff]
      have hc3 : ((σ.erase v).image lab).card ≤ (σ.erase v).card := Finset.card_image_le
      omega
    exact hne (hinj (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hvv.1, hv₁⟩))
      (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hvv.2, hv₂⟩)) heq)
  · rintro (h | h) <;> rw [h]
    · exact ⟨hv₁, good _ hv₁ _ hv₂ hne heq⟩
    · exact ⟨hv₂, good _ hv₂ _ hv₁ (Ne.symm hne) heq.symm⟩

open Classical in
theorem loose_ne_up {m : ℕ} (hm : 1 ≤ m) {lab : (Fin n → ℤ) → Fin n × Bool}
    (H : ∀ x ∈ grid n m, ∀ y ∈ grid n m, (∀ i, |x i - y i| ≤ 1) → lab y ≠ flipL (lab x))
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab)
    (hl : σ.card = (sgnSupp σ).card + 1) (hL : σ.image lab ≠ sgnSupp σ) :
    ((grid n m).filter (fun q => q ∉ σ ∧ IsSimplex (insert q σ) ∧
        sgnSupp (insert q σ) ⊆ σ.image lab)).card = 1 := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  have hss : sgnSupp σ ⊂ σ.image lab := Finset.ssubset_iff_subset_ne.2 ⟨hh, Ne.symm hL⟩
  obtain ⟨ℓ, hℓL, hℓS⟩ := Finset.exists_of_ssubset hss
  have hLeq : σ.image lab = insert ℓ (sgnSupp σ) := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hℓL hh)
    rw [Finset.card_insert_of_notMem hℓS, ← hl]
    exact Finset.card_image_le
  obtain ⟨vℓ, hvℓ, hvℓlab⟩ := Finset.mem_image.1 hℓL
  have hflip : flipL ℓ ∉ sgnSupp σ := by
    intro hf
    obtain ⟨u, hu, hulab⟩ := Finset.mem_image.1 (hh hf)
    exact H vℓ (hg hvℓ) u (hg hu) (fun i => abs_sub_le_one_of_mem hS hvℓ hu i)
      (by rw [hulab, hvℓlab])
  have hj : (ℓ.1, true) ∉ sgnSupp σ ∧ (ℓ.1, false) ∉ sgnSupp σ := by
    obtain ⟨j, b⟩ := ℓ
    cases b
    · exact ⟨hflip, hℓS⟩
    · exact ⟨hℓS, hflip⟩
  rw [← loose_cofaces_card hm hS hg hl ℓ.1 ℓ.2 hj.1 hj.2]
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [hLeq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, Finset.eq_of_subset_of_card_le h3 ?_⟩
    have := card_le_sgnSupp_card_succ h2
    rw [Finset.card_insert_of_notMem h1] at this
    rw [Finset.card_insert_of_notMem hℓS]
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.subset⟩

open Classical in
theorem loose_ne_down {m : ℕ} {lab : (Fin n → ℤ) → Fin n × Bool}
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab)
    (hl : σ.card = (sgnSupp σ).card + 1) (hL : σ.image lab ≠ sgnSupp σ) :
    (σ.filter (fun v => (σ.erase v).Nonempty ∧ sgnSupp σ ⊆ (σ.erase v).image lab)).card =
      if σ = {0} then 0 else 1 := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  have hss : sgnSupp σ ⊂ σ.image lab := Finset.ssubset_iff_subset_ne.2 ⟨hh, Ne.symm hL⟩
  obtain ⟨ℓ, hℓL, hℓS⟩ := Finset.exists_of_ssubset hss
  obtain ⟨vℓ, hvℓ, hvℓlab⟩ := Finset.mem_image.1 hℓL
  have key : ∀ v ∈ σ, (sgnSupp σ ⊆ (σ.erase v).image lab ↔ v = vℓ) := by
    intro v hv
    constructor
    · intro hsub
      by_contra hne
      have h1 : insert ℓ (sgnSupp σ) ⊆ (σ.erase v).image lab := by
        refine Finset.insert_subset ?_ hsub
        rw [← hvℓlab]
        exact Finset.mem_image_of_mem lab (Finset.mem_erase.2 ⟨Ne.symm hne, hvℓ⟩)
      have h2 := Finset.card_le_card h1
      rw [Finset.card_insert_of_notMem hℓS] at h2
      have h3 : ((σ.erase v).image lab).card ≤ (σ.erase v).card := Finset.card_image_le
      have h4 := Finset.card_erase_add_one hv
      omega
    · intro hvv
      rw [hvv]
      intro x hx
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.1 (hh hx)
      have hne : u ≠ vℓ := by
        intro huv
        rw [huv, hvℓlab] at hux
        rw [← hux] at hx
        exact hℓS hx
      rw [← hux]
      exact Finset.mem_image_of_mem lab (Finset.mem_erase.2 ⟨hne, hu⟩)
  have hfilt : σ.filter (fun v => (σ.erase v).Nonempty ∧ sgnSupp σ ⊆ (σ.erase v).image lab) =
      σ.filter (fun v => (σ.erase vℓ).Nonempty ∧ v = vℓ) := by
    apply Finset.filter_congr
    intro v hv
    rw [key v hv]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [← h2] at h1
      exact ⟨h1, h2⟩
  rw [hfilt]
  by_cases hne : (σ.erase vℓ).Nonempty
  · have hσ0 : σ ≠ {0} := by
      intro h0
      rw [h0, Finset.mem_singleton] at hvℓ
      rw [h0, hvℓ, Finset.erase_singleton] at hne
      exact Finset.not_nonempty_empty hne
    rw [ite_eq_right hσ0, Finset.card_eq_one]
    refine ⟨vℓ, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, h⟩
      exact h
    · intro h
      rw [h]
      exact ⟨hvℓ, hne, rfl⟩
  · have hσ0 : σ = {0} := by
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hc := Finset.card_erase_add_one hvℓ
      rw [hne, Finset.card_empty] at hc
      have hS0 : sgnSupp σ = ∅ := by
        rw [← Finset.card_eq_zero]
        omega
      have hc1 : σ.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc1
      have ha0 : a = 0 := sgnSupp_eq_empty_iff.1 hS0 a (by rw [ha]; exact Finset.mem_singleton_self a)
      rw [ha, ha0]
    rw [ite_eq_left hσ0, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _ h
    exact hne h.1

theorem nbrs_card {m : ℕ} (hm : 1 ≤ m) {lab : (Fin n → ℤ) → Fin n × Bool}
    (hanti : ∀ x ∈ grid n m, (∃ i, |x i| = (m : ℤ)) → lab (-x) = flipL (lab x))
    (H : ∀ x ∈ grid n m, ∀ y ∈ grid n m, (∀ i, |x i - y i| ≤ 1) → lab y ≠ flipL (lab x))
    {σ : Finset (Fin n → ℤ)} (hσ : σ ∈ happySet n m lab) :
    (nbrs m lab σ).card = if σ = {0} then 1 else 2 := by
  obtain ⟨hg, hS, hh⟩ := mem_happySet.1 hσ
  rw [nbrs_card_eq hm hσ, up_card hσ, down_card hσ, anti_card hanti hσ]
  have hc1 := card_le_sgnSupp_card_succ hS
  have hc2 := Finset.card_le_card hh
  have hc3 : (σ.image lab).card ≤ σ.card := Finset.card_image_le
  rcases (by omega : σ.card = (sgnSupp σ).card ∨ σ.card = (sgnSupp σ).card + 1) with ht | hl
  · rw [tight_up hm hσ ht, tight_down ht]
    have hσ0 : σ ≠ {0} := by
      rintro rfl
      rw [sgnSupp_zero] at ht
      simp at ht
    rw [ite_eq_right hσ0]
    split_ifs <;> rfl
  · rw [ite_eq_right (not_isBdry_of_loose hm hS hl)]
    by_cases hL : σ.image lab = sgnSupp σ
    · rw [loose_eq_up hl hL, loose_eq_down hl hL]
      have hσ0 : σ ≠ {0} := by
        rintro rfl
        rw [sgnSupp_zero] at hL
        simp at hL
      rw [ite_eq_right hσ0]
    · rw [loose_ne_up hm H hσ hl hL, loose_ne_down hσ hl hL]
      split_ifs <;> rfl

end FT

open FT in
theorem tucker : TuckerStatement := by
  classical
  intro n m hm lab hanti
  by_contra Hc
  have H : ∀ x ∈ grid n m, ∀ y ∈ grid n m, (∀ i, |x i - y i| ≤ 1) → lab y ≠ flipL (lab x) := by
    intro x hx y hy hxy hlab
    exact Hc ⟨x, y, mem_grid.1 hx, mem_grid.1 hy, hxy, hlab⟩
  have hanti' : ∀ x ∈ grid n m, (∃ i, |x i| = (m : ℤ)) → lab (-x) = flipL (lab x) :=
    fun x hx hi => hanti x (mem_grid.1 hx) hi
  have hodd : (Finset.univ.filter (fun v : {σ // σ ∈ happySet n m lab} =>
      Odd ((ftGraph m lab).degree v))) = {⟨{0}, zero_mem_happySet⟩} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [ftGraph_degree v, nbrs_card hm hanti' H v.2]
    constructor
    · intro h
      split_ifs at h with hv
      · exact Subtype.ext hv
      · exact absurd h (by decide)
    · rintro rfl
      simp
  have heven := (ftGraph m lab).even_card_odd_degree_vertices
  rw [hodd, Finset.card_singleton] at heven
  exact absurd heven (by decide)

end Tucker
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
