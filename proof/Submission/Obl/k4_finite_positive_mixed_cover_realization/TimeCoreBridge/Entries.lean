-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/Entries.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Entries.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 793edcb4e591,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Entries.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GraphAssembly

/-!
# Entries of a greedy cover and their geometric member sets

An *entry* is a candidate `a`, a sub-block `jj < 2^{s₀}` of its old packet's block, a box index
(in a bounded range, `boxOf`) for the normalized position at the sub-block midpoint, a sign of the
candidate's hidden derivative and a sign of the old test's hidden derivative, both at the
midpoint. `memE` is the set of lines of the candidate's assignment `A' a` with these data; it has a
fixed Boolean format, and entries with different data have disjoint member sets.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The integer box index of a normalized position. -/
noncomputable def boxIdx (s₀ : ℕ) (z : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ :=
  fun e => ⌊z e / side s₀⌋

theorem inBox_iff_boxIdx {s₀ : ℕ} {k : Fin 2 → ℤ} {z : EuclideanSpace ℝ (Fin 2)} :
    inBox s₀ k z ↔ boxIdx s₀ z = k := by
  have hs := side_pos s₀
  constructor
  · intro h
    funext e
    obtain ⟨h1, h2⟩ := h e
    simp only [boxIdx]
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hs]; exact h1
    · rw [div_lt_iff₀ hs]; exact h2
  · intro h e
    have he := congrFun h e
    simp only [boxIdx] at he
    rw [Int.floor_eq_iff] at he
    obtain ⟨h1, h2⟩ := he
    exact ⟨(le_div_iff₀ hs).mp h1, (div_lt_iff₀ hs).mp h2⟩

/-- Bounded box indices `Fin (2K+2)`, read as integers in `[-(K+1), K]`. -/
def boxOf (K : ℕ) (k : Fin 2 → Fin (2 * K + 2)) : Fin 2 → ℤ :=
  fun e => (k e : ℤ) - (K + 1)

theorem boxOf_injective (K : ℕ) : Function.Injective (boxOf K) := by
  intro k k' h
  funext e
  have := congrFun h e
  simp only [boxOf] at this
  exact Fin.ext (by omega)

/-- The data of an entry. -/
abbrev Entry (n s₀ K : ℕ) := Fin n × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool × Bool

section Members

variable {n C : ℕ} (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
  (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (j : Fin C → ℕ)
  (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
  (R : Fin C → MvPolynomial (Fin 4) ℝ) (Ti s₀ K : ℕ)

/-- The midpoint time of an entry's sub-block. -/
noncomputable def entryMid (e : Entry n s₀ K) : ℝ := subMid Ti s₀ (j (old e.1)) e.2.1

/-- The lines of an entry. -/
def memE (e : Entry n s₀ K) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | l ∈ A' e.1 ∧
    boxIdx s₀ (zc (Q (old e.1)) (c (old e.1)) (u (old e.1)) l (entryMid old j Ti s₀ K e)) =
      boxOf K e.2.2.1 ∧
    decide (0 ≤ eval (gx l (entryMid old j Ti s₀ K e)) (pderiv 3 (R' e.1))) = e.2.2.2.1 ∧
    decide (0 ≤ eval (gx l (entryMid old j Ti s₀ K e)) (pderiv 3 (R (old e.1)))) = e.2.2.2.2}

theorem memE_subset_inBox {e : Entry n s₀ K} {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ memE old R' A' j c u Q R Ti s₀ K e) :
    l ∈ A' e.1 ∧ inBox s₀ (boxOf K e.2.2.1)
      (zc (Q (old e.1)) (c (old e.1)) (u (old e.1)) l (subMid Ti s₀ (j (old e.1)) e.2.1)) :=
  ⟨hl.1, inBox_iff_boxIdx.mpr hl.2.1⟩

/-- Entries of one candidate and one sub-block with different data have disjoint lines. -/
theorem memE_disjoint_of_ne {e e' : Entry n s₀ K} (ha : e.1 = e'.1) (hjj : e.2.1 = e'.2.1)
    (hne : e ≠ e') :
    Disjoint (memE old R' A' j c u Q R Ti s₀ K e) (memE old R' A' j c u Q R Ti s₀ K e') := by
  rw [Set.disjoint_left]
  intro l hl hl'
  apply hne
  obtain ⟨a, jj, k, sc, st⟩ := e
  obtain ⟨a', jj', k', sc', st'⟩ := e'
  simp only at ha hjj
  subst ha hjj
  have hmid : entryMid old j Ti s₀ K (a, jj, k, sc, st) =
      entryMid old j Ti s₀ K (a, jj, k', sc', st') := rfl
  obtain ⟨-, hk, hsc, hst⟩ := hl
  obtain ⟨-, hk', hsc', hst'⟩ := hl'
  rw [hmid] at hk hsc hst
  have hkk : k = k' := boxOf_injective K (hk.symm.trans hk')
  have hscc : sc = sc' := hsc.symm.trans hsc'
  have hstt : st = st' := hst.symm.trans hst'
  rw [hkk, hscc, hstt]

end Members

section Formats

/-- A component of the normalized position at a fixed time, as an affine polynomial in the line
coordinates. -/
noncomputable def zcPoly (Qi : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (e : Fin 2) : MvPolynomial (Fin 6) ℝ :=
  C (Qi e 0) * (X 0 + C t * X 3 - C (c 0) - C (t * u 0)) +
    C (Qi e 1) * (X 1 + C t * X 4 - C (c 1) - C (t * u 1))

theorem eval_zcPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (e : Fin 2) (i : ℕ) (z : Fin 6 → ℝ) :
    eval z (zcPoly Q⁻¹ c u t e) = (zc Q c u (i, z) t) e := by
  simp only [zcPoly, zc, toEuclideanLin_apply_fin2]
  simp [gy, gx]

theorem totalDegree_zcPoly_le (Qi : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (t : ℝ) (e : Fin 2) : (zcPoly Qi c u t e).totalDegree ≤ 1 := by
  unfold zcPoly
  have hlin : ∀ (a b : Fin 6) (x y : ℝ), (X a + C t * X b - C x - C y :
      MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := by
    intro a b x y
    refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
    refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
    refine (totalDegree_add _ _).trans (max_le (by simp [totalDegree_X]) ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]; exact hlin _ _ _ _
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]; exact hlin _ _ _ _

/-- A sign condition of a polynomial. -/
theorem gfmt_sign {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (b : Bool) :
    gfmt n 1 p.totalDegree {x | decide (0 ≤ eval x p) = b} := by
  cases b
  · have h := gfmt_compl (gfmt_nonneg p)
    have e : {x : Fin n → ℝ | 0 ≤ eval x p}ᶜ = {x | decide (0 ≤ eval x p) = false} := by
      ext x; simp
    rwa [e] at h
  · have h := gfmt_nonneg p
    have e : {x : Fin n → ℝ | 0 ≤ eval x p} = {x | decide (0 ≤ eval x p) = true} := by
      ext x; simp
    rwa [e] at h

/-- Box membership of the normalized position at a fixed time. -/
theorem gfmt_boxIdx (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (s₀ : ℕ) (k : Fin 2 → ℤ) (i : ℕ) :
    gfmt 6 4 1 {z : Fin 6 → ℝ | boxIdx s₀ (zc Q c u (i, z) t) = k} := by
  have hcomp : ∀ e : Fin 2, gfmt 6 2 1 {z : Fin 6 → ℝ | (k e : ℝ) * side s₀ ≤ (zc Q c u (i, z) t) e ∧
      (zc Q c u (i, z) t) e < ((k e : ℝ) + 1) * side s₀} := by
    intro e
    have h1 := gfmt_ge_const (zcPoly Q⁻¹ c u t e) ((k e : ℝ) * side s₀)
    have h2 := gfmt_compl (gfmt_ge_const (zcPoly Q⁻¹ c u t e) (((k e : ℝ) + 1) * side s₀))
    have h := gfmt_inter h1 h2
    have hd := totalDegree_zcPoly_le Q⁻¹ c u t e
    have e1 : {x : Fin 6 → ℝ | (k e : ℝ) * side s₀ ≤ eval x (zcPoly Q⁻¹ c u t e)} ∩
        {x : Fin 6 → ℝ | ((k e : ℝ) + 1) * side s₀ ≤ eval x (zcPoly Q⁻¹ c u t e)}ᶜ =
        {z : Fin 6 → ℝ | (k e : ℝ) * side s₀ ≤ (zc Q c u (i, z) t) e ∧
          (zc Q c u (i, z) t) e < ((k e : ℝ) + 1) * side s₀} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le,
        eval_zcPoly Q c u t e i z]
    rw [e1] at h
    exact gfmt_mono (by norm_num) (max_le hd hd) h
  have h := gfmt_inter (hcomp 0) (hcomp 1)
  have e : {z : Fin 6 → ℝ | (k 0 : ℝ) * side s₀ ≤ (zc Q c u (i, z) t) 0 ∧
      (zc Q c u (i, z) t) 0 < ((k 0 : ℝ) + 1) * side s₀} ∩
      {z : Fin 6 → ℝ | (k 1 : ℝ) * side s₀ ≤ (zc Q c u (i, z) t) 1 ∧
        (zc Q c u (i, z) t) 1 < ((k 1 : ℝ) + 1) * side s₀} =
      {z : Fin 6 → ℝ | boxIdx s₀ (zc Q c u (i, z) t) = k} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ← inBox_iff_boxIdx, inBox]
    constructor
    · rintro ⟨h0, h1⟩ e; fin_cases e
      · exact h0
      · exact h1
    · intro h; exact ⟨h 0, h 1⟩
  rw [e] at h
  exact gfmt_mono (by norm_num) (by simp) h

/-- The member set of an entry has a fixed Boolean format at every copy index. -/
theorem gfmt_memE {n C : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ} {Ti s₀ K : ℕ} {H : ℝ} {Dg : ℕ}
    (hA' : ∀ a q, gfmt 6 H Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (e : Entry n s₀ K) (q : ℕ) :
    gfmt 6 (H + 6) (max Dg 2) {z | (q, z) ∈ memE old R' A' j c u Q R Ti s₀ K e} := by
  set tm := entryMid old j Ti s₀ K e
  have hs1 := gfmt_sign (slicePoly tm (pderiv 3 (R' e.1))) e.2.2.2.1
  have hs2 := gfmt_sign (slicePoly tm (pderiv 3 (R (old e.1)))) e.2.2.2.2
  have hd1 : (slicePoly tm (pderiv 3 (R' e.1))).totalDegree ≤ 2 :=
    (totalDegree_slicePoly_le _ _).trans
      ((totalDegree_pderiv_le' _ (3 : Fin 4) (d := 1) (hR' e.1)).trans (by norm_num))
  have hd2 : (slicePoly tm (pderiv 3 (R (old e.1)))).totalDegree ≤ 2 :=
    (totalDegree_slicePoly_le _ _).trans
      ((totalDegree_pderiv_le' _ (3 : Fin 4) (d := 1) (hR (old e.1))).trans (by norm_num))
  have hb := gfmt_boxIdx (Q (old e.1)) (c (old e.1)) (u (old e.1)) tm s₀ (boxOf K e.2.2.1) q
  have h := gfmt_inter (hA' e.1 q) (gfmt_inter hb (gfmt_inter (gfmt_mono le_rfl hd1 hs1)
    (gfmt_mono le_rfl hd2 hs2)))
  have eq : {z | (q, z) ∈ A' e.1} ∩ ({z : Fin 6 → ℝ |
      boxIdx s₀ (zc (Q (old e.1)) (c (old e.1)) (u (old e.1)) (q, z) tm) = boxOf K e.2.2.1} ∩
      ({x | decide (0 ≤ eval x (slicePoly tm (pderiv 3 (R' e.1)))) = e.2.2.2.1} ∩
        {x | decide (0 ≤ eval x (slicePoly tm (pderiv 3 (R (old e.1))))) = e.2.2.2.2})) =
      {z | (q, z) ∈ memE old R' A' j c u Q R Ti s₀ K e} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, memE, eval_slicePoly _ _ q z]
    rfl
  rw [eq] at h
  exact gfmt_mono (by linarith) (by omega) h

/-- Finite unions of sets in format. -/
theorem gfmt_finset_iUnion {n : ℕ} {α : Type*} (S : Finset α) {H : ℝ} {D : ℕ} (hH : 0 ≤ H)
    (A : α → Set (Fin n → ℝ)) (h : ∀ a ∈ S, gfmt n H D (A a)) :
    gfmt n (S.card * H) D (⋃ a ∈ S, A a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.notMem_empty,
      Set.iUnion_of_empty, Set.iUnion_empty]
    have := gfmt_compl (gfmt_univ n 0 le_rfl D)
    simpa using this
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    have hu := gfmt_union h1 h2
    rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha]
    refine gfmt_mono (by push_cast; linarith) (by simp) hu

end Formats

section Reduction

theorem subIdx_inj {s₀ j₀ j₀' jj jj' : ℕ} (hjj : jj < 2 ^ s₀) (hjj' : jj' < 2 ^ s₀)
    (h : subIdx s₀ j₀ jj = subIdx s₀ j₀' jj') : j₀ = j₀' ∧ jj = jj' := by
  unfold subIdx at h
  have hp : 0 < 2 ^ s₀ := by positivity
  have h1 : (j₀ * 2 ^ s₀ + jj) / 2 ^ s₀ = j₀ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hjj, zero_add]
  have h2 : (j₀' * 2 ^ s₀ + jj') / 2 ^ s₀ = j₀' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hjj', zero_add]
  have h3 : (j₀ * 2 ^ s₀ + jj) % 2 ^ s₀ = jj := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj]
  have h4 : (j₀' * 2 ^ s₀ + jj') % 2 ^ s₀ = jj' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj']
  exact ⟨by rw [← h1, ← h2, h], by rw [← h3, ← h4, h]⟩

/-- The group (old packet, sub-block, box, true sign) of an entry. -/
def entryGroup {n C s₀ K : ℕ} (old : Fin n → Fin C) (e : Entry n s₀ K) :
    Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool :=
  (old e.1, e.2.1, e.2.2.1, e.2.2.2.2)

/-- **Graph atlas from entries.** Bins, representatives, lists, closeness of covered points
to the representative root tests and their list success give the graph atlas. -/
theorem graphAtlas_of_entries
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {r₀ h θ β : ℝ} {M D : ℕ}
    {C : ℕ} {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
    {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Fin C → Prop} {κ : ℝ} {Mp Dp : ℕ}
    {i Ti : ℕ} {rold : ℝ}
    {n : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {Mg Dg : ℕ} {s₀ K : ℕ}
    {ME DE : ℕ}
    -- bins, representatives, lists and covered points
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (binOf : Entry n s₀ K → Λ)
    (P : (Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ →
      MvPolynomial (Fin 4) ℝ)
    (s m₀ : (Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ → ℝ)
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) →
      Finset ((Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ))
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    -- the sample
    (hNk : 1 ≤ Nk) (hB : ∀ w, 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M)
    (hE : ∀ w q, gfmt 7 (Nk ^ ME) DE
      {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E w})
    (hold : ∀ a, gchart Nk Mp Dp κ Ti (j (old a) : ℝ) rold (B (γ (old a))) (E (γ (old a)))
      (c (old a)) (u (old a)) (Q (old a)) (R (old a)) (A (old a)) (F (old a)) (ex (old a)))
    (hlev : ∀ a, lev (old a) = i) (hjlt : ∀ a, j (old a) < 2 ^ Ti)
    (hAdisj : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hA'A : ∀ a, A' a ⊆ A (old a))
    (hA'disj : ∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a'))
    (hA'fmt : ∀ a q, gfmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    -- representatives
    (hP : ∀ ℓ, (P ℓ).totalDegree ≤ 2) (hPcoef : ∀ ℓ e, |(P ℓ).coeff e| ≤ Nk ^ M)
    (hs : ∀ ℓ, 0 < s ℓ ∧ s ℓ ≤ Nk ^ M ∧ (s ℓ)⁻¹ ≤ Nk ^ M)
    (hm₀ : ∀ ℓ, 0 ≤ m₀ ℓ ∧ m₀ ℓ ≤ rootThreshold Nk r₀ h θ L (B (γ ℓ.1.1)) (s ℓ))
    (hcurv : ∀ ℓ, |qc (P ℓ)| * m₀ ℓ ≤ s ℓ ^ 2 / 40)
    -- covered points, closeness, lists and success
    (hcov : ∀ e, cov e ⊆ {p | p ∈ E (γ (old e.1)) ∧
      p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧ p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1})
    (hclose : ∀ e, ∀ p ∈ cov e, p.1 ∈ rootTestSet (P (entryGroup old e, binOf e))
      (s (entryGroup old e, binOf e)) (m₀ (entryGroup old e, binOf e))
      ((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)))
    (hlst : ∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ β)
    (hlstm : ∀ w ℓ, MeasurableSet {o | ℓ ∈ lst w o})
    (hsucc : ENNReal.ofReal (Nk ^ (-β)) ≤ ∑ ℓ, ENNReal.ofReal (ω (γ ℓ.1.1)) *
      ((ν (γ ℓ.1.1)).prod volume) {p | (∃ e, (entryGroup old e, binOf e) = ℓ ∧ p ∈ cov e) ∧
        ℓ ∈ lst (γ ℓ.1.1) (obs (B (γ ℓ.1.1)) (δ Nk L) p)})
    -- parameters
    (hκ : κ + 1 ≤ Nk ^ β) (hMp : Mp ≤ M) (hcu : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ M)
    (hfr : (side s₀)⁻¹ * Nk ^ Mp ≤ Nk ^ M)
    (hfmtM : Nk ^ ME + (Fintype.card (Entry n s₀ K) : ℝ) * (Nk ^ Mg + 6) + 11 + 3 ≤ Nk ^ M)
    (hD : max DE (max (max Dg 2) 4) ≤ D)
    (hcard : (Fintype.card ((Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ) : ℝ)
      ≤ Nk ^ M) :
    ∃ (C₂ : ℕ) (γ₃ : Fin C₂ → Fin W) (j₃ : Fin C₂ → Fin (2 ^ (Ti + s₀)))
      (c₃ u₃ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₃ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
      (P₃ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (s₃ : Fin C₂ → ℝ)
      (A₃ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ))) (F₃ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₃ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
      GraphAtlas Nk L W ω ν E B r₀ h θ β M D (Ti + s₀) C₂ γ₃ j₃ c₃ u₃ Q₃ P₃ s₃ A₃ F₃ lst₃ := by
  classical
  -- labels and their member sets
  let Lab := (Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ
  let lab : Entry n s₀ K → Lab := fun e => (entryGroup old e, binOf e)
  let memL : Lab → Set (ℕ × (Fin 6 → ℝ)) := fun ℓ =>
    ⋃ e ∈ Finset.univ.filter (fun e => lab e = ℓ), memE old R' A' j c u Q R Ti s₀ K e
  let ι := {ℓ : Lab // (memL ℓ).Nonempty}
  -- an entry of a label shares its group
  have hgrp : ∀ ℓ : Lab, ∀ e, lab e = ℓ → old e.1 = ℓ.1.1 ∧ e.2.1 = ℓ.1.2.1 ∧
      e.2.2.1 = ℓ.1.2.2.1 := by
    intro ℓ e he
    rw [← he]
    exact ⟨rfl, rfl, rfl⟩
  have hmemL : ∀ ℓ : Lab, ∀ l ∈ memL ℓ, ∃ e, lab e = ℓ ∧
      l ∈ memE old R' A' j c u Q R Ti s₀ K e := by
    intro ℓ l hl
    simp only [memL, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    obtain ⟨e, he, hl⟩ := hl
    exact ⟨e, he, hl⟩
  -- a chosen entry of each nonempty label
  have hentry : ∀ ℓ : ι, ∃ e, lab e = ℓ.1 := by
    intro ℓ
    obtain ⟨l, hl⟩ := ℓ.2
    obtain ⟨e, he, -⟩ := hmemL ℓ.1 l hl
    exact ⟨e, he⟩
  let e₀ : ι → Entry n s₀ K := fun ℓ => (hentry ℓ).choose
  have he₀ : ∀ ℓ : ι, lab (e₀ ℓ) = ℓ.1 := fun ℓ => (hentry ℓ).choose_spec
  have hpk : ∀ ℓ : ι, old (e₀ ℓ).1 = ℓ.1.1.1 := fun ℓ => (hgrp ℓ.1 (e₀ ℓ) (he₀ ℓ)).1
  -- the member format
  have hfmtE : ∀ e q, gfmt 6 (Nk ^ Mg + 6) (max Dg 2)
      {z | (q, z) ∈ memE old R' A' j c u Q R Ti s₀ K e} :=
    fun e q => gfmt_memE hA'fmt hR' hR e q
  have hfmtL : ∀ (ℓ : Lab) q, gfmt 6 ((Fintype.card (Entry n s₀ K) : ℝ) * (Nk ^ Mg + 6))
      (max Dg 2) {z | (q, z) ∈ memL ℓ} := by
    intro ℓ q
    have h := gfmt_finset_iUnion (Finset.univ.filter (fun e => lab e = ℓ))
      (by positivity : (0 : ℝ) ≤ Nk ^ Mg + 6)
      (fun e => {z | (q, z) ∈ memE old R' A' j c u Q R Ti s₀ K e}) (fun e _ => hfmtE e q)
    have e : (⋃ e ∈ Finset.univ.filter (fun e => lab e = ℓ),
        {z | (q, z) ∈ memE old R' A' j c u Q R Ti s₀ K e}) = {z | (q, z) ∈ memL ℓ} := by
      ext z
      simp only [memL, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [e] at h
    refine gfmt_mono ?_ le_rfl h
    have hc : ((Finset.univ.filter (fun e => lab e = ℓ)).card : ℝ) ≤
        (Fintype.card (Entry n s₀ K) : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  let lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι :=
    fun w o => (lst w o).subtype (fun ℓ => (memL ℓ).Nonempty)
  refine graphAtlas_of_labels (ι := ι) (fun ℓ => ℓ.1.1.1) (fun ℓ => (ℓ.1.1.2.1 : ℕ))
    (fun ℓ => boxOf K ℓ.1.1.2.2.1) (fun ℓ => P ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => m₀ ℓ.1)
    (fun ℓ => memL ℓ.1)
    (fun ℓ => memL ℓ.1 ∩ rootTestSet (P ℓ.1) (s ℓ.1) (m₀ ℓ.1)
      ((subIdx s₀ (j ℓ.1.1.1) (ℓ.1.1.2.1 : ℕ) : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j ℓ.1.1.1) (ℓ.1.1.2.1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)))
    lst' s₀ (Hmem := (Fintype.card (Entry n s₀ K) : ℝ) * (Nk ^ Mg + 6)) (Dmem := max Dg 2)
    hNk hB hE (fun ℓ => by rw [← hpk ℓ]; exact hold (e₀ ℓ).1)
    (fun ℓ => by rw [← hpk ℓ]; exact hjlt (e₀ ℓ).1) (fun ℓ => ℓ.1.1.2.1.isLt)
    (fun ℓ => hP ℓ.1) (fun ℓ => hPcoef ℓ.1) (fun ℓ => hs ℓ.1) (fun ℓ => hm₀ ℓ.1)
    (fun ℓ => hcurv ℓ.1)
    ?_ (fun ℓ q => hfmtL ℓ.1 q) (fun ℓ => ℓ.2) ?_ (fun ℓ => le_rfl) ?_ ?_ ?_
    hκ hMp hcu hfr hfmtM hD ?_
  · -- members lie in the packet and the box
    intro ℓ l hl
    obtain ⟨e, he, hle⟩ := hmemL ℓ.1 l hl
    obtain ⟨h1, h2, h3⟩ := hgrp ℓ.1 e he
    obtain ⟨hA', hbox⟩ := memE_subset_inBox old R' A' j c u Q R Ti s₀ K hle
    rw [h1] at hbox
    rw [h2, h3] at hbox
    refine ⟨?_, hbox⟩
    rw [← h1]
    exact hA'A e.1 hA'
  · -- disjointness
    intro ℓ ℓ' hne hγ hj
    rw [Set.disjoint_left]
    intro l hl hl'
    obtain ⟨e, he, hle⟩ := hmemL ℓ.1 l hl
    obtain ⟨e', he', hle'⟩ := hmemL ℓ'.1 l hl'
    obtain ⟨h1, h2, -⟩ := hgrp ℓ.1 e he
    obtain ⟨h1', h2', -⟩ := hgrp ℓ'.1 e' he'
    have hjj := subIdx_inj ℓ.1.1.2.1.isLt ℓ'.1.1.2.1.isLt hj
    have hA1 := hA'A e.1 hle.1
    have hA2 := hA'A e'.1 hle'.1
    by_cases hold' : old e.1 = old e'.1
    · by_cases ha : e.1 = e'.1
      · have hjje : e.2.1 = e'.2.1 := by
          rw [h2, h2']; exact Fin.ext hjj.2
        by_cases hee : e = e'
        · apply hne
          apply Subtype.ext
          rw [← he, ← he', hee]
        · exact Set.disjoint_left.mp (memE_disjoint_of_ne old R' A' j c u Q R Ti s₀ K ha hjje hee)
            hle hle'
      · exact Set.disjoint_left.mp (hA'disj e.1 e'.1 ha hold') hle.1 hle'.1
    · have hγ' : γ (old e.1) = γ (old e'.1) := by rw [h1, h1']; exact hγ
      have hj' : j (old e.1) = j (old e'.1) := by rw [h1, h1']; exact hjj.1
      have hlev : lev (old e.1) = lev (old e'.1) := by rw [hlev, hlev]
      exact Set.disjoint_left.mp (hAdisj _ _ hold' hlev hγ' hj') hA1 hA2
  · -- lists
    intro w o
    calc ((lst' w o).card : ℝ) ≤ (lst w o).card := by
          exact_mod_cast (Finset.card_subtype _ _).le.trans (Finset.card_filter_le _ _)
      _ ≤ Nk ^ β := hlst w o
  · intro w ℓ
    have : {o | ℓ ∈ lst' w o} = {o | ℓ.1 ∈ lst w o} := by
      ext o; exact Finset.mem_subtype
    rw [this]; exact hlstm w ℓ.1
  · -- success
    refine hsucc.trans ?_
    rw [← Fintype.sum_subtype_add_sum_subtype (fun ℓ : Lab => (memL ℓ).Nonempty)]
    have hzero : ∑ ℓ : {ℓ : Lab // ¬ (memL ℓ).Nonempty}, ENNReal.ofReal (ω (γ ℓ.1.1.1)) *
        ((ν (γ ℓ.1.1.1)).prod volume) {p | (∃ e, (entryGroup old e, binOf e) = ℓ.1 ∧ p ∈ cov e) ∧
          ℓ.1 ∈ lst (γ ℓ.1.1.1) (obs (B (γ ℓ.1.1.1)) (δ Nk L) p)} = 0 := by
      refine Finset.sum_eq_zero fun ℓ _ => ?_
      have hempty : {p : (ℕ × (Fin 6 → ℝ)) × ℝ | (∃ e, (entryGroup old e, binOf e) = ℓ.1 ∧
          p ∈ cov e) ∧ ℓ.1 ∈ lst (γ ℓ.1.1.1) (obs (B (γ ℓ.1.1.1)) (δ Nk L) p)} = ∅ := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨e, he, hp⟩ -
        apply ℓ.2
        refine ⟨p.1, ?_⟩
        simp only [memL, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, he, (hcov e hp).2.1⟩
      rw [hempty, measure_empty, mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_le_sum fun ℓ _ => mul_le_mul_right (measure_mono ?_) _
    rintro p ⟨⟨e, he, hp⟩, hpl⟩
    obtain ⟨hpE, hpm, hpt⟩ := hcov e hp
    obtain ⟨h1, h2, -⟩ := hgrp ℓ.1 e he
    have hcl := hclose e p hp
    rw [show (entryGroup old e, binOf e) = ℓ.1 from he] at hcl
    refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← h1]; exact hpE
    · simp only [memL, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hpm⟩
    · rw [h1, h2] at hcl; exact hcl
    · rw [h1, h2] at hpt; exact hpt
    · exact Finset.mem_subtype.mpr hpl
  · -- count
    calc (Fintype.card ι : ℝ) ≤ Fintype.card Lab := by exact_mod_cast Fintype.card_subtype_le _
      _ ≤ Nk ^ M := hcard

end Reduction

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
