-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/EntryPartition.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0674 via x0672,
-- commit69d09a7b, Submission/Obl/k4_greedy_cover_graph_atlas/EntryPartition.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Entries

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface

private theorem exists_fin_shift {K : ℕ} {k : ℤ}
    (hlo : -((K : ℤ) + 1) ≤ k) (hhi : k ≤ K) :
    ∃ b : Fin (2 * K + 2), (b : ℤ) - (K + 1) = k := by
  refine ⟨⟨(k + (K + 1)).toNat, by omega⟩, ?_⟩
  change ((k + (K + 1)).toNat : ℤ) - (K + 1) = k
  omega

private theorem bounded_floor {K : ℕ} {z a : ℝ} (ha : 0 < a)
    (hz : |z| ≤ K * a) :
    -((K : ℤ) + 1) ≤ ⌊z / a⌋ ∧ ⌊z / a⌋ ≤ K := by
  have h := abs_le.mp hz
  constructor
  · apply Int.le_floor.mpr
    push_cast
    rw [le_div_iff₀ ha]
    nlinarith
  · apply Int.floor_le_iff.mpr
    push_cast
    rw [div_lt_iff₀ ha]
    nlinarith

/-- The bounded index type contains the box of every point in the required ball. -/
theorem exists_boxOf_eq_boxIdx {s₀ K : ℕ} {z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖z‖ ≤ K * side s₀) :
    ∃ k : Fin 2 → Fin (2 * K + 2), boxOf K k = boxIdx s₀ z := by
  have hcoord (e : Fin 2) : |z e| ≤ K * side s₀ := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le z e).trans hz
  have hex (e : Fin 2) : ∃ b : Fin (2 * K + 2),
      (b : ℤ) - (K + 1) = boxIdx s₀ z e := by
    have h := bounded_floor (side_pos s₀) (hcoord e)
    exact exists_fin_shift h.1 h.2
  choose k hk using hex
  exact ⟨k, funext hk⟩


/-- Choose a bounded box range using the old chart allowance. -/
noncomputable def boxRange (κ : ℝ) (s₀ : ℕ) : ℕ := ⌈κ / side s₀⌉₊

theorem le_boxRange_mul_side (κ : ℝ) (s₀ : ℕ) :
    κ ≤ boxRange κ s₀ * side s₀ := by
  exact (div_le_iff₀ (side_pos s₀)).mp (Nat.le_ceil (κ / side s₀))

theorem boxRange_le {κ : ℝ} (hκ : 0 ≤ κ) (s₀ : ℕ) :
    (boxRange κ s₀ : ℝ) ≤ κ / side s₀ + 1 :=
  (Nat.ceil_lt_add_one (div_nonneg hκ (side_pos s₀).le)).le

section Members

variable {n C : ℕ} (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
  (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (j : Fin C → ℕ)
  (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
  (R : Fin C → MvPolynomial (Fin 4) ℝ) (Ti s₀ K : ℕ)

/-- Every assigned line belongs to an entry on each sub-block. -/
theorem exists_memE {a : Fin n} {jj : Fin (2 ^ s₀)} {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ A' a)
    (hz : ‖zc (Q (old a)) (c (old a)) (u (old a)) l
      (subMid Ti s₀ (j (old a)) jj)‖ ≤ K * side s₀) :
    ∃ e : Entry n s₀ K, e.1 = a ∧ e.2.1 = jj ∧
      l ∈ memE old R' A' j c u Q R Ti s₀ K e := by
  classical
  obtain ⟨k, hk⟩ := exists_boxOf_eq_boxIdx hz
  let tm := subMid Ti s₀ (j (old a)) jj
  refine ⟨(a, jj, k, decide (0 ≤ eval (gx l tm) (pderiv 3 (R' a))),
    decide (0 ≤ eval (gx l tm) (pderiv 3 (R (old a))))), rfl, rfl, hl, ?_, rfl, rfl⟩
  exact hk.symm

/-- The candidate and sub-block determine a unique entry for any of their lines. -/
theorem memE_eq_of_mem {e e' : Entry n s₀ K} {l : ℕ × (Fin 6 → ℝ)}
    (ha : e.1 = e'.1) (hjj : e.2.1 = e'.2.1)
    (hl : l ∈ memE old R' A' j c u Q R Ti s₀ K e)
    (hl' : l ∈ memE old R' A' j c u Q R Ti s₀ K e') : e = e' := by
  by_contra hne
  exact Set.disjoint_left.mp (memE_disjoint_of_ne old R' A' j c u Q R Ti s₀ K ha hjj hne) hl hl'


/-- Disjoint candidate assignments give disjoint entries at the same refined time block. -/
theorem memE_disjoint_same_block {W : ℕ} (γ : Fin C → Fin W)
    (hdisj : ∀ a a', a ≠ a' → γ (old a) = γ (old a') → j (old a) = j (old a') →
      Disjoint (A' a) (A' a')) {e e' : Entry n s₀ K} (hne : e ≠ e')
    (hγ : γ (old e.1) = γ (old e'.1))
    (hblock : subIdx s₀ (j (old e.1)) e.2.1 = subIdx s₀ (j (old e'.1)) e'.2.1) :
    Disjoint (memE old R' A' j c u Q R Ti s₀ K e)
      (memE old R' A' j c u Q R Ti s₀ K e') := by
  obtain ⟨hj, hjj⟩ := subIdx_inj e.2.1.isLt e'.2.1.isLt hblock
  by_cases ha : e.1 = e'.1
  · exact memE_disjoint_of_ne old R' A' j c u Q R Ti s₀ K ha (Fin.ext hjj) hne
  · exact (hdisj e.1 e'.1 ha hγ hj).mono (fun _ h => h.1) (fun _ h => h.1)

end Members

/-- Exact size of the finite entry table, including both derivative signs. -/
theorem card_Entry (n s₀ K : ℕ) :
    Fintype.card (Entry n s₀ K) = n * 2 ^ s₀ * (2 * K + 2) ^ 2 * 4 := by
  simp only [Entry, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool]
  ring

/-- A packet's entries cost only its own candidate count times the fixed geometric table. -/
theorem card_Entry_packet {n C s₀ K : ℕ} (old : Fin n → Fin C) (b : Fin C) :
    ((Finset.univ.filter (fun e : Entry n s₀ K => old e.1 = b)).card) =
      (Finset.univ.filter (fun a : Fin n => old a = b)).card *
        2 ^ s₀ * (2 * K + 2) ^ 2 * 4 := by
  classical
  have heq : (Finset.univ.filter (fun e : Entry n s₀ K => old e.1 = b)) =
      (Finset.univ.filter (fun a : Fin n => old a = b)) ×ˢ
        (Finset.univ : Finset (Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool × Bool)) := by
    ext e
    simp
  rw [heq, Finset.card_product, Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
  ring

private theorem exists_fin_cell {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) n) :
    ∃ j : Fin n, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 := by
  by_cases hlast : t = n
  · refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
    · simpa only [hlast, Nat.cast_le] using Nat.sub_le n 1
    · have h : n - 1 + 1 = n := by omega
      change t ≤ ((n - 1 : ℕ) : ℝ) + 1
      have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast h
      rw [hc]
      exact ht.2
  · have hlt : t < n := lt_of_le_of_ne ht.2 hlast
    refine ⟨⟨⌊t⌋₊, (Nat.floor_lt ht.1).mpr hlt⟩, Nat.floor_le ht.1, ?_⟩
    exact (Nat.lt_floor_add_one t).le

/-- The closed dyadic sub-blocks cover the entire original closed block. -/
theorem exists_subBlock {Ti s₀ j₀ : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((j₀ : ℝ) / (2 : ℝ) ^ Ti)
      (((j₀ : ℝ) + 1) / (2 : ℝ) ^ Ti)) :
    ∃ jj : Fin (2 ^ s₀), t ∈ subBlock Ti s₀ j₀ jj := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ Ti := by positivity
  have hq : (0 : ℝ) < (2 : ℝ) ^ s₀ := by positivity
  let τ := (t * (2 : ℝ) ^ Ti - j₀) * (2 : ℝ) ^ s₀
  have hτ : τ ∈ Set.Icc (0 : ℝ) (2 ^ s₀ : ℕ) := by
    have hlow := (div_le_iff₀ hp).mp ht.1
    have hhigh := (le_div_iff₀ hp).mp ht.2
    push_cast
    dsimp only [τ]
    constructor <;> nlinarith
  obtain ⟨jj, hjlo, hjhi⟩ := exists_fin_cell (by positivity : 0 < 2 ^ s₀) hτ
  refine ⟨jj, ?_, ?_⟩
  · change (subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (Ti + s₀) ≤ t
    rw [div_le_iff₀ (by positivity), pow_add]
    dsimp only [τ] at hjlo
    unfold subIdx
    push_cast
    nlinarith
  · change t ≤ ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)
    rw [le_div_iff₀ (by positivity), pow_add]
    dsimp only [τ] at hjhi
    unfold subIdx
    push_cast
    nlinarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
