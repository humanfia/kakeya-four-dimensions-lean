-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Tower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Compose the parent assignments between two levels. -/
def ancestor {N : ℕ → ℕ} (f : ∀ j, Fin (N (j + 1)) → Fin (N j))
    {j k : ℕ} (h : j ≤ k) : Fin (N k) → Fin (N j) :=
  Nat.leRecOn (C := fun k => Fin (N k) → Fin (N j)) h
    (fun {k} a => a ∘ f k) id

lemma ancestor_self {N : ℕ → ℕ} (f : ∀ j, Fin (N (j + 1)) → Fin (N j))
    (j : ℕ) (i : Fin (N j)) : ancestor f (Nat.le_refl j) i = i := by
  simp [ancestor, Nat.leRecOn_self]

lemma ancestor_succ {N : ℕ → ℕ} (f : ∀ j, Fin (N (j + 1)) → Fin (N j))
    {j k : ℕ} (h : j ≤ k) (i : Fin (N (k + 1))) :
    ancestor f (Nat.le_succ_of_le h) i = ancestor f h (f k i) := by
  rw [ancestor, Nat.leRecOn_succ h]
  rfl

lemma ancestor_comp {N : ℕ → ℕ} (f : ∀ j, Fin (N (j + 1)) → Fin (N j))
    {j k l : ℕ} (hjk : j ≤ k) (hkl : k ≤ l) (i : Fin (N l)) :
    ancestor f hjk (ancestor f hkl i) = ancestor f (hjk.trans hkl) i := by
  induction l, hkl using Nat.le_induction with
  | base => simp [ancestor_self]
  | succ l hkl ih =>
      rw [ancestor_succ f hkl, ancestor_succ f (hjk.trans hkl)]
      exact ih (f l i)

lemma ancestor_containment {X : Type*} {N : ℕ → ℕ}
    (f : ∀ j, Fin (N (j + 1)) → Fin (N j))
    (U : ∀ j, Fin (N j) → Set X) (J : ℕ)
    (hU : ∀ j, j < J → ∀ i, U (j + 1) i ⊆ U j (f j i))
    {j k : ℕ} (hjk : j ≤ k) (hkJ : k ≤ J) (i : Fin (N k)) :
    U k i ⊆ U j (ancestor f hjk i) := by
  induction k, hjk using Nat.le_induction with
  | base => simp [ancestor_self]
  | succ k hjk ih =>
      rw [ancestor_succ f hjk]
      exact (hU k (by omega) i).trans (ih (by omega) (f k i))

/-- Pick a tower radius just above the requested radius. -/
theorem select_radius (r : ℕ → ℝ) (J : ℕ) (d g ε ρ₀ : ℝ)
    (hd : 0 < d) (hd1 : d < 1) (hg : 0 ≤ g) (hgε : g < ε)
    (hr0 : r 0 = 1) (hrJ : r J = d)
    (hgap : ∀ j, j < J → d ^ g * r j ≤ r (j + 1))
    (hρd : d ≤ ρ₀) (hρ1 : ρ₀ ≤ 1) :
    ∃ j : ℕ, j ≤ J ∧ ρ₀ ≤ r j ∧ r j < d ^ (-ε) * ρ₀ := by
  classical
  let S := (Finset.range (J + 1)).filter fun j => ρ₀ ≤ r j
  have h0 : 0 ∈ S := by simp [S, hr0, hρ1]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun j => j) ⟨0, h0⟩
  obtain ⟨hjrange, hρj⟩ := Finset.mem_filter.mp hj
  have hjJ : j ≤ J := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjrange
  have hρpos : 0 < ρ₀ := hd.trans_le hρd
  have hpow : 0 < d ^ (-g) := Real.rpow_pos_of_pos hd _
  have hinv : d ^ (-g) * d ^ g = 1 := by
    rw [← Real.rpow_add hd, neg_add_cancel, Real.rpow_zero]
  have hle : r j ≤ d ^ (-g) * ρ₀ := by
    by_cases he : j = J
    · have h1 : 1 ≤ d ^ (-g) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hd hd1.le (neg_nonpos.mpr hg)
      calc
        r j = d := he ▸ hrJ
        _ ≤ ρ₀ := hρd
        _ ≤ d ^ (-g) * ρ₀ := by nlinarith
    · have hjlt : j < J := lt_of_le_of_ne hjJ he
      have hnext : r (j + 1) < ρ₀ := by
        by_contra hn
        have hmem : j + 1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, le_of_not_gt hn⟩
        have := hmax (j + 1) hmem
        omega
      have h := mul_le_mul_of_nonneg_left ((hgap j hjlt).trans hnext.le) hpow.le
      simpa only [← mul_assoc, hinv, one_mul] using h
  refine ⟨j, hjJ, hρj, hle.trans_lt ?_⟩
  exact mul_lt_mul_of_pos_right
    (Real.rpow_lt_rpow_of_exponent_gt hd hd1 (neg_lt_neg hgε)) hρpos

end WangZahlLot.Obl.wz_tower_balanced_refinement
