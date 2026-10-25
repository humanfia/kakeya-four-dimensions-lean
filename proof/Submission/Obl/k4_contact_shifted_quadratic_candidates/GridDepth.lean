import Mathlib

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

noncomputable section

/-- A finite original-depth grid, kept constant beyond its final level. -/
def finiteGridDepth (s₀ U' : ℝ) (m h : ℕ) : ℝ :=
  s₀ + (min h m : ℕ) * (U' / m)

theorem finiteGridDepth_zero (s₀ U' : ℝ) (m : ℕ) : finiteGridDepth s₀ U' m 0 = s₀ := by
  simp [finiteGridDepth]

theorem finiteGridDepth_of_le (s₀ U' : ℝ) {m h : ℕ} (hh : h ≤ m) :
    finiteGridDepth s₀ U' m h = s₀ + (h : ℝ) * (U' / m) := by
  simp only [finiteGridDepth, Nat.min_eq_left hh]

theorem finiteGridDepth_bounds {s₀ U' : ℝ} {m : ℕ} (hU' : 0 ≤ U') (hm : 1 ≤ m)
    (h : ℕ) : s₀ ≤ finiteGridDepth s₀ U' m h ∧ finiteGridDepth s₀ U' m h ≤ s₀ + U' := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hη : 0 ≤ U' / m := div_nonneg hU' hmpos.le
  have hmin : ((min h m : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.min_le_right h m
  unfold finiteGridDepth
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hη)
  · have hh := mul_le_mul_of_nonneg_right hmin hη
    have heq : (m : ℝ) * (U' / m) = U' := by field_simp
    rw [heq] at hh
    linarith

theorem finiteGridDepth_succ_lt {s₀ U' : ℝ} {m h : ℕ} (hU' : 0 < U') (hh : h < m) :
    finiteGridDepth s₀ U' m h < finiteGridDepth s₀ U' m (h + 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le h |>.trans_lt hh)
  rw [finiteGridDepth_of_le s₀ U' hh.le, finiteGridDepth_of_le s₀ U' (by omega)]
  push_cast
  have hη : 0 < U' / m := div_pos hU' hmpos
  nlinarith

theorem finiteGridDepth_succ_eq {s₀ U' : ℝ} {m h : ℕ} (hh : m ≤ h) :
    finiteGridDepth s₀ U' m (h + 1) = finiteGridDepth s₀ U' m h := by
  simp only [finiteGridDepth, Nat.min_eq_right hh, Nat.min_eq_right (by omega : m ≤ h + 1)]

/-- Finite-index palettes extend to every natural level without transports:
the extra levels repeat the final original depth. -/
theorem finiteGridDepth_capIndex (s₀ U' : ℝ) (m h : ℕ) :
    s₀ + (((⟨min h m, by omega⟩ : Fin (m + 1)) : ℕ) : ℝ) * (U' / m) =
      finiteGridDepth s₀ U' m h := rfl


/-- Frozen nesting on the prepared original depth range supplies all natural
ancestor maps of the capped grid. Beyond the final grid depth the map is the
identity, so no assumptions outside that range are needed. -/
theorem exists_finiteGrid_ancestors {α : Type*}
    (n : ℝ → ℕ) (A : (s : ℝ) → Fin (n s) → Set α)
    (J : (s : ℝ) → Fin (n s) → Set ℝ)
    {s₀ U' : ℝ} {m : ℕ} (hU' : 0 < U') (hm : 1 ≤ m)
    (hnest : ∀ s t : ℝ, s₀ ≤ s → s < t → t ≤ s₀ + U' →
      ∀ i : Fin (n t), ∃ a : Fin (n s), A t i ⊆ A s a ∧ J t i ⊆ J s a) :
    ∃ anc : (h : ℕ) → Fin (n (finiteGridDepth s₀ U' m (h + 1))) →
      Fin (n (finiteGridDepth s₀ U' m h)),
      ∀ h i, A (finiteGridDepth s₀ U' m (h + 1)) i ⊆
        A (finiteGridDepth s₀ U' m h) (anc h i) ∧
        J (finiteGridDepth s₀ U' m (h + 1)) i ⊆ J (finiteGridDepth s₀ U' m h) (anc h i) := by
  classical
  have hall (h : ℕ) : ∀ i : Fin (n (finiteGridDepth s₀ U' m (h + 1))),
      ∃ a : Fin (n (finiteGridDepth s₀ U' m h)),
        A (finiteGridDepth s₀ U' m (h + 1)) i ⊆ A (finiteGridDepth s₀ U' m h) a ∧
        J (finiteGridDepth s₀ U' m (h + 1)) i ⊆ J (finiteGridDepth s₀ U' m h) a := by
    by_cases hh : h < m
    · exact hnest _ _ (finiteGridDepth_bounds hU'.le hm h).1
        (finiteGridDepth_succ_lt hU' hh) (finiteGridDepth_bounds hU'.le hm (h + 1)).2
    · have heq := finiteGridDepth_succ_eq (s₀ := s₀) (U' := U') (Nat.le_of_not_gt hh)
      rw [heq]
      intro i
      exact ⟨i, Set.Subset.rfl, Set.Subset.rfl⟩
  choose anc hanc using hall
  exact ⟨anc, hanc⟩

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
