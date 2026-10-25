import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

/-- The last band has no lower bound and includes zero gaps. -/
def Band (N δ b x : ℝ) : Prop :=
  x ≤ N ^ (-b + δ) ∧ (b < 2 → N ^ (-b - δ) ≤ x)

noncomputable def binExponent (m : ℕ) (b : Fin (2 * m + 1)) : ℝ := (b.val : ℝ) / (m : ℝ)

lemma binExponent_mem {m : ℕ} (hm : 0 < m) (b : Fin (2 * m + 1)) :
    0 ≤ binExponent m b ∧ binExponent m b ≤ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hm'.le
  · dsimp [binExponent]
    apply (div_le_iff₀ hm').2
    exact_mod_cast (show b.val ≤ 2 * m by omega)

/-- A bounded nonnegative gap has a power band; any gap above the first
threshold can be placed in band zero. -/
lemma exists_bin {m : ℕ} (hm : 0 < m) {N x : ℝ} (hN : 1 ≤ N)
    (hx : x ≤ N ^ (1 / (m : ℝ))) :
    ∃ b : Fin (2 * m + 1), Band N (1 / (m : ℝ)) (binExponent m b) x ∧
      (N ^ (-(1 / (m : ℝ))) ≤ x → b = 0) := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hlarge : N ^ (-(1 / (m : ℝ))) ≤ x
  · refine ⟨0, ?_, fun _ => rfl⟩
    simpa [Band, binExponent] using And.intro hx (fun (_ : (0 : ℝ) < 2) => hlarge)
  let s : Finset (Fin (2 * m + 1)) :=
    Finset.univ.filter fun b => x ≤ N ^ (-binExponent m b + 1 / (m : ℝ))
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [s, binExponent] using hx
  let b := s.max' hs
  have hb : b ∈ s := Finset.max'_mem s hs
  have hbupper : x ≤ N ^ (-binExponent m b + 1 / (m : ℝ)) :=
    (Finset.mem_filter.1 hb).2
  refine ⟨b, ⟨hbupper, ?_⟩, fun h => False.elim (hlarge h)⟩
  intro hbsmall
  have hbval : b.val < 2 * m := by
    have h : (b.val : ℝ) < 2 * (m : ℝ) := (div_lt_iff₀ hm').1 hbsmall
    exact_mod_cast h
  let c : Fin (2 * m + 1) := ⟨b.val + 1, by omega⟩
  have hnot : ¬ x ≤ N ^ (-binExponent m c + 1 / (m : ℝ)) := by
    intro hc
    have hcmem : c ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩
    have hcb : c ≤ b := Finset.le_max' s c hcmem
    have : c.val ≤ b.val := hcb
    dsimp [c] at this
    omega
  have heq : -binExponent m c + 1 / (m : ℝ) = -binExponent m b := by
    dsimp [binExponent, c]
    push_cast
    ring
  rw [heq] at hnot
  have hexp : -binExponent m b - 1 / (m : ℝ) ≤ -binExponent m b := by
    have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hN hexp).trans (not_le.1 hnot).le

end Submission.Obl.k4_matching_gap_regularization
