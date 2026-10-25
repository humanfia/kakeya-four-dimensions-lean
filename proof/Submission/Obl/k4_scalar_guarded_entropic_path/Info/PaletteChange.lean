/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/PaletteChange.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.EntropyWindow
import Submission.Obl.k4_matching_palette_likelihood.Entropy

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

/-- A finite joint record, without changing the reference probability. -/
def pairedRecord (F Z : α → ℕ) (x : α) : ℕ := Nat.pair (F x) (Z x)

theorem fiberMass_pairedRecord (p : α → ℝ) (F Z : α → ℕ) (x : α) :
    fiberMass p (pairedRecord F Z) (pairedRecord F Z x) =
      colorMass p F Z (F x) (Z x) := by
  simp only [fiberMass, colorMass, pairedRecord, Nat.pair_eq_pair]

theorem colorMass_pairedRecord_swap (p : α → ℝ) (F Y Z : α → ℕ) (x : α) :
    colorMass p (pairedRecord F Y) Z (pairedRecord F Y x) (Z x) =
      colorMass p (pairedRecord F Z) Y (pairedRecord F Z x) (Y x) := by
  unfold colorMass
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord, Nat.pair_eq_pair]
  tauto

theorem posterior_pair_swap (p : α → ℝ) (F Y Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) {x : α} (hpx : 0 < p x) :
    posterior p F Y x * posterior p (pairedRecord F Y) Z x =
      posterior p F Z x * posterior p (pairedRecord F Z) Y x := by
  have hFY : 0 < colorMass p F Y (F x) (Y x) := hpx.trans_le (self_le_colorMass p F Y hp x)
  have hFZ : 0 < colorMass p F Z (F x) (Z x) := hpx.trans_le (self_le_colorMass p F Z hp x)
  have hF : 0 < fiberMass p F (F x) := hFY.trans_le (colorMass_le_fiberMass p F Y hp _ _)
  simp only [posterior, fiberMass_pairedRecord]
  rw [colorMass_pairedRecord_swap]
  field_simp [hFY.ne', hFZ.ne', hF.ne']

/-- A palette change costs only its ambiguity given the old palette and
parent record, plus one reverse-likelihood term whose expectation is
bounded by one. All likelihoods are from the unchanged reference law. -/
theorem palette_change_score_point (p : α → ℝ) (F E Y Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) {x : α} (hpx : 0 < p x) :
    max 0 (Real.log (posterior p E Y x / posterior p F Y x)) ≤
      max 0 (Real.log (posterior p E Z x / posterior p F Z x)) -
        Real.log (posterior p (pairedRecord F Z) Y x) +
        posterior p (pairedRecord F Y) Z x / posterior p (pairedRecord E Y) Z x := by
  have hpos (f W : α → ℕ) : 0 < posterior p f W x := posterior_pos p f W hp x hpx
  have hlogF := congrArg Real.log (posterior_pair_swap p F Y Z hp hpx)
  have hlogE := congrArg Real.log (posterior_pair_swap p E Y Z hp hpx)
  rw [Real.log_mul (hpos F Y).ne' (hpos (pairedRecord F Y) Z).ne',
    Real.log_mul (hpos F Z).ne' (hpos (pairedRecord F Z) Y).ne'] at hlogF
  rw [Real.log_mul (hpos E Y).ne' (hpos (pairedRecord E Y) Z).ne',
    Real.log_mul (hpos E Z).ne' (hpos (pairedRecord E Z) Y).ne'] at hlogE
  have hcondF : Real.log (posterior p (pairedRecord F Z) Y x) ≤ 0 :=
    Real.log_nonpos (posterior_nonneg p _ _ hp x) (posterior_le_one p _ _ hp x)
  have hcondE : Real.log (posterior p (pairedRecord E Z) Y x) ≤ 0 :=
    Real.log_nonpos (posterior_nonneg p _ _ hp x) (posterior_le_one p _ _ hp x)
  have hratioPos : 0 < posterior p (pairedRecord F Y) Z x /
      posterior p (pairedRecord E Y) Z x := div_pos (hpos _ _) (hpos _ _)
  have hratio := Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_div (hpos (pairedRecord F Y) Z).ne'
    (hpos (pairedRecord E Y) Z).ne'] at hratio
  rw [Real.log_div (hpos E Y).ne' (hpos F Y).ne',
    Real.log_div (hpos E Z).ne' (hpos F Z).ne']
  apply max_le
  · have hmax := le_max_left 0 (Real.log (posterior p E Z x) - Real.log (posterior p F Z x))
    linarith
  · have hmax := le_max_right 0 (Real.log (posterior p E Z x) - Real.log (posterior p F Z x))
    linarith

/-- The expected positive information score changes by at most the old
conditional palette entropy and one absolute constant. -/
theorem palette_change_score_le (p : α → ℝ) (F E Y Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ x y, E x = E y → F x = F y) :
    (∑ x, p x * max 0 (Real.log (posterior p E Y x / posterior p F Y x))) ≤
      (∑ x, p x * max 0 (Real.log (posterior p E Z x / posterior p F Z x))) +
        entropy p (pairedRecord F Z) Y + 1 := by
  have hpoint (x : α) :
      p x * max 0 (Real.log (posterior p E Y x / posterior p F Y x)) ≤
        p x * max 0 (Real.log (posterior p E Z x / posterior p F Z x)) -
          p x * Real.log (posterior p (pairedRecord F Z) Y x) +
          p x * (posterior p (pairedRecord F Y) Z x / posterior p (pairedRecord E Y) Z x) := by
    by_cases hx : p x = 0
    · simp only [hx, zero_mul, sub_zero, add_zero, le_refl]
    · have hb := mul_le_mul_of_nonneg_left
        (palette_change_score_point p F E Y Z hp (lt_of_le_of_ne (hp x) (Ne.symm hx))) (hp x)
      simpa only [mul_add, mul_sub] using hb
  have hnest' : ∀ x y, pairedRecord E Y x = pairedRecord E Y y →
      pairedRecord F Y x = pairedRecord F Y y := by
    intro x y hxy
    have heq := Nat.pair_eq_pair.mp hxy
    exact Nat.pair_eq_pair.mpr ⟨hnest x y heq.1, heq.2⟩
  have hratio := expected_ratio_le p (pairedRecord F Y) (pairedRecord E Y) Z hp hnest'
  rw [hp1] at hratio
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  unfold entropy
  linarith

theorem palette_change_score_le_log_card {n K : ℕ}
    (p : Fin n → ℝ) (F E Y Z : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hK : 1 ≤ K)
    (hnest : ∀ x y, E x = E y → F x = F y)
    (hamb : ∀ x, ((Finset.univ.filter (fun y =>
      0 < p y ∧ pairedRecord F Z y = pairedRecord F Z x)).image Y).card ≤ K) :
    (∑ x, p x * max 0 (Real.log (posterior p E Y x / posterior p F Y x))) ≤
      (∑ x, p x * max 0 (Real.log (posterior p E Z x / posterior p F Z x))) +
        Real.log (K : ℝ) + 1 := by
  have hcard := neg_log_card_le_log_likelihood p (pairedRecord F Z) Y hK hp hp1 hamb
  have hentropy : entropy p (pairedRecord F Z) Y ≤ Real.log (K : ℝ) := by
    change -Real.log (K : ℝ) ≤ ∑ x, p x *
      Real.log (posterior p (pairedRecord F Z) Y x) at hcard
    unfold entropy
    linarith
  exact (palette_change_score_le p F E Y Z hp hp1 hnest).trans (by linarith)

/-- A normalized velocity palette may vary with the potential parent
window. Bounded ambiguity relative to one common original palette adds
only its logarithm to the selected window's information budget. -/
theorem exists_low_information_changed_palette_window
    (n L C M K : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ)
    (Z : Fin n → ℕ) (Y : ℕ → Fin n → ℕ)
    (hL : 0 < L) (hC : 1 ≤ C) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter
      (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M)
    (hamb : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y =>
      0 < p y ∧ pairedRecord (F a) Z y = pairedRecord (F a) Z x)).image (Y a)).card ≤ K) :
    ∃ a : ℕ, a < L ∧
      (∑ x, p x * max 0 (Real.log
        (posterior p (F (a + C)) (Y a) x / posterior p (F a) (Y a) x))) ≤
          (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + Real.log (K : ℝ) + 2 := by
  obtain ⟨a, ha, hscore⟩ := exists_low_information_window n L C M p F Z
    hL hC hM hp hp1 hnest hsupp
  have hnest' : ∀ x y, F (a + C) x = F (a + C) y → F a x = F a y :=
    fun x y hxy => nested_record F hnest a (a + C) (Nat.le_add_right a C) x y hxy
  refine ⟨a, ha, ?_⟩
  have hchange := palette_change_score_le_log_card p (F a) (F (a + C)) (Y a) Z
    hp hp1 hK hnest' (hamb a ha)
  linarith

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
