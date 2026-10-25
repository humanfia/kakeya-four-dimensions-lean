/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/StateReadout.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.AppendedScore

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

/-- A record predicted by another record has zero conditional entropy
under the original finite law. -/
theorem entropy_eq_zero_of_predicted (p : α → ℝ) (E Y : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hpred : ∀ x y, E x = E y → Y x = Y y) :
    entropy p E Y = 0 := by
  classical
  unfold entropy
  rw [Finset.sum_eq_zero, neg_zero]
  intro x _
  by_cases hx : p x = 0
  · rw [hx, zero_mul]
  · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    have hmass : colorMass p E Y (E x) (Y x) = fiberMass p E (E x) := by
      unfold colorMass fiberMass
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.left, fun he => ⟨he, hpred y x he⟩⟩
    have hpos : 0 < fiberMass p E (E x) := hpx.trans_le
      ((self_le_colorMass p E Y hp x).trans (colorMass_le_fiberMass p E Y hp _ _))
    rw [posterior, hmass, div_self hpos.ne', Real.log_one, mul_zero]

/-- Discarding part of a fine state costs at most one in the positive
information score, with every posterior still from the original law. -/
theorem state_readout_score_le (p : α → ℝ) (F E Y Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hEF : ∀ x y, E x = E y → F x = F y)
    (hYF : ∀ x y, Y x = Y y → F x = F y)
    (hEY : ∀ x y, E x = E y → Y x = Y y) :
    positiveScore p F Y Z ≤ positiveScore p F E Z + 1 := by
  have hZF : ∀ x y, pairedRecord F Z x = pairedRecord F Z y → F x = F y :=
    fun _ _ h => (Nat.pair_eq_pair.mp h).1
  have hpred : ∀ x y, pairedRecord F E x = pairedRecord F E y → Y x = Y y :=
    fun x y h => hEY x y (Nat.pair_eq_pair.mp h).2
  calc
    _ = positiveScore p F (pairedRecord F Z) Y := positiveScore_symmetry p F Y Z hp hYF
    _ ≤ positiveScore p F (pairedRecord F Z) E + entropy p (pairedRecord F E) Y + 1 :=
      palette_change_score_le p F (pairedRecord F Z) Y E hp hp1 hZF
    _ = positiveScore p F E Z + 1 := by
      rw [entropy_eq_zero_of_predicted p _ Y hp hpred,
        ← positiveScore_symmetry p F E Z hp hEF, add_zero]

/-- Grid cells may be any readout of the rich history and appended
point-state record used to choose the original information window. -/
theorem exists_low_information_readout_window
    (n L C M Kv Ks : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ)
    (Z : Fin n → ℕ) (V A Y : ℕ → Fin n → ℕ)
    (hL : 0 < L) (hC : 1 ≤ C) (hM : 1 ≤ M) (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter (fun y =>
      0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M)
    (hv : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      pairedRecord (F a) Z y = pairedRecord (F a) Z x)).image (V a)).card ≤ Kv)
    (hs : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      F (a + C) y = F (a + C) x)).image (A a)).card ≤ Ks)
    (hY : ∀ a < L, ∀ x y, pairedRecord (F (a + C)) (A a) x =
      pairedRecord (F (a + C)) (A a) y → Y a x = Y a y) :
    ∃ a : ℕ, a < L ∧ positiveScore p (F a) (pairedRecord (F a) (Y a)) (V a) ≤
      (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 4 := by
  obtain ⟨a, ha, hscore⟩ := exists_low_information_extended_window
    n L C M Kv Ks p F Z V A hL hC hM hKv hKs hp hp1 hnest hsupp hv hs
  have hEF : ∀ x y, pairedRecord (F (a + C)) (A a) x =
      pairedRecord (F (a + C)) (A a) y → F a x = F a y := by
    intro x y h
    exact nested_record F hnest a (a + C) (Nat.le_add_right a C) x y
      (Nat.pair_eq_pair.mp h).1
  have hYF : ∀ x y, pairedRecord (F a) (Y a) x =
      pairedRecord (F a) (Y a) y → F a x = F a y :=
    fun _ _ h => (Nat.pair_eq_pair.mp h).1
  have hEY : ∀ x y, pairedRecord (F (a + C)) (A a) x =
      pairedRecord (F (a + C)) (A a) y →
      pairedRecord (F a) (Y a) x = pairedRecord (F a) (Y a) y :=
    fun x y h => Nat.pair_eq_pair.mpr ⟨hEF x y h, hY a ha x y h⟩
  have hread := state_readout_score_le p (F a) (pairedRecord (F (a + C)) (A a))
    (pairedRecord (F a) (Y a)) (V a) hp hp1 hEF hYF hEY
  exact ⟨a, ha, by linarith⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
