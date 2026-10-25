/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/AppendedScore.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PaletteChange

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

def positiveScore (p : α → ℝ) (F E Z : α → ℕ) : ℝ :=
  ∑ x, p x * max 0 (Real.log (posterior p E Z x / posterior p F Z x))

theorem colorMass_parent_fine (p : α → ℝ) (F E : α → ℕ)
    (hnest : ∀ x y, E x = E y → F x = F y) (x : α) :
    colorMass p F E (F x) (E x) = fiberMass p E (E x) := by
  classical
  unfold colorMass fiberMass
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hnest y x h, h⟩⟩

theorem colorMass_paired_parent_fine (p : α → ℝ) (F E Z : α → ℕ)
    (hnest : ∀ x y, E x = E y → F x = F y) (x : α) :
    colorMass p (pairedRecord F Z) E (pairedRecord F Z x) (E x) =
      colorMass p E Z (E x) (Z x) := by
  classical
  unfold colorMass
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord, Nat.pair_eq_pair]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hnest y x h.1, h.2⟩, h.1⟩⟩

theorem posterior_ratio_symmetry (p : α → ℝ) (F E Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hnest : ∀ x y, E x = E y → F x = F y)
    {x : α} (hpx : 0 < p x) :
    posterior p E Z x / posterior p F Z x =
      posterior p (pairedRecord F Z) E x / posterior p F E x := by
  have hF : 0 < fiberMass p F (F x) := hpx.trans_le
    ((self_le_colorMass p F Z hp x).trans (colorMass_le_fiberMass p F Z hp _ _))
  have hE : 0 < fiberMass p E (E x) := hpx.trans_le
    ((self_le_colorMass p E Z hp x).trans (colorMass_le_fiberMass p E Z hp _ _))
  have hFZ : 0 < colorMass p F Z (F x) (Z x) := hpx.trans_le (self_le_colorMass p F Z hp x)
  unfold posterior
  rw [colorMass_paired_parent_fine p F E Z hnest, fiberMass_pairedRecord,
    colorMass_parent_fine p F E hnest]
  field_simp [hF.ne', hE.ne', hFZ.ne']

/-- Conditional positive information is symmetric after retaining the
parent record in the exchanged velocity record. Zero atoms cost nothing. -/
theorem positiveScore_symmetry (p : α → ℝ) (F E Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hnest : ∀ x y, E x = E y → F x = F y) :
    positiveScore p F E Z = positiveScore p F (pairedRecord F Z) E := by
  unfold positiveScore
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, zero_mul]
  · rw [posterior_ratio_symmetry p F E Z hp hnest (lt_of_le_of_ne (hp x) (Ne.symm hx))]

/-- Appending point-state information costs its original conditional
entropy, plus one absolute reverse-likelihood term. -/
theorem appended_state_score_le_entropy (p : α → ℝ) (F E A Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ x y, E x = E y → F x = F y) :
    positiveScore p F (pairedRecord E A) Z ≤ positiveScore p F E Z +
      entropy p (pairedRecord F E) (pairedRecord E A) + 1 := by
  have hnestA : ∀ x y, pairedRecord E A x = pairedRecord E A y → F x = F y :=
    fun x y h => hnest x y (Nat.pair_eq_pair.mp h).1
  have hnestZ : ∀ x y, pairedRecord F Z x = pairedRecord F Z y → F x = F y :=
    fun _ _ h => (Nat.pair_eq_pair.mp h).1
  calc
    _ = positiveScore p F (pairedRecord F Z) (pairedRecord E A) :=
      positiveScore_symmetry p F (pairedRecord E A) Z hp hnestA
    _ ≤ positiveScore p F (pairedRecord F Z) E +
        entropy p (pairedRecord F E) (pairedRecord E A) + 1 :=
      palette_change_score_le p F (pairedRecord F Z) (pairedRecord E A) E hp hp1 hnestZ
    _ = _ := by rw [← positiveScore_symmetry p F E Z hp hnest]

theorem appended_state_entropy_le_log_card {n K : ℕ}
    (p : Fin n → ℝ) (F E A : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hK : 1 ≤ K)
    (hamb : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ E y = E x)).image A).card ≤ K) :
    entropy p (pairedRecord F E) (pairedRecord E A) ≤ Real.log (K : ℝ) := by
  classical
  have hamb' (x : Fin n) : ((Finset.univ.filter (fun y =>
      0 < p y ∧ pairedRecord F E y = pairedRecord F E x)).image (pairedRecord E A)).card ≤ K := by
    let s := Finset.univ.filter (fun y => 0 < p y ∧ E y = E x)
    have hsub : Finset.univ.filter (fun y => 0 < p y ∧
        pairedRecord F E y = pairedRecord F E x) ⊆ s := by
      intro y hy
      obtain ⟨hy₀, hy₁⟩ := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy₀, (Nat.pair_eq_pair.mp hy₁).2⟩
    calc
      _ ≤ (s.image (pairedRecord E A)).card :=
        Finset.card_le_card (Finset.image_subset_image hsub)
      _ = ((s.image A).image (fun a => Nat.pair (E x) a)).card := by
        rw [Finset.image_image]
        congr 1
        apply Finset.image_congr
        intro y hy
        dsimp only [pairedRecord, Function.comp_apply]
        rw [(Finset.mem_filter.mp hy).2.2]
      _ ≤ (s.image A).card := Finset.card_image_le
      _ ≤ K := hamb x
  have hc := neg_log_card_le_log_likelihood p (pairedRecord F E) (pairedRecord E A) hK hp hp1 hamb'
  change -Real.log (K : ℝ) ≤ ∑ x, p x * Real.log (posterior p (pairedRecord F E) (pairedRecord E A) x) at hc
  unfold entropy
  linarith

theorem appended_state_score_le_log_card {n K : ℕ}
    (p : Fin n → ℝ) (F E A Z : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hK : 1 ≤ K)
    (hnest : ∀ x y, E x = E y → F x = F y)
    (hamb : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ E y = E x)).image A).card ≤ K) :
    positiveScore p F (pairedRecord E A) Z ≤
      positiveScore p F E Z + Real.log (K : ℝ) + 1 := by
  have h := appended_state_entropy_le_log_card p F E A hp hp1 hK hamb
  exact (appended_state_score_le_entropy p F E A Z hp hp1 hnest).trans (by linarith)

/-- One original probability chooses the history window, while both its
normalized velocity palette and its appended point-state record may vary
with the potential parent. The two ambiguities pay only their logarithms. -/
theorem exists_low_information_extended_window
    (n L C M Kv Ks : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ)
    (Z : Fin n → ℕ) (V A : ℕ → Fin n → ℕ)
    (hL : 0 < L) (hC : 1 ≤ C) (hM : 1 ≤ M) (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M)
    (hv : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      pairedRecord (F a) Z y = pairedRecord (F a) Z x)).image (V a)).card ≤ Kv)
    (hs : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      F (a + C) y = F (a + C) x)).image (A a)).card ≤ Ks) :
    ∃ a : ℕ, a < L ∧ positiveScore p (F a) (pairedRecord (F (a + C)) (A a)) (V a) ≤
      (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 3 := by
  obtain ⟨a, ha, hscore⟩ := exists_low_information_changed_palette_window
    n L C M Kv p F Z V hL hC hM hKv hp hp1 hnest hsupp hv
  have hn : ∀ x y, F (a + C) x = F (a + C) y → F a x = F a y :=
    fun x y h => nested_record F hnest a (a + C) (Nat.le_add_right a C) x y h
  have happ := appended_state_score_le_log_card p (F a) (F (a + C)) (A a) (V a)
    hp hp1 hKs hn (hs a ha)
  change positiveScore p (F a) (F (a + C)) (V a) ≤ _ at hscore
  exact ⟨a, ha, by linarith⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
