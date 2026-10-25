-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowColor.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowColor.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, WindowColor.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketWindowFilling

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- Keep one complete axial colour, without cutting any retained row further. -/
def colorWindowRows {κ : Type*} {N n : ℕ} (W : κ × Fin N → Fin n → Set V)
    (r : Fin 17) (p : κ × Fin N) (i : Fin n) : Set V :=
  if p.2.val % 17 = r.val then W p i else ∅

/-- A single axial colour retains a seventeenth of the aggregate incidence
mass. Disjoint original labels and separated same-colour windows then give
pairwise disjoint output rows for each original index. -/
theorem select_axial_window_color {κ : Type*} [Fintype κ] {N n : ℕ}
    {c ℓ : ℝ} (hc : 0 < c) (A B : κ → ℝ) (z : κ → V)
    (e : κ → V ≃ₗᵢ[ℝ] V) (Y : κ → Fin n → Set V)
    (W : κ × Fin N → Fin n → Set V)
    (hY : ∀ i, Pairwise fun k k' => Disjoint (Y k i) (Y k' i))
    (hW : ∀ p i, W p i ⊆ Y p.1 i ∩
      P (A p.1) (B p.1) (c/8) (axialWindowCenter c ℓ (z p.1) (e p.1) p.2) (e p.1)) :
    ∃ r : Fin 17,
      (1/17:ENNReal)*(∑ p, ∑ i, μ (W p i)) ≤ ∑ p, ∑ i, μ (colorWindowRows W r p i) ∧
      (∀ i, Pairwise fun p p' => Disjoint (colorWindowRows W r p i) (colorWindowRows W r p' i)) ∧
      (∀ p i, colorWindowRows W r p i ⊆ W p i) ∧
      ∀ p, (⋃ i, colorWindowRows W r p i).Nonempty → ∀ i, colorWindowRows W r p i = W p i := by
  classical
  obtain ⟨r, hr⟩ := axial_color_mass (fun p => ∑ i, μ (W p i))
  have hsum : (∑ p, ∑ i, μ (colorWindowRows W r p i)) =
      ∑ p, if p.2.val % 17 = r.val then ∑ i, μ (W p i) else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.2.val % 17 = r.val <;> simp [colorWindowRows, hp]
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · rw [hsum]
    have hh := mul_le_mul' (le_refl (1/17:ENNReal)) hr
    have hc17 : (1/17:ENNReal)*17 = 1 := by
      rw [one_div, ENNReal.inv_mul_cancel (by norm_num : (17:ENNReal) ≠ 0) (by norm_num)]
    simp only [← mul_assoc, hc17, one_mul] at hh
    exact hh
  · intro i p p' hpp'
    by_cases hp : p.2.val % 17 = r.val
    · by_cases hp' : p'.2.val % 17 = r.val
      · simp only [colorWindowRows, if_pos hp, if_pos hp']
        by_cases hk : p.1 = p'.1
        · have hj : p.2.val ≠ p'.2.val := by
            intro hj
            apply hpp'
            exact Prod.ext hk (Fin.ext hj)
          have hd : Disjoint
              (P (A p.1) (B p.1) c (axialWindowCenter c ℓ (z p.1) (e p.1) p.2) (e p.1))
              (P (A p'.1) (B p'.1) c (axialWindowCenter c ℓ (z p'.1) (e p'.1) p'.2) (e p'.1)) := by
            rw [← hk]
            exact prescribed_length_windows_disjoint hc (z p.1) (e p.1) hj (hp.trans hp'.symm)
          apply hd.mono
          · intro x hx
            have hx' := (hW p i hx).2
            exact ⟨hx'.1, hx'.2.1, hx'.2.2.trans (by linarith)⟩
          · intro x hx
            have hx' := (hW p' i hx).2
            exact ⟨hx'.1, hx'.2.1, hx'.2.2.trans (by linarith)⟩
        · exact (hY i hk).mono ((hW p i).trans inter_subset_left)
            ((hW p' i).trans inter_subset_left)
      · simp [colorWindowRows, hp']
    · simp [colorWindowRows, hp]
  · intro p i
    by_cases hp : p.2.val % 17 = r.val <;> simp [colorWindowRows, hp]
  · intro p hp
    have hrp : p.2.val % 17 = r.val := by
      by_contra hh
      simpa [colorWindowRows, hh] using hp
    intro i
    simp [colorWindowRows, hrp]

/-- Colour selection preserves measurability, every per-window broadness
bound, and density in each occupied window. -/
theorem color_window_properties {κ : Type*} {N n : ℕ}
    (W : κ × Fin N → Fin n → Set V) (r : Fin 17)
    {β d θ D : ℝ} (ν : Fin n → V) (U : κ × Fin N → Set V)
    (hWm : ∀ p i, MeasurableSet (W p i))
    (hBr : ∀ p x u s, d ≤ s → q n {i | x ∈ W p i ∧ pd (ν i) u ≤ s} ≤
      8*(s/θ)^β*q n {i | x ∈ W p i})
    (hden : ∀ p, (⋃ i, W p i).Nonempty → O D*μ (U p) ≤ μ (⋃ i, W p i)) :
    (∀ p i, MeasurableSet (colorWindowRows W r p i)) ∧
    (∀ p x u s, d ≤ s → q n {i | x ∈ colorWindowRows W r p i ∧ pd (ν i) u ≤ s} ≤
      8*(s/θ)^β*q n {i | x ∈ colorWindowRows W r p i}) ∧
    ∀ p, (⋃ i, colorWindowRows W r p i).Nonempty →
      O D*μ (U p) ≤ μ (⋃ i, colorWindowRows W r p i) := by
  constructor
  · intro p i
    by_cases hp : p.2.val % 17 = r.val <;> simp [colorWindowRows, hp, hWm]
  constructor
  · intro p x u s hs
    by_cases hp : p.2.val % 17 = r.val
    · simpa only [colorWindowRows, if_pos hp] using hBr p x u s hs
    · simp [colorWindowRows, hp, q]
  · intro p hp
    by_cases hrp : p.2.val % 17 = r.val
    · simpa only [colorWindowRows, if_pos hrp] using hden p
        (by simpa only [colorWindowRows, if_pos hrp] using hp)
    · simpa [colorWindowRows, hrp] using hp

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
