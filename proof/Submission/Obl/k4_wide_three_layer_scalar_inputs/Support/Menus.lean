import Mathlib

set_option linter.unusedVariables false

/-!
# Finite menus of floor states from small variation

If the real coordinates of a family of points vary by at most the bin widths, their floor
states lie in a box of `3^n` states around any one of them.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

noncomputable section

theorem floor_sub_floor_le_one {a b : ℝ} (h : |a - b| ≤ 1) : ⌊a⌋ - ⌊b⌋ ≤ 1 ∧ -1 ≤ ⌊a⌋ - ⌊b⌋ := by
  have ha1 := Int.floor_le a
  have ha2 := Int.lt_floor_add_one a
  have hb1 := Int.floor_le b
  have hb2 := Int.lt_floor_add_one b
  rw [abs_le] at h
  constructor
  · have : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
    have : ⌊a⌋ - ⌊b⌋ < 2 := by exact_mod_cast this
    omega
  · have : (-2 : ℝ) < ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by push_cast; linarith
    have : -2 < ⌊a⌋ - ⌊b⌋ := by exact_mod_cast this
    omega

theorem floor_div_close {x y r : ℝ} (hr : 0 < r) (h : |x - y| ≤ r) :
    ⌊x / r⌋ - ⌊y / r⌋ ≤ 1 ∧ -1 ≤ ⌊x / r⌋ - ⌊y / r⌋ := by
  apply floor_sub_floor_le_one
  rw [← sub_div, abs_div, abs_of_pos hr, div_le_one hr]
  exact h

/-- The box of `3^n` floor states around `σ₀`. -/
def stateBox {n : ℕ} (σ₀ : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Finset.univ.image (fun δ : Fin n → Fin 3 => fun i => σ₀ i + ((δ i : ℕ) : ℤ) - 1)

theorem card_stateBox_le {n : ℕ} (σ₀ : Fin n → ℤ) : (stateBox σ₀).card ≤ 3 ^ n := by
  unfold stateBox
  refine (Finset.card_image_le).trans ?_
  simp

theorem mem_stateBox {n : ℕ} {σ₀ σ : Fin n → ℤ} (h : ∀ i, σ i - σ₀ i ≤ 1 ∧ -1 ≤ σ i - σ₀ i) :
    σ ∈ stateBox σ₀ := by
  unfold stateBox
  rw [Finset.mem_image]
  refine ⟨fun i => ⟨(σ i - σ₀ i + 1).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have := h i; omega
  · funext i
    have := h i
    simp only
    omega

/-- **Finite menus.**  If on `E ∩ G` every coordinate `f · i` varies by at most `r i`, the floor
states of `E ∩ G` lie in a menu of at most `3^n` states. -/
theorem exists_floor_menu {Ω : Type*} {n : ℕ} (E G : Set Ω) (f : Ω → Fin n → ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (hvar : ∀ p ∈ E ∩ G, ∀ p' ∈ E ∩ G, ∀ i, |f p i - f p' i| ≤ r i) :
    ∃ M : Finset (Fin n → ℤ), M.card ≤ 3 ^ n ∧
      ∀ p ∈ E ∩ G, (fun i => ⌊f p i / r i⌋) ∈ M := by
  classical
  by_cases hne : (E ∩ G).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    refine ⟨stateBox (fun i => ⌊f p₀ i / r i⌋), card_stateBox_le _, ?_⟩
    intro p hp
    apply mem_stateBox
    intro i
    exact floor_div_close (hr i) (hvar p hp p₀ hp₀ i)
  · refine ⟨∅, by simp, ?_⟩
    intro p hp
    exact (hne ⟨p, hp⟩).elim

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
