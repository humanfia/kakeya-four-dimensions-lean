-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Lists; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Mathlib

/-!
# Residual lists built from cells, intercept bins, labels and shifts

A residual list at one velocity bin `a` collects, over scalar cells `x`, intercept bins
`b'` compatible with `x` and `a`, coarse labels of the tag `(a, b')`, fine labels of
each coarse label, and integer shifts `|k'| ≤ L`, the pair `(x, val x i j + k')`.
Its cardinality is at most the product of the menu sizes.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

noncomputable section

namespace Parent.FieldFrame

/-- The residual list at velocity bin `a`. -/
def listBuild {ι κ : Type*} (cells : Finset (ℤ × ℤ)) (bRange : ℤ × ℤ → ℤ → Finset ℤ)
    (choices : (Fin 2 → ℤ) → Finset ι) (fine : ι → Finset κ) (val : ℤ × ℤ → ι → κ → ℤ)
    (L : ℤ) (a : ℤ) : Finset ((Fin 2 → ℤ) × ℤ) := by
  classical
  exact cells.biUnion fun x => (bRange x a).biUnion fun b' => (choices ![a, b']).biUnion
    fun i => (fine i).biUnion fun j =>
      (Finset.Icc (-L) L).image fun k' => ((![x.1, x.2] : Fin 2 → ℤ), val x i j + k')

theorem mem_listBuild {ι κ : Type*} {cells : Finset (ℤ × ℤ)} {bRange : ℤ × ℤ → ℤ → Finset ℤ}
    {choices : (Fin 2 → ℤ) → Finset ι} {fine : ι → Finset κ} {val : ℤ × ℤ → ι → κ → ℤ}
    {L a : ℤ} {x : ℤ × ℤ} {b' : ℤ} {i : ι} {j : κ} {k' : ℤ}
    (hx : x ∈ cells) (hb : b' ∈ bRange x a) (hi : i ∈ choices ![a, b']) (hj : j ∈ fine i)
    (hk : k' ∈ Finset.Icc (-L) L) :
    ((![x.1, x.2] : Fin 2 → ℤ), val x i j + k') ∈ listBuild cells bRange choices fine val L a := by
  classical
  unfold listBuild
  simp only [Finset.mem_biUnion, Finset.mem_image]
  exact ⟨x, hx, b', hb, i, hi, j, hj, k', hk, rfl⟩

theorem card_biUnion_le_real {ι β : Type*} [DecidableEq β] (s : Finset ι) (t : ι → Finset β)
    {B : ℝ} (h : ∀ i ∈ s, ((t i).card : ℝ) ≤ B) :
    ((s.biUnion t).card : ℝ) ≤ s.card * B := by
  calc ((s.biUnion t).card : ℝ) ≤ ((∑ i ∈ s, (t i).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ i ∈ s, ((t i).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

theorem card_Icc_real {a b : ℤ} (h : a ≤ b + 1) :
    ((Finset.Icc a b).card : ℝ) = b + 1 - a := by
  rw [Int.card_Icc]
  have : (0 : ℤ) ≤ b + 1 - a := by omega
  rw [show ((b + 1 - a).toNat : ℝ) = (((b + 1 - a).toNat : ℤ) : ℝ) from rfl,
    Int.toNat_of_nonneg this]
  push_cast
  ring

theorem card_listBuild_le {ι κ : Type*} (cells : Finset (ℤ × ℤ))
    (bRange : ℤ × ℤ → ℤ → Finset ℤ)
    (choices : (Fin 2 → ℤ) → Finset ι) (fine : ι → Finset κ) (val : ℤ × ℤ → ι → κ → ℤ)
    {L : ℤ} (hL : 0 ≤ L) (a : ℤ) {Bb Bc Bf : ℝ} (hBc : 0 ≤ Bc) (hBf : 0 ≤ Bf)
    (hb : ∀ x, ((bRange x a).card : ℝ) ≤ Bb) (hc : ∀ τ, ((choices τ).card : ℝ) ≤ Bc)
    (hf : ∀ i, ((fine i).card : ℝ) ≤ Bf) :
    ((listBuild cells bRange choices fine val L a).card : ℝ) ≤
      cells.card * (Bb * (Bc * (Bf * (2 * L + 1)))) := by
  classical
  have hL' : (0 : ℝ) ≤ 2 * L + 1 := by
    have : (0 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hk : ∀ x i j, (((Finset.Icc (-L) L).image fun k' =>
      ((![x.1, x.2] : Fin 2 → ℤ), val x i j + k')).card : ℝ) ≤ 2 * L + 1 := by
    intro x i j
    calc _ ≤ ((Finset.Icc (-L) L).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = 2 * L + 1 := by rw [card_Icc_real (by omega)]; push_cast; ring
  unfold listBuild
  apply card_biUnion_le_real
  intro x _
  calc _ ≤ ((bRange x a).card : ℝ) * (Bc * (Bf * (2 * L + 1))) := by
        apply card_biUnion_le_real
        intro b' _
        calc _ ≤ ((choices ![a, b']).card : ℝ) * (Bf * (2 * L + 1)) := by
              apply card_biUnion_le_real
              intro i _
              calc _ ≤ ((fine i).card : ℝ) * (2 * L + 1) := by
                    apply card_biUnion_le_real
                    intro j _
                    exact hk x i j
                _ ≤ Bf * (2 * L + 1) := mul_le_mul_of_nonneg_right (hf i) hL'
          _ ≤ Bc * (Bf * (2 * L + 1)) :=
              mul_le_mul_of_nonneg_right (hc _) (mul_nonneg hBf hL')
    _ ≤ Bb * (Bc * (Bf * (2 * L + 1))) :=
        mul_le_mul_of_nonneg_right (hb x) (mul_nonneg hBc (mul_nonneg hBf hL'))

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
