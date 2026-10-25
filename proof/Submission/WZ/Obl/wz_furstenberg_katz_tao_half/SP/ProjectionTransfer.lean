-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.ProjectionTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealRuzsaSum
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealCoverAlgebra
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScaledGridCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridQuantization
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScalarAlgebra

/-!
# Transferring a small projection between overlapping products

If `A₀ + t₀ B₀` and `A₁ + t B₁` both have small covers and `A₀ ∩ A₁`, `B₀ ∩ B₁` are large,
then `A₀ + t B₀` has a small cover (four applications of Ruzsa's triangle inequality,
`real_ruzsa_sum`). This lets products chosen separately for each scalar be replaced by
one product.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

theorem RealCoverBound.of_subset_sum {δ M : ℝ} {A A' B B' : Finset ℝ} (h : RealCoverBound δ (A + B) M)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : RealCoverBound δ (A' + B') M :=
  h.mono (Finset.add_subset_add hA hB) le_rfl

theorem RealCoverBound.comm_sum {δ M : ℝ} {A B : Finset ℝ} (h : RealCoverBound δ (A + B) M) :
    RealCoverBound δ (B + A) M := by
  rw [add_comm]
  exact h

/-- `real_ruzsa_sum` in the `RealCoverBound` form, with a lower bound for the middle grid. -/
theorem RealCoverBound.ruzsa {δ M N g : ℝ} (hδ : 0 < δ) (hg : 0 < g) {A B C : Finset ℝ}
    (hAB : RealCoverBound δ (A + B) M) (hBC : RealCoverBound δ (B + C) N)
    (hBg : g ≤ ((B.image (realGridIndex δ)).card : ℝ)) :
    RealCoverBound δ (A + C) (36 * M * N / g) := by
  obtain ⟨m, ca, hca, hm⟩ := hAB
  obtain ⟨n, cc, hcc, hn⟩ := hBC
  obtain ⟨k, centers, hcov, hk⟩ := real_ruzsa_sum hδ A B C ca cc hca hcc
  refine ⟨k, centers, hcov, ?_⟩
  rw [le_div_iff₀ hg]
  have h1 : (k : ℝ) * g ≤ (k : ℝ) * ((B.image (realGridIndex δ)).card : ℝ) :=
    mul_le_mul_of_nonneg_left hBg (Nat.cast_nonneg _)
  have h2 : 36 * (m : ℝ) * (n : ℝ) ≤ 36 * M * N := by
    have hM : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have : (m : ℝ) * n ≤ M * N := mul_le_mul hm hn hN (hM.trans hm)
    linarith
  linarith

theorem grid_card_eq_of_separated {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    ((A.image (realGridIndex δ)).card : ℝ) = (A.card : ℝ) := by
  rw [Finset.card_image_of_injOn (realGridIndex_injective hδ hsep)]

/-- **Transfer of a small projection.** Constants: with `M` bounding both covers,
`#(A₀ ∩ A₁) ≥ a`, `#(B₀ ∩ B₁) ≥ b`, `τ ≤ t₀, t ≤ 1`, the sum `A₀ + t B₀` has a cover of
size `241864704 * M ^ 5 / (τ ^ 4 * a * b * #A₀ * #B₀)`. -/
theorem projection_transfer {δ M τ t₀ t a b : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (ht₀ : τ ≤ t₀) (ht₀1 : t₀ ≤ 1) (ht : τ ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b)
    {A₀ B₀ A₁ B₁ : Finset ℝ} (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
    (hA₀sep : ∀ x ∈ A₀, ∀ y ∈ A₀, x ≠ y → δ ≤ dist x y)
    (hB₀sep : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → δ ≤ dist x y)
    (h₀ : RealCoverBound δ (A₀ + realScalarImage t₀ B₀) M)
    (h₁ : RealCoverBound δ (A₁ + realScalarImage t B₁) M)
    (hX : a ≤ ((A₀ ∩ A₁).card : ℝ)) (hY : b ≤ ((B₀ ∩ B₁).card : ℝ)) :
    RealCoverBound δ (A₀ + realScalarImage t B₀)
      (241864704 * M ^ 5 / (τ ^ 4 * a * b * (A₀.card : ℝ) * (B₀.card : ℝ))) := by
  classical
  have ht₀p : 0 < t₀ := hτ.trans_le ht₀
  have htp : 0 < t := hτ.trans_le ht
  have hM : 0 ≤ M := h₀.nonneg
  have hnA : (0 : ℝ) < A₀.card := by exact_mod_cast hA₀.card_pos
  have hnB : (0 : ℝ) < B₀.card := by exact_mod_cast hB₀.card_pos
  -- grids
  have hgB₀ : t₀ * (B₀.card : ℝ) / 4 ≤
      (((realScalarImage t₀ B₀).image (realGridIndex δ)).card : ℝ) := by
    have h := scaled_grid_card_lower hδ ht₀p ht₀1 B₀ hB₀sep
    simp only [realScalarImage]
    linarith
  have hgA₀ : (A₀.card : ℝ) ≤
      (((realScalarImage (1 / t₀) A₀).image (realGridIndex δ)).card : ℝ) := by
    have hsep' : ∀ x ∈ realScalarImage (1 / t₀) A₀, ∀ y ∈ realScalarImage (1 / t₀) A₀,
        x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hne
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      have hne' : x' ≠ y' := fun h => hne (by rw [h])
      have h := hA₀sep x' hx' y' hy' hne'
      rw [Real.dist_eq] at h ⊢
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / t₀)]
      have h1 : 1 ≤ 1 / t₀ := by rw [le_div_iff₀ ht₀p]; linarith
      nlinarith [abs_nonneg (x' - y')]
    rw [grid_card_eq_of_separated hδ hsep']
    simp only [realScalarImage]
    rw [Finset.card_image_of_injective _ (fun x y h => by
      have h' : (1 / t₀) * x = (1 / t₀) * y := h
      exact mul_left_cancel₀ (by positivity) h')]
  -- Step 1: A₀ + A₀
  have hAA : RealCoverBound δ (A₀ + A₀) (36 * M * M / (t₀ * (B₀.card : ℝ) / 4)) :=
    RealCoverBound.ruzsa hδ (by positivity) h₀ h₀.comm_sum hgB₀
  -- Step 2: B₀ + B₀, through `A₀ / t₀`
  have hBA : RealCoverBound δ (B₀ + realScalarImage (1 / t₀) A₀) (3 * (1 / t₀) * M) := by
    have h := RealCoverBound.scale hδ (u := 1 / t₀) (U := 1 / t₀)
      (by rw [le_div_iff₀ ht₀p]; linarith) (le_of_eq (abs_of_pos (by positivity))) h₀
    have heq : (A₀ + realScalarImage t₀ B₀).image (fun x => 1 / t₀ * x) =
        realScalarImage (1 / t₀) A₀ + B₀ := by
      have := realScalarImage_add (1 / t₀) A₀ (realScalarImage t₀ B₀)
      simp only [realScalarImage] at this ⊢
      rw [this, Finset.image_image]
      congr 1
      have hf : (fun x => 1 / t₀ * x) ∘ (fun x => t₀ * x) = id := by
        funext x
        simp only [Function.comp, id]
        field_simp
      rw [hf, Finset.image_id]
    rw [heq] at h
    exact h.comm_sum
  have hBB : RealCoverBound δ (B₀ + B₀)
      (36 * (3 * (1 / t₀) * M) * (3 * (1 / t₀) * M) / (A₀.card : ℝ)) :=
    RealCoverBound.ruzsa hδ hnA hBA hBA.comm_sum hgA₀
  -- Step 3: A₀ + t B₁, through `A₀ ∩ A₁`
  have hX0 : RealCoverBound δ (A₀ + (A₀ ∩ A₁)) (36 * M * M / (t₀ * (B₀.card : ℝ) / 4)) :=
    hAA.of_subset_sum subset_rfl Finset.inter_subset_left
  have hX1 : RealCoverBound δ ((A₀ ∩ A₁) + realScalarImage t B₁) M :=
    h₁.of_subset_sum Finset.inter_subset_right subset_rfl
  have hXsep : ∀ x ∈ A₀ ∩ A₁, ∀ y ∈ A₀ ∩ A₁, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hne => hA₀sep x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 hne
  have hgX : a ≤ (((A₀ ∩ A₁).image (realGridIndex δ)).card : ℝ) := by
    rw [grid_card_eq_of_separated hδ hXsep]
    exact hX
  have hAtB₁ : RealCoverBound δ (A₀ + realScalarImage t B₁)
      (36 * (36 * M * M / (t₀ * (B₀.card : ℝ) / 4)) * M / a) :=
    RealCoverBound.ruzsa hδ ha hX0 hX1 hgX
  -- Step 4: A₀ + t B₀, through `t (B₀ ∩ B₁)`
  have hY0 : RealCoverBound δ (A₀ + realScalarImage t (B₀ ∩ B₁))
      (36 * (36 * M * M / (t₀ * (B₀.card : ℝ) / 4)) * M / a) := by
    apply hAtB₁.of_subset_sum subset_rfl
    exact Finset.image_subset_image Finset.inter_subset_right
  have hY1 : RealCoverBound δ (realScalarImage t (B₀ ∩ B₁) + realScalarImage t B₀)
      (36 * (3 * (1 / t₀) * M) * (3 * (1 / t₀) * M) / (A₀.card : ℝ)) := by
    have h := RealCoverBound.scale_contract hδ.le (u := t)
      (by rw [abs_of_pos htp]; exact ht1) hBB
    have heq : (B₀ + B₀).image (fun x => t * x) = realScalarImage t B₀ + realScalarImage t B₀ := by
      have := realScalarImage_add t B₀ B₀
      simpa only [realScalarImage] using this
    rw [heq] at h
    apply h.of_subset_sum _ subset_rfl
    exact Finset.image_subset_image Finset.inter_subset_left
  have hYsep : ∀ x ∈ B₀ ∩ B₁, ∀ y ∈ B₀ ∩ B₁, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hne => hB₀sep x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 hne
  have hgY : t * b / 4 ≤ (((realScalarImage t (B₀ ∩ B₁)).image (realGridIndex δ)).card : ℝ) := by
    have h := scaled_grid_card_lower hδ htp ht1 (B₀ ∩ B₁) hYsep
    have hb' : t * b ≤ t * ((B₀ ∩ B₁).card : ℝ) := mul_le_mul_of_nonneg_left hY htp.le
    simp only [realScalarImage]
    linarith
  have hfinal := RealCoverBound.ruzsa hδ (by positivity) hY0 hY1 hgY
  apply hfinal.mono subset_rfl
  -- the constant
  have hτ4 : τ ^ 4 ≤ t * t₀ ^ 3 := by
    have h1 : τ ^ 3 ≤ t₀ ^ 3 := pow_le_pow_left₀ hτ.le ht₀ 3
    calc τ ^ 4 = τ * τ ^ 3 := by ring
      _ ≤ t * t₀ ^ 3 := mul_le_mul ht h1 (by positivity) htp.le
  have hid : 36 * (36 * (36 * M * M / (t₀ * (B₀.card : ℝ) / 4)) * M / a) *
      (36 * (3 * (1 / t₀) * M) * (3 * (1 / t₀) * M) / (A₀.card : ℝ)) / (t * b / 4) =
      241864704 * M ^ 5 / ((t * t₀ ^ 3) * a * b * (A₀.card : ℝ) * (B₀.card : ℝ)) := by
    field_simp
    ring
  rw [hid]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hab : 0 < a * b * (A₀.card : ℝ) * (B₀.card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right hτ4 hab.le
  nlinarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
