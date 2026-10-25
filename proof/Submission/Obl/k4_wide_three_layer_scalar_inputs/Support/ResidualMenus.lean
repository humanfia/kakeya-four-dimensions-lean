import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualGeometry

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Finset

noncomputable section

private theorem card_biUnion_real_le {I J : Type*} [DecidableEq J] (S : Finset I)
    (F : I → Finset J) {B : ℝ} (hB : ∀ i ∈ S, ((F i).card : ℝ) ≤ B) :
    ((S.biUnion F).card : ℝ) ≤ (S.card : ℝ) * B := by
  calc
    _ ≤ ∑ i ∈ S, ((F i).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _i ∈ S, B := sum_le_sum hB
    _ = _ := by simp

open scoped Classical in
/-- The residual options at one base cell and one fine original velocity bin. -/
def residualVelocityMenu {Γ : Type} (pc : Γ → Fin 6 → ℝ) (σ Kz τv H : ℝ)
    (Ch : (Fin 2 → ℤ) → ℤ → Finset (ℤ × ℤ)) (G : (ℤ × ℤ) → Finset Γ)
    (Fo : (ℤ × ℤ) → Γ → Finset ℤ) (z : Fin 2 → ℤ) (w : ℤ) : Finset ℤ :=
  (Ch z w).biUnion fun ch => (G ch).biUnion fun γ => (Fo ch γ).biUnion fun o =>
    residualBinOptions τv H (residualBaseValue (pc γ) σ Kz z) o

theorem residualVelocityMenu_card {Γ : Type} (pc : Γ → Fin 6 → ℝ) {σ Kz τv H M₀ A : ℝ}
    (hτv : 0 < τv) (hH : 1 ≤ H) (hM₀ : 0 ≤ M₀) (hA : 0 ≤ A)
    (Ch : (Fin 2 → ℤ) → ℤ → Finset (ℤ × ℤ)) (G : (ℤ × ℤ) → Finset Γ)
    (Fo : (ℤ × ℤ) → Γ → Finset ℤ)
    (hCh : ∀ z w, ((Ch z w).card : ℝ) ≤ M₀)
    (hG : ∀ ch, ((G ch).card : ℝ) ≤ H)
    (hFo : ∀ ch γ, ((Fo ch γ).card : ℝ) ≤ H * A) (z : Fin 2 → ℤ) (w : ℤ) :
    ((residualVelocityMenu pc σ Kz τv H Ch G Fo z w).card : ℝ) ≤ M₀ * H ^ 3 * A * 7 := by
  classical
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have ho ch γ : (((Fo ch γ).biUnion fun o =>
      residualBinOptions τv H (residualBaseValue (pc γ) σ Kz z) o).card : ℝ) ≤
      (H * A) * (7 * H) :=
    (card_biUnion_real_le _ _ (fun o _ => residualBinOptions_card hτv hH o)).trans
      (mul_le_mul_of_nonneg_right (hFo ch γ) (by positivity))
  have hg ch : (((G ch).biUnion fun γ => (Fo ch γ).biUnion fun o =>
      residualBinOptions τv H (residualBaseValue (pc γ) σ Kz z) o).card : ℝ) ≤
      H * ((H * A) * (7 * H)) :=
    (card_biUnion_real_le _ _ (fun γ _ => ho ch γ)).trans
      (mul_le_mul_of_nonneg_right (hG ch) (by positivity))
  calc
    _ ≤ ((Ch z w).card : ℝ) * (H * ((H * A) * (7 * H))) :=
      card_biUnion_real_le _ _ (fun ch _ => hg ch)
    _ ≤ M₀ * (H * ((H * A) * (7 * H))) :=
      mul_le_mul_of_nonneg_right (hCh z w) (by positivity)
    _ = _ := by ring

theorem mem_residualVelocityMenu {Γ : Type} (pc : Γ → Fin 6 → ℝ) (σ Kz τv H : ℝ)
    (Ch : (Fin 2 → ℤ) → ℤ → Finset (ℤ × ℤ)) (G : (ℤ × ℤ) → Finset Γ)
    (Fo : (ℤ × ℤ) → Γ → Finset ℤ) (z : Fin 2 → ℤ) (w : ℤ)
    {ch : ℤ × ℤ} {γ : Γ} {o j : ℤ} (hch : ch ∈ Ch z w) (hγ : γ ∈ G ch)
    (ho : o ∈ Fo ch γ)
    (hj : j ∈ residualBinOptions τv H (residualBaseValue (pc γ) σ Kz z) o) :
    j ∈ residualVelocityMenu pc σ Kz τv H Ch G Fo z w := by
  classical
  exact mem_biUnion.mpr ⟨ch, hch, mem_biUnion.mpr ⟨γ, hγ, mem_biUnion.mpr ⟨o, ho, hj⟩⟩⟩

open scoped Classical in
/-- The full output menu for one velocity bin, summed over the original bounded base grid. -/
def residualOutputMenu {Γ : Type} (pc : Γ → Fin 6 → ℝ) (σ Kz τv H : ℝ)
    (Ch : (Fin 2 → ℤ) → ℤ → Finset (ℤ × ℤ)) (G : (ℤ × ℤ) → Finset Γ)
    (Fo : (ℤ × ℤ) → Γ → Finset ℤ) (w : ℤ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  (residualBaseCells σ Kz).biUnion fun z =>
    (residualVelocityMenu pc σ Kz τv H Ch G Fo z w).image (fun j => (z, j))

theorem residualOutputMenu_card {Γ : Type} (pc : Γ → Fin 6 → ℝ) {σ Kz τv H M₀ A : ℝ}
    (hσ : 0 < σ) (hKz : 0 ≤ Kz) (hτv : 0 < τv) (hH : 1 ≤ H) (hM₀ : 0 ≤ M₀) (hA : 0 ≤ A)
    (Ch : (Fin 2 → ℤ) → ℤ → Finset (ℤ × ℤ)) (G : (ℤ × ℤ) → Finset Γ)
    (Fo : (ℤ × ℤ) → Γ → Finset ℤ)
    (hCh : ∀ z w, ((Ch z w).card : ℝ) ≤ M₀)
    (hG : ∀ ch, ((G ch).card : ℝ) ≤ H)
    (hFo : ∀ ch γ, ((Fo ch γ).card : ℝ) ≤ H * A) (w : ℤ) :
    ((residualOutputMenu pc σ Kz τv H Ch G Fo w).card : ℝ) ≤
      ((1 / σ + 2) * (2 * Kz / σ + 2)) * (M₀ * H ^ 3 * A * 7) := by
  classical
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hi z : (((residualVelocityMenu pc σ Kz τv H Ch G Fo z w).image
      (fun j => (z, j))).card : ℝ) ≤ M₀ * H ^ 3 * A * 7 := by
    refine (show _ ≤ ((residualVelocityMenu pc σ Kz τv H Ch G Fo z w).card : ℝ) from ?_).trans
      (residualVelocityMenu_card pc hτv hH hM₀ hA Ch G Fo hCh hG hFo z w)
    exact_mod_cast card_image_le
  calc
    _ ≤ ((residualBaseCells σ Kz).card : ℝ) * (M₀ * H ^ 3 * A * 7) :=
      card_biUnion_real_le _ _ (fun z _ => hi z)
    _ ≤ _ := mul_le_mul_of_nonneg_right (residualBaseCells_card hσ hKz) (by positivity)

open scoped Classical in
/-- A finite initial universe uses all original labels. Its size is irrelevant: the
palette argument will count its positive surviving states using the velocity menus. -/
def residualCandidateUniverse {Γ Λ : Type} [Fintype Λ] (crs : Λ → Γ)
    (pc : Γ → Fin 6 → ℝ) (D2 : Λ → ℝ) (σ Kz τv H : ℝ) :
    Finset ((Fin 2 → ℤ) × ℤ) :=
  (residualBaseCells σ Kz).biUnion fun z => (univ : Finset Λ).biUnion fun x =>
    (residualBinOptions τv H (residualBaseValue (pc (crs x)) σ Kz z) ⌊D2 x / τv⌋).image
      (fun j => (z, j))

theorem mem_residualCandidateUniverse {Γ Λ : Type} [Fintype Λ] (crs : Λ → Γ)
    (pc : Γ → Fin 6 → ℝ) (D2 : Λ → ℝ) (σ Kz τv H : ℝ) (x : Λ)
    {z : Fin 2 → ℤ} {j : ℤ} (hz : z ∈ residualBaseCells σ Kz)
    (hj : j ∈ residualBinOptions τv H (residualBaseValue (pc (crs x)) σ Kz z) ⌊D2 x / τv⌋) :
    (z, j) ∈ residualCandidateUniverse crs pc D2 σ Kz τv H := by
  classical
  exact mem_biUnion.mpr ⟨z, hz, mem_biUnion.mpr
    ⟨x, mem_univ _, mem_image.mpr ⟨j, hj, rfl⟩⟩⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
