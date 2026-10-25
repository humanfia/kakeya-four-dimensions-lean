-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphRealTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphRectification
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProjectionFromPaths

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Real vertex sets obtained by graph rectification work simultaneously
for every affine projection with slope bounded away from zero. -/
theorem graph_real_projection_transfer (A B : Finset ℝ) (R : A → B → Prop)
    {δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hdensity : d * (A.card : ℝ) * (B.card : ℝ) ≤
      ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ)) :
    ∃ X Y : Finset ℝ, X ⊆ A ∧ Y ⊆ B ∧ X.Nonempty ∧ Y.Nonempty ∧
      (d / 4) * (A.card : ℝ) ≤ (X.card : ℝ) ∧
      (d ^ 2 / 16) * (B.card : ℝ) ≤ (Y.card : ℝ) ∧
      ∀ c t : ℝ, 0 < c → c ≤ t → t ≤ 1 →
        ∀ (m : ℕ) (cc : Fin m → ℝ),
          Covers δ ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
            (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) cc →
          ∃ (n : ℕ) (centers : Fin n → ℝ),
            Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(X ×ˢ Y) : Set (ℝ × ℝ))) centers ∧
            c * (d ^ 7 / 524288) * (A.card : ℝ) * (B.card : ℝ) * (n : ℝ) ≤
              288 * (m : ℝ) ^ 3 := by
  classical
  letI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  letI : Nonempty B := ⟨⟨hB.choose, hB.choose_spec⟩⟩
  have hdens : d * (Fintype.card A : ℝ) * (Fintype.card B : ℝ) ≤
      ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ) := by
    simpa only [Fintype.card_coe] using hdensity
  obtain ⟨X₀, Y₀, hX₀, hY₀, hXsize, hYsize, hpaths⟩ := graph_rectification R hd hd1 hdens
  let X := X₀.image (fun x : A => (x : ℝ))
  let Y := Y₀.image (fun y : B => (y : ℝ))
  have hXcard : X.card = X₀.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hYcard : Y.card = Y₀.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hXA : X ⊆ A := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    exact x₀.2
  have hYB : Y ⊆ B := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
    exact y₀.2
  simp only [Fintype.card_coe] at hXsize hYsize hpaths
  refine ⟨X, Y, hXA, hYB, hX₀.image _, hY₀.image _, ?_, ?_, ?_⟩
  · rwa [hXcard]
  · rwa [hYcard]
  · intro c t hc hct ht m cc hcov
    obtain ⟨n, centers, hn, hcount⟩ := projection_cover_of_many_paths A B R X₀ Y₀
      hδ hc hct ht hAsep hBsep hpaths cc hcov
    refine ⟨n, centers, hn.mono_set ?_, hcount⟩
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    obtain ⟨x, hx₀, hx⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy₀, hy⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx₀, hy₀⟩, by simp [hx, hy]⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
