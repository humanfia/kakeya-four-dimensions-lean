-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FactorProjections.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Strips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set

/-- A dense finite tripartite hypergraph uses at least its density fraction
of each of the three vertex classes. -/
theorem product_density_projection_cards {X Y Z : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (A : Finset X) (B : Finset Y) (C : Finset Z) (H : Finset (X × Y × Z))
    (hH : H ⊆ A ×ˢ (B ×ˢ C)) (hHne : H.Nonempty) {d : ℝ}
    (hd : d * (A.card : ℝ) * (B.card : ℝ) * (C.card : ℝ) ≤ (H.card : ℝ)) :
    d * (A.card : ℝ) ≤ ((H.image Prod.fst).card : ℝ) ∧
    d * (B.card : ℝ) ≤ ((H.image (fun p => p.2.1)).card : ℝ) ∧
    d * (C.card : ℝ) ≤ ((H.image (fun p => p.2.2)).card : ℝ) := by
  obtain ⟨p, hp⟩ := hHne
  have hp' := Finset.mem_product.mp (hH hp)
  have hp'' := Finset.mem_product.mp hp'.2
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.1, hp'.1⟩
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.2.1, hp''.1⟩
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.2.2, hp''.2⟩
  have h₁ : H ⊆ H.image Prod.fst ×ˢ (B ×ˢ C) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      (Finset.mem_product.mp (hH hp)).2⟩
  have h₂ : H ⊆ A ×ˢ (H.image (fun p => p.2.1) ×ˢ C) := by
    intro p hp
    have h := Finset.mem_product.mp (hH hp)
    exact Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, (Finset.mem_product.mp h.2).2⟩⟩
  have h₃ : H ⊆ A ×ˢ (B ×ˢ H.image (fun p => p.2.2)) := by
    intro p hp
    have h := Finset.mem_product.mp (hH hp)
    exact Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp h.2).1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩⟩
  have hc₁ : (H.card : ℝ) ≤ ((H.image Prod.fst).card : ℝ) * (B.card : ℝ) * (C.card : ℝ) := by
    have h := Finset.card_le_card h₁
    simp only [Finset.card_product] at h
    exact_mod_cast (by simpa only [mul_assoc] using h)
  have hc₂ : (H.card : ℝ) ≤ (A.card : ℝ) * ((H.image (fun p => p.2.1)).card : ℝ) * (C.card : ℝ) := by
    have h := Finset.card_le_card h₂
    simp only [Finset.card_product] at h
    exact_mod_cast (by simpa only [mul_assoc] using h)
  have hc₃ : (H.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) * ((H.image (fun p => p.2.2)).card : ℝ) := by
    have h := Finset.card_le_card h₃
    simp only [Finset.card_product] at h
    exact_mod_cast (by simpa only [mul_assoc] using h)
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_le_mul_iff_left₀ hBpos).mp ((mul_le_mul_iff_left₀ hCpos).mp (hd.trans hc₁))
  · have h := (mul_le_mul_iff_left₀ hCpos).mp (hd.trans hc₂)
    apply (mul_le_mul_iff_right₀ hApos).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ (mul_pos hApos hBpos)).mp
    nlinarith [hd.trans hc₃]

theorem FiniteFrostman.projected_factors {δ C d : ℝ} {S T U : Finset Plane}
    (hS : FiniteFrostman δ C S) (hT : FiniteFrostman δ C T) (hU : FiniteFrostman δ C U)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hd : 0 < d)
    (H : Finset Triple) (hH : H ⊆ S ×ˢ (T ×ˢ U)) (hHne : H.Nonempty)
    (hdensity : d * (S.card : ℝ) * (T.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ)) :
    FiniteFrostman δ (C / d) (H.image Prod.fst) ∧
    FiniteFrostman δ (C / d) (H.image (fun p => p.2.1)) ∧
    FiniteFrostman δ (C / d) (H.image (fun p => p.2.2)) := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := product_density_projection_cards S T U H hH hHne hdensity
  refine ⟨hS.subset hδ hC hd ?_ h₁, hT.subset hδ hC hd ?_ h₂,
    hU.subset hδ hC hd ?_ h₃⟩
  · rintro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (hH hp)).1
  · rintro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  · rintro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).2

end WangZahlLot.Obl.wz_separated_projection_dichotomy
