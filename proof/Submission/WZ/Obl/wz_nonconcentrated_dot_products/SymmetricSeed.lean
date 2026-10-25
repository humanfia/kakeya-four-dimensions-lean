-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.SymmetricSeed.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.QuarterThinTubes
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinTubes

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- The seed can be obtained in both directions with the same cutoff. -/
theorem exists_symmetric_quarter_thin_tubes {ℓ ζ α : ℝ} (hℓ : 0 < ℓ) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (I J : Type) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
        (f : I → Plane) (g : J → Plane),
      IndexedFrostman δ (δ ^ (-ℓ)) f → IndexedFrostman δ (δ ^ (-ℓ)) g →
      IndexedLineFrostman δ (δ ^ (-ℓ)) ζ f → IndexedLineFrostman δ (δ ^ (-ℓ)) ζ g →
      (∀ i j, 1 / 4 ≤ ‖f i - g j‖ ∧ ‖f i - g j‖ ≤ 8) →
      SymmetricThinTubes δ (1 / 4) (32 * δ ^ (-(ℓ + 3 * α / ζ))) (δ ^ α) f g := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hseed⟩ := exists_quarter_thin_tubes hℓ hζ hζ1 hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hsmall I J _ _ _ _ f g hF hG hLF hLG hpoints
  refine ⟨hseed δ hδ hsmall I J f g hF hG hLG hpoints, ?_⟩
  apply hseed δ hδ hsmall J I g f hG hF hLF
  intro j i
  simpa only [norm_sub_rev] using hpoints i j

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
