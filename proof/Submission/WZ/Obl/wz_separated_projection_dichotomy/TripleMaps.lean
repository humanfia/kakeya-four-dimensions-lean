-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleMaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadiusTransfer
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Parameters
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRestriction

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

def mapTriple (φ ψ : Plane → Plane) (p : Triple) : Triple := (φ p.1, ψ p.2.1, ψ p.2.2)

theorem mapTriple_injective {φ ψ : Plane → Plane} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) : Function.Injective (mapTriple φ ψ) := by
  intro p q hpq
  have h₁ := hφ (congrArg Prod.fst hpq)
  have h₂ := hψ (congrArg (fun p : Triple => p.2.1) hpq)
  have h₃ := hψ (congrArg (fun p : Triple => p.2.2) hpq)
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

theorem mapTriple_contained {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (φ ψ : Plane → Plane) :
    H.image (mapTriple φ ψ) ⊆ F.image φ ×ˢ (G.image ψ ×ˢ U.image ψ) := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := Finset.mem_product.mp (hH hq)
  have h' := Finset.mem_product.mp h.2
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q.1, h.1, rfl⟩,
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q.2.1, h'.1, rfl⟩,
      Finset.mem_image.mpr ⟨q.2.2, h'.2, rfl⟩⟩⟩

theorem TripleUniform.density {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hsupport : ∀ x ∈ G, ∃ a b, (a, x, b) ∈ H) :
    d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) := by
  classical
  have hh := h.restrict_second_density (Finset.Subset.refl G) hsupport
  have heq : restrictSecond H G = H := by
    ext p
    simp only [restrictSecond, Finset.mem_filter, and_iff_left_iff_imp]
    intro hp
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  simpa only [heq] using hh

theorem CoverLower.of_anisotropic_triples {e : Plane} {h δ N : ℝ} {H : Finset Triple}
    (he : ‖e‖ = 1) (hh : 0 < h)
    (hcov : CoverLower (δ / h)
      (DotSet (↑(H.image (mapTriple (anisotropicMap e h⁻¹ 1) (anisotropicMap e 1 h⁻¹))) : Set Triple)) N) :
    CoverLower δ (DotSet (↑H : Set Triple)) N := by
  classical
  have hc := hcov.affine_image (u := 0) hh
  have hrad : h * (δ / h) = δ := by field_simp
  rw [hrad] at hc
  apply hc.mono_set
  rintro t ⟨s, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  refine ⟨q, hq, ?_⟩
  simp only [mapTriple, add_zero]
  exact (anisotropicMap_dual_dot he hh q.1 q.2.1 q.2.2).symm

end WangZahlLot.Obl.wz_separated_projection_dichotomy
