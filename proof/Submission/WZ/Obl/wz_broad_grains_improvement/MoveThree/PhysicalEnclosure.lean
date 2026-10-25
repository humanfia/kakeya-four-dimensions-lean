-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, PhysicalEnclosure.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConvexEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalWidth
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AffineVolume
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (affine_preimage_density affineEquiv_volume affineEquiv_jacobian_pos)

/-- Density survives the inverse affine map and the bounded-volume rectangular
enclosure. The entire normalized body is retained. -/
theorem inverse_dense_prism_enclosure {a b c A₀ B₀ C₀ K D : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hA₀ : 0 ≤ A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀)
    (hC₀ : 0 < C₀) (hK : 0 < K) (hD : 0 ≤ D)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V) (H : Set V)
    (hInv : ∀ p q, dist (f.symm p) (f.symm q) ≤ (K*c)*dist p q)
    (hwhole : f '' P a b c z e ⊆ P A₀ B₀ C₀ z₀ e₀)
    (hH : H ⊆ P A₀ B₀ C₀ z₀ e₀)
    (hden : O D * μ (P A₀ B₀ C₀ z₀ e₀) ≤ μ H) :
    ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 8*K*C₀*c ∧
      f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ P A B (8*K*C₀*c) z' e' ∧
      f.symm '' H ⊆ P A B (8*K*C₀*c) z' e' ∧
      μ (P A B (8*K*C₀*c) z' e') ≤ O (6912*K*C₀) * μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) ∧
      O (D/(6912*K*C₀)) * μ (P A B (8*K*C₀*c) z' e') ≤ μ (f.symm '' H) := by
  obtain ⟨A, B, z', e', haA, hAB, hB, hbox, hvol⟩ :=
    inverse_prism_enclosure ha hab hbc hA₀ hAB₀ hBC₀ hC₀ hK z z₀ e e₀ f hInv hwhole
  have hden' : O D * μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) ≤ μ (f.symm '' H) := by
    have hh := affine_preimage_density f (affineEquiv_jacobian_pos f)
      (affineEquiv_volume f) (O D) hden
    have he (W : Set V) : f.symm '' W = f ⁻¹' W := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        simpa only [mem_preimage, f.apply_symm_apply] using hq
      · intro hp
        exact ⟨f p, hp, f.symm_apply_apply p⟩
    simpa only [he] using hh
  refine ⟨A, B, z', e', haA, hAB, hB, hbox, (image_mono hH).trans hbox, hvol, ?_⟩
  calc
    O (D/(6912*K*C₀)) * μ (P A B (8*K*C₀*c) z' e')
        ≤ O (D/(6912*K*C₀)) * (O (6912*K*C₀) * μ (f.symm '' P A₀ B₀ C₀ z₀ e₀)) :=
      mul_le_mul' le_rfl hvol
    _ = O D * μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ D/(6912*K*C₀)),
        div_mul_cancel₀ _ (by positivity : 6912*K*C₀ ≠ 0)]
    _ ≤ μ (f.symm '' H) := hden'

/-- High overlap, whole-body containment and normalized density produce a
dense physical prism at a larger relative middle scale. All fixed enclosure
losses fit a uniform cutoff; the long side grows by `8 K C₀`. -/
theorem HB_dense_inverse_prism {q₀ jump h₀ h₁ K C₀ : ℝ}
    (hjump : 0 < jump) (hq : 3*jump < q₀) (hh : h₀ < h₁)
    (hK : 0 < K) (hC₀ : 0 < C₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {h ρ a c b g m A₀ B₀ : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f₀ : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs : Fin L → Set V} {γ : Fin L → Fin N},
      0 < ρ → (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f₀ a c b g L z e Hs γ m →
      0 ≤ A₀ → A₀ ≤ B₀ → B₀ ≤ C₀ →
      ∀ (Q : Finset (Fin L)) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
        (f : V ≃ᵃ[ℝ] V) (H : Set V),
        (∀ p q, dist (f.symm p) (f.symm q) ≤ (K*c)*dist p q) →
        (∀ j ∈ Q, f '' P a (ρ*c) c (z j) (e j) ⊆ P A₀ B₀ C₀ z₀ e₀) →
        (∃ p, δ ^ (-q₀) < q L {j | j ∈ Q ∧ p ∈ Hs j}) →
        M H → H ⊆ P A₀ B₀ C₀ z₀ e₀ →
        O (δ^h₀) * μ (P A₀ B₀ C₀ z₀ e₀) ≤ μ H →
        ∃ (A ρ' : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
          a ≤ A ∧ A ≤ ρ'*(8*K*C₀*c) ∧ 0 < ρ' ∧ ρ' ≤ 1 ∧
          δ^(-jump)*ρ ≤ ρ' ∧
          f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ P A (ρ'*(8*K*C₀*c)) (8*K*C₀*c) z' e' ∧
          (∀ j ∈ Q, P a (ρ*c) c (z j) (e j) ⊆ P A (ρ'*(8*K*C₀*c)) (8*K*C₀*c) z' e') ∧
          M (f.symm '' H) ∧ f.symm '' H ⊆ P A (ρ'*(8*K*C₀*c)) (8*K*C₀*c) z' e' ∧
          O (δ^h₁) * μ (P A (ρ'*(8*K*C₀*c)) (8*K*C₀*c) z' e') ≤ μ (f.symm '' H) := by
  let t := (jump + q₀/3)/2
  have hjt : jump < t := by dsimp only [t]; linarith
  have ht : 0 < t := hjump.trans hjt
  have htq : 3*t < q₀ := by dsimp only [t]; linarith
  obtain ⟨dW, hdW, hdW1, HW⟩ := HB_container_width_growth ht htq
  obtain ⟨dR, hdR, HR⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hjt) (by positivity : 0 < 1/(8*K*C₀))
  obtain ⟨dD, hdD, HD⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hh) (by positivity : 0 < 1/(6912*K*C₀))
  refine ⟨min dW (min dR dD), lt_min hdW (lt_min hdR hdD),
    (min_le_left _ _).trans hdW1, ?_⟩
  intro δ hδ hδd h ρ a c b g m A₀ B₀ n N L x v S Z y w f₀ z e Hs γ
    hρ hw hX hHB hA₀ hAB₀ hBC₀ Q z₀ e₀ f H hInv hwhole hhigh hHm hH hden
  have ha : 0 < a := hδ.trans_le hHB.1
  have hb : 0 < ρ*c := ha.trans_le hHB.2.1
  have hc : 0 < c := hb.trans_le hHB.2.2.1
  have hQ : Q.Nonempty := by
    by_contra hQ
    obtain ⟨p, hp⟩ := hhigh
    have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp [he, q] at hp
    exact (Real.rpow_pos_of_pos hδ (-q₀)).not_gt hp
  obtain ⟨j₀, hj₀⟩ := hQ
  obtain ⟨A, B, z', e', haA, hAB, hB, hbox, hHbox, _, hD⟩ :=
    inverse_dense_prism_enclosure ha hHB.2.1 hHB.2.2.1 hA₀ hAB₀ hBC₀ hC₀ hK
      (Real.rpow_nonneg hδ.le h₀) (z j₀) z₀ (e j₀) e₀ f H hInv (hwhole j₀ hj₀) hH hden
  have hsub (j) (hj : j ∈ Q) : P a (ρ*c) c (z j) (e j) ⊆ P A B (8*K*C₀*c) z' e' := by
    intro p hp
    exact hbox ⟨f p, hwhole j hj (mem_image_of_mem f hp), f.symm_apply_apply p⟩
  have hwidth : δ^(-t)*ρ*c ≤ B := HW δ hδ (hδd.trans (min_le_left _ _))
    hρ (ha.le.trans haA) hAB hw hX hHB Q z' e' hsub hhigh
  have hconst : δ^(t-jump) ≤ 1/(8*K*C₀) :=
    HR δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hscale : δ^(-jump)*ρ ≤ B/(8*K*C₀*c) := by
    apply (le_div_iff₀ (by positivity : 0 < 8*K*C₀*c)).mpr
    calc
      δ^(-jump)*ρ*(8*K*C₀*c) =
          ((8*K*C₀)*δ^(t-jump)) * (δ^(-t)*ρ*c) := by
        rw [show ((8*K*C₀)*δ^(t-jump)) * (δ^(-t)*ρ*c) =
          (8*K*C₀)*(δ^(t-jump)*δ^(-t))*ρ*c by ring, ← Real.rpow_add hδ]
        rw [show t-jump+-t = -jump by ring]
        ring
      _ ≤ 1*(δ^(-t)*ρ*c) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh := (le_div_iff₀ (by positivity : 0 < 8*K*C₀)).mp hconst
        nlinarith
      _ ≤ B := by simpa only [one_mul] using hwidth
  have hdenloss : δ^h₁ ≤ δ^h₀/(6912*K*C₀) := by
    have hh := HD δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_right _ _)))
    calc
      δ^h₁ = δ^(h₁-h₀)*δ^h₀ := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ (1/(6912*K*C₀))*δ^h₀ := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  have hmul : B/(8*K*C₀*c)*(8*K*C₀*c) = B := div_mul_cancel₀ _ (by positivity)
  refine ⟨A, B/(8*K*C₀*c), z', e', haA, ?_,
    (mul_pos (Real.rpow_pos_of_pos hδ _) hρ).trans_le hscale, ?_, hscale, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hmul] using hAB
  · exact (div_le_one (by positivity : 0 < 8*K*C₀*c)).mpr hB
  · simpa only [hmul] using hbox
  · simpa only [hmul] using hsub
  · exact f.symm.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hHm
  · simpa only [hmul] using hHbox
  · simpa only [hmul] using (mul_le_mul' (ENNReal.ofReal_le_ofReal hdenloss) le_rfl).trans hD

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
