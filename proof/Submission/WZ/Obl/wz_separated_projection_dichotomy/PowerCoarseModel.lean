-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.PowerCoarseModel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseTripleModel
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseNumerics

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem CoarseTripleData.mono_bounds {δ C C' D ζ d d' : ℝ}
    {F G U : Finset Plane} {H : Finset Triple}
    (model : CoarseTripleData δ C D ζ d F G U H) (hδ : 0 ≤ δ) (hCC : C ≤ C') (hdd : d' ≤ d) :
    Nonempty (CoarseTripleData δ C' D ζ d' F G U H) := by
  refine ⟨{ model with
    first_frostman := by
      intro x r hr
      have hrp : 0 ≤ r := hδ.trans hr
      exact (model.first_frostman x r hr).trans (by gcongr)
    second_frostman := by
      intro x r hr
      have hrp : 0 ≤ r := hδ.trans hr
      exact (model.second_frostman x r hr).trans (by gcongr)
    third_frostman := by
      intro x r hr
      have hrp : 0 ≤ r := hδ.trans hr
      exact (model.third_frostman x r hr).trans (by gcongr)
    density := ?_ }⟩
  exact (by gcongr : d' * (model.first.card : ℝ) * (model.second.card : ℝ) * (model.third.card : ℝ) ≤
    d * (model.first.card : ℝ) * (model.second.card : ℝ) * (model.third.card : ℝ)).trans model.density

/-- Bounded counting configurations admit separated models with arbitrarily
small power losses in regularity and density. -/
theorem exists_power_coarse_model {ℓ α ζ R : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hα1 : α ≤ 1) (hζ : 0 < ζ) (hR : 0 ≤ R)
    (hαℓ : α ≤ ℓ / 100) (hαζ : α ≤ ℓ * ζ / 100) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (F G U : Finset Plane) (H : Finset Triple),
        (∀ x ∈ F, ‖x‖ ≤ R) → (∀ x ∈ G, ‖x‖ ≤ R) → (∀ x ∈ U, ‖x‖ ≤ R) →
        ClosedFiniteFrostman δ (δ ^ (-ℓ / 4)) F →
        ClosedFiniteFrostman δ (δ ^ (-ℓ / 4)) G →
        ClosedFiniteFrostman δ (δ ^ (-ℓ / 4)) U →
        IndexedLineFrostman δ (δ ^ (-ℓ / 4)) ζ (fun x : G => (x : Plane)) →
        IndexedLineFrostman δ (δ ^ (-ℓ / 4)) ζ (fun x : U => (x : Plane)) →
        H ⊆ F ×ˢ (G ×ˢ U) → H.Nonempty →
        δ ^ α * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
        Nonempty (CoarseTripleData δ (δ ^ (-ℓ)) (δ ^ (-ℓ)) ζ (δ ^ (3 * α)) F G U H) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hbudget⟩ := exists_coarse_scale_budget hℓ hα hα1 hζ hR hαℓ hαζ
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hsmall F G U H hFn hGn hUn hF hG hU hGl hUl hH hHne hden
  obtain ⟨n, hlast, hpoint, hline, hdensity⟩ := hbudget δ hδ hsmall
  have hδ1 : δ ≤ 1 := hsmall.trans hδ₀1
  let A := (2 * R + 1) ^ (2 : ℕ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmall' : 3 * (δ ^ (α + 2) / (6 * A)) * (A / δ ^ (2 : ℕ)) ≤ δ ^ α / 2 := by
    have heq : 3 * (δ ^ (α + 2) / (6 * A)) * (A / δ ^ (2 : ℕ)) = δ ^ α / 2 := by
      rw [Real.rpow_add hδ, Real.rpow_ofNat]
      field_simp
      <;> ring
    exact heq.le
  obtain ⟨model⟩ := exists_coarse_triple_data hδ hδ1 hR
    (by positivity : 0 ≤ δ ^ (-ℓ / 4)) (by positivity : 0 ≤ δ ^ (-ℓ)) hζ.le
    (by positivity : 0 < δ ^ α) (by positivity : 0 < δ ^ (α + 2) / (6 * A))
    (le_refl (A / δ ^ (2 : ℕ))) hsmall' hlast hline
    F G U H hFn hGn hUn hF hG hU hGl hUl hH hHne hden
  exact model.mono_bounds hδ.le hpoint hdensity

end WangZahlLot.Obl.wz_separated_projection_dichotomy
