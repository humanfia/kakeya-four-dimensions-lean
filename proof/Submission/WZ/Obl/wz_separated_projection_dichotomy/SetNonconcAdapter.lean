-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.SetNonconcAdapter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SetCountBridges
import Submission.WZ.Obl.wz_separated_projection_dichotomy.GeneralSetAdapter

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- A set version of bounded Prop. 8.5, expressed without subtype indices. -/
def BoundedSetNonconcentratedAt (δ ℓ ζ α ε : ℝ) : Prop :=
  ∀ (F G U : Set Plane) (H : Set Triple),
    BoundedSetFrostman δ (δ ^ (-ℓ)) F →
    BoundedSetFrostman δ (δ ^ (-ℓ)) G →
    BoundedSetFrostman δ (δ ^ (-ℓ)) U →
    (∀ (u : Plane) (a r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ({x ∈ G | |inner ℝ x u - a| < r}.ncard : ℝ) ≤ (δ ^ (-ℓ) * r) ^ ζ * G.ncard) →
    (∀ (u : Plane) (a r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ({x ∈ U | |inner ℝ x u - a| < r}.ncard : ℝ) ≤ (δ ^ (-ℓ) * r) ^ ζ * U.ncard) →
    (∀ x ∈ G, ∀ y ∈ U, 1 / 4 ≤ dist x y) →
    H ⊆ F ×ˢ (G ×ˢ U) → H.Nonempty →
    δ ^ α * (F.ncard : ℝ) * (G.ncard : ℝ) * (U.ncard : ℝ) ≤ (H.ncard : ℝ) →
    CoverLower δ (DotSet H) (δ ^ (ε - 1))

def BoundedSetNonconcentratedPrinciple : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → BoundedSetNonconcentratedAt δ ℓ ζ α ε

theorem BoundedSetNonconcentratedAt.to_finset {δ ℓ ζ α ε : ℝ}
    (h : BoundedSetNonconcentratedAt δ ℓ ζ α ε) :
    BoundedNonconcentratedAt true δ ℓ ζ α ε := by
  intro F G U H hFn hGn hUn hFs hGs hUs hF hG hU hGl hUl hsep hH hHne hden
  apply h (↑F : Set Plane) (↑G : Set Plane) (↑U : Set Plane) (↑H : Set Triple)
    (boundedSetFrostman_coe hFn (hFs rfl) hF)
    (boundedSetFrostman_coe hGn (hGs rfl) hG)
    (boundedSetFrostman_coe hUn (hUs rfl) hU)
    (indexedLineFrostman_iff_ncard.mp hGl) (indexedLineFrostman_iff_ncard.mp hUl)
  · intro x hx y hy
    simpa only [dist_eq_norm] using hsep x hx y hy
  · intro p hp
    simpa only [Set.mem_prod, Finset.mem_product, Finset.mem_coe] using hH hp
  · exact hHne
  · simpa only [Set.ncard_coe_finset] using hden

theorem bounded_nonconcentrated_of_set
    (h : BoundedSetNonconcentratedPrinciple) : BoundedNonconcentratedPrinciple true := by
  intro ε hε hε1
  obtain ⟨ℓ, hℓ, hℓP⟩ := h ε hε hε1
  refine ⟨ℓ, hℓ, ?_⟩
  intro ζ hζ hζ1
  obtain ⟨α, δ₀, hα, hδ₀, hP⟩ := hℓP ζ hζ hζ1
  exact ⟨α, δ₀, hα, hδ₀, fun δ hδ hs => (hP δ hδ hs).to_finset⟩

theorem separated_set_statement_of_set_nonconcentrated
    (h : BoundedSetNonconcentratedPrinciple) : SeparatedSetStatement :=
  separated_set_statement_of_bounded_nonconcentrated (bounded_nonconcentrated_of_set h)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
