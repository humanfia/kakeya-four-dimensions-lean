-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_refined_induction_on_scales.Children.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_refined_induction_on_scales.Glue
import Submission.WZ.Obl.wz_refined_induction_on_scales.Frozen

/-!
# The children of the split of o019, in the notation of `Interfaces`

`GrainsChild`, `FlatChild` and `GainChild` (and `E σ ω → R σ ω`) are the statements of the children with their
abbreviations unfolded to the definitions of `Interfaces`; `*_of_frozen` instantiate the frozen
statements of `Frozen` (every `∀ X, X = … →` by `rfl`). `Refined` is the data of o019's alternative
(B) carried by a refinement of a sub-family, and `Conclusion` is o019's conclusion.
-/

namespace WangZahlLot.Obl.wz_refined_induction_on_scales

open MeasureTheory

namespace Interfaces

/-- The data of o019's alternative (B) at error `ζ` and scale `ρ`, carried by a refinement
`S' ⊆ S`, `Z' ⊆ Z` of a given sub-family. -/
def Refined (ζ δ ρ : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (S : Finset (Fin n))
    (Z : Fin n → Set V) : Prop :=
  ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ) (y' w' : Fin N' → V)
    (f' : Fin n → Fin N'),
    S' ⊆ S ∧ (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i) ∧
    o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S', μ (Z' i) ∧
    (∀ k, ‖w' k‖ = 1) ∧ (∀ i ∈ S', T δ (x i) (v i) ⊆ T ρ (y' (f' i)) (w' (f' i))) ∧
    K ρ (δ ^ (-ζ)) N' y' w' ∧ F ρ (δ ^ (-ζ)) N' y' w' ∧ B δ ρ (δ ^ (-ζ)) n N' x v S' y' w' f'

/-- The conclusion of o019, in the notation of `Interfaces`. -/
def Conclusion (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V)
        (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧
        δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧
        (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
        K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ B δ ρ (δ ^ (-ζ)) n N x v S y w f

/-- The two-scale grains child: Proposition 7.5 (o044's content), with the local rescaling `R`
as an additional premise. -/
def GrainsChild (σ ω : ℝ) : Prop :=
  E σ ω → R σ ω → ∀ h : ℝ, 0 < h → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ h ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
      ∃ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f

/-- Proposition 5.2 for boxes `P a b c`, `ρ ≤ a ≤ b ≤ c`, `1 ≤ c ≤ 8`. -/
def Jb :=
  fun (σ ω : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ N y w f, C δ η n x v Y Finset.univ Y ρ N y w f → ∀ a b c : ℝ, ρ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 → ∀ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L), (fun (U : Fin L → Set V) => (∀ k, T ρ (y k) (w k) ⊆ U (g k)) → (∀ j j', q {k | g k = j} ≤ δ ^ (-η) * q {k | g k = j'}) → (∀ k, q {j | T ρ (y k) (w k) ⊆ U j} ≤ δ ^ (-η)) → (∀ W, Convex ℝ W → o (q {j | U j ⊆ W} * (a * b * c)) ≤ o (δ ^ (-η)) * μ W) → (∀ j W, Convex ℝ W → o (q {k | g k = j ∧ T ρ (y k) (w k) ⊆ U j ∩ W}) * μ (U j) ≤ o (δ ^ (-η) * q {k | g k = j}) * μ (U j ∩ W)) → o (κ * δ ^ (ω + ε) * (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)) (fun j => P a b c (z j) (e j))

/-- The flat-box child: WZ Proposition 5.2 for boxes `P a b c`, `1 ≤ c ≤ 8`. -/
def FlatChild (σ ω : ℝ) : Prop := E σ ω → Jb σ ω

/-- The conclusion of the gain child (after its premises `E` and `Jb`): WZ §9, Steps 1–6, for a
grains configuration with no heavy Katz–Tao sub-collection of `ρ`-tubes. -/
def GainBody (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ h : ℝ, 0 < h ∧ h ≤ ζ / 10 ∧ ∃ α : ℝ, 0 < α ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f →
        (∀ U : Finset (Fin N),
          o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i) →
          ¬ ∀ W, Convex ℝ W →
            o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) →
        o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)

/-- The gain child. -/
def GainChild (σ ω : ℝ) : Prop := E σ ω → Jb σ ω → GainBody σ ω

end Interfaces

open Interfaces

/-- The frozen grains child gives `GrainsChild`. -/
theorem grainsChild_of_frozen (h : Frozen.grainsFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GrainsChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl

/-- The frozen rescaling child gives `E σ ω → R σ ω`. -/
theorem rescale_of_frozen (h : Frozen.rescaleFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : E σ ω → R σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- The frozen flat-box child gives `FlatChild`. -/
theorem flatChild_of_frozen (h : Frozen.flatFrozen) {σ ω : ℝ} (hσ : 0 < σ) (hσu : σ ≤ 1 / 2)
    (hω : 0 < ω) (hωu : ω ≤ 1) : FlatChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- The frozen gain child gives `GainChild`. -/
theorem gainChild_of_frozen (h : Frozen.gainFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GainChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

end WangZahlLot.Obl.wz_refined_induction_on_scales
