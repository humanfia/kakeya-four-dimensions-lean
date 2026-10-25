-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Bridge
import Submission.WZ.Obl.wz_restricted_uniform_improvement.UniformDensity
import Submission.WZ.Obl.wz_tube_packing_bound
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Frostman.FinalQ
import Submission.WZ.Obl.wz_concentrated_family_improvement

/-!
# The children of the split of o017, restated

The three children in the readable terms of `Estimates.lean` and
`AllScales.lean`: `Admissible`, `Katz`, `Frostman`, `Estimate`, `Full`,
`AllScalesCover`. Subfamilies are injective maps `g : Fin k → Fin n`.
-/

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement.Glue

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap WangZahlLot.Obl.wz_restricted_uniform_improvement

/-- The frozen assertion `e`, with its admissibility hypotheses curried. -/
def Ee (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    Dense δ η Y → Katz δ m x v → Frostman δ l x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem Full.curried {σ ω : ℝ} (hE : Full σ ω) : Ee σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  exact ⟨a, ha, η, hη, fun δ hδ hδ1 m l hm hl n x v Y hn hv hb hd hmeas hsub hden hK hF =>
    h δ hδ hδ1 m l hm hl n x v Y ⟨hn, hv, hb, hd, hmeas, hsub, hden⟩ hK hF⟩

/-- A nonempty, injectively indexed subfamily satisfying the all-scales
condition with error `ξ`. -/
def Sticky (ξ δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
    AllScalesCover δ ξ (fun j => x (g j)) (fun j => v (g j))

/-- An injectively indexed subfamily of at least `δ ^ θ * n` tubes that is
Frostman for convex sets with error `δ ^ (-ζ)`. -/
def FrostSub (θ ζ δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {j | tube δ (x (g j)) (v (g j)) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-ζ) * k) * volume W

/-- The restricted target at exponent `w`. -/
def Target (σ w ε a δ m : ℝ) (n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (a * δ ^ (w + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

/-! ### The children -/

theorem packing : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
    (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (n : ℝ) * δ ^ 4 ≤ C :=
  WangZahlLot.wz_tube_packing_bound

theorem frostman_case {σ ω u : ℝ} (hA : AllScalesVolume)
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω < u)
    (hD : Estimate σ ω) (hE : Full σ u) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ α : ℝ, 0 < α ∧ ∃ ζ : ℝ, 0 < ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m : ℝ, 1 ≤ m →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η x v Y → (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
      Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
      ¬ Sticky ξ δ n x v → FrostSub η ζ δ n x v → Target σ (u - α) ε a δ m n Y := by
  have hE' : Ee σ u := Full.curried hE
  have hA' : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.StatementA := by
    intro ε hε
    obtain ⟨a, ha, η, hη, h⟩ := hA ε hε
    refine ⟨a, ha, η, hη, ?_⟩
    intro δ hδ hδ1 n x v Y hn hv hb hd hmeas hsub hden hcover
    exact h δ hδ hδ1 n x v Y ⟨hn, hv, hb, hd, hmeas, hsub, hden⟩ hcover
  obtain ⟨α, hα, ζ, hζ, h⟩ :=
    WangZahlLot.Obl.wz_restricted_uniform_improvement.Frostman.o038_of_A hA'
      σ ω u hσ hσ2 hω hωu hD hE' ξ hξ
  refine ⟨α, hα, ζ, hζ, fun ε hε => ?_⟩
  obtain ⟨a, ha, η, hη, hδ⟩ := h ε hε
  refine ⟨a, ha, η, hη, fun δ hδ0 hδ1 m hm n x v Y hA hind hK hF hS hFS => ?_⟩
  obtain ⟨hn, hv, hb, hd, hmeas, hsub, hden⟩ := hA
  exact hδ δ hδ0 hδ1 m hm n x v Y hn hv hb hd hmeas hsub hden hK hF hind hS hFS

theorem concentrated_case {σ ω u : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hωu : ω < u) (hD : Estimate σ ω) (hE : Full σ u) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ α : ℝ, 0 < α ∧ ∀ θ : ℝ, 0 < θ → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m : ℝ, 1 ≤ m →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η x v Y → (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
      Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
      ¬ FrostSub θ ζ δ n x v → Target σ (u - α) ε a δ m n Y := by
  have hE' : Ee σ u := Full.curried hE
  obtain ⟨α, hα, h⟩ :=
    WangZahlLot.wz_concentrated_family_improvement σ ω u hσ hσ2 hω hωu hD hE' ζ hζ
  refine ⟨α, hα, fun θ hθ ε hε => ?_⟩
  obtain ⟨a, ha, η, hη, hδ⟩ := h θ hθ ε hε
  refine ⟨a, ha, η, hη, fun δ hδ0 hδ1 m hm n x v Y hA hind hK hF hNF => ?_⟩
  obtain ⟨hn, hv, hb, hd, hmeas, hsub, hden⟩ := hA
  exact hδ δ hδ0 hδ1 m hm n x v Y hn hv hb hd hmeas hsub hden hK hF hind
    (fun k g hg hk hfr => hNF ⟨k, g, hg, hk, hfr⟩)

end WangZahlLot.Obl.wz_restricted_uniform_improvement.Glue
