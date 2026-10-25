/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   FrontEnd.lean, and session x0913, branch x0913 at 49f56643, FrozenBridge.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.Raw
import Submission.Obl.k4_narrow_projected_row_parents.Witness
import Submission.Obl.k4_narrow_projected_row_parents.RowParents

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

/-- The front half: narrow layers give row parents at one depth below `U`. -/
def NarrowFront : Prop :=
  Row → Match →
  ∀ (α : Type) [MeasurableSpace α] (cfg : Model α), Model.Valid cfg →
    ∃ Λ : ℝ → ℝ, (∀ L, 2 < L → L + 2 ≤ cfg.S * Λ L) ∧
    ∀ L₀ : ℝ, 2 < L₀ →
      (∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) →
        ∀ m : ℝ, L₀ * a < m → Model.LayerOutput cfg false L₀ a D m) →
      ∀ a s : ℝ, 0 < a → Λ L₀ * a < cfg.U → a ≤ s → s ≤ 2 * a →
      ∀ (τ : ℕ → ℕ) (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
        (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
        (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
        (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
        (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
        Model.NarrowWitness cfg L₀ a ((L₀ + 1) * a) s τ H ρ' β n' C tag u v G →
        cfg.Candidates ∨ ∃ r : ℝ, 0 < r ∧ r < cfg.U ∧ RowParents cfg r

/-- Explicit existential form of the row-parent interface. -/
def RawRowParents {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) : Prop :=
  (fun r:ℝ => ∃ e:ℝ,0 < e ∧ ∃ M:ℕ → ℝ,(∀ k,1 ≤ M k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,M k ≤ cfg.N k^ε) ∧ ∃ᶠ k in Filter.atTop,∃ (Q:Fin (cfg.n k r)) (Brow:Fin 2 → ℝ) (lam:ℝ) (Gset:Set (α × ℝ)),MeasurableSet Gset ∧ Gset ⊆ cfg.B k r Q ×ˢ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k r) (cfg.j k r Q) ∧ ENNReal.ofReal (((2:ℝ)^(-(cfg.T k r:ℤ)))/M k)*cfg.ν k (cfg.A k r Q) ≤ cfg.ρ k Gset ∧ |Brow 0|+|Brow 1| ≤ M k ∧ |lam| ≤ M k ∧ ∀ z ∈ Gset,|(2:ℝ)^(-(cfg.T k r:ℤ))*(cfg.b k z.1 4-cfg.c k r Q 3-cfg.c k r Q 4*cfg.b k z.1 3)/((2:ℝ)^(-(cfg.T k r:ℤ))*cfg.N k^(-cfg.ℓ*r))-Brow 0-Brow 1*cfg.b k z.1 3+lam*((cfg.b k z.1 0+(((cfg.j k r Q:ℕ):ℝ)/(2:ℝ)^cfg.T k r)*cfg.b k z.1 3-(cfg.c k r Q 0+(((cfg.j k r Q:ℕ):ℝ)/(2:ℝ)^cfg.T k r)*cfg.c k r Q 1))/((2:ℝ)^(-(cfg.T k r:ℤ))))| ≤ cfg.N k^(-e)) r

/-- Expanding the row-parent record adds no hypothesis. -/
theorem rawRowParents_iff {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) :
    RawRowParents cfg r ↔ RowParents cfg r := by
  constructor
  · rintro ⟨e, he, M, hM, hsub, hfreq⟩
    refine ⟨e, he, M, hM, hsub, ?_⟩
    apply hfreq.mono
    rintro k ⟨Q, B, lam, G, hmeas, hG, hmass, hB, hlam, hrow⟩
    exact ⟨⟨Q, B, lam, G, hmeas, hG, hmass, hB, hlam, hrow⟩⟩
  · rintro ⟨e, he, M, hM, hsub, hfreq⟩
    refine ⟨e, he, M, hM, hsub, ?_⟩
    apply hfreq.mono
    rintro k ⟨RP⟩
    exact ⟨RP.Q, RP.B, RP.lam, RP.G, RP.measurable_G, RP.G_sub, RP.mass,
      RP.B_le, RP.lam_le, RP.row⟩

/-- The structured row-parent theorem implies the frozen statement. -/
theorem raw_of_front (h : NarrowFront) : RawNarrowFront := by
  intro hRow hMatch N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀
    α inst ν μ ρ π b P T n j A B c F hbasic hcaps hatlas hnested
  let cfg : Model α := ⟨N, K, d, κ, ℓ, S, U, e₀, ν, μ, ρ, π, b, P, T, n, j, A, B, c, F⟩
  have hv : Model.Valid cfg :=
    ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he₀,
      hbasic, hcaps, hatlas, hnested⟩
  obtain ⟨Λ, hΛ, hf⟩ := h hRow hMatch α cfg hv
  refine ⟨Λ, hΛ, ?_⟩
  intro L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw
  rcases hw with ⟨hτ, hH, hsub, hρ', hslice, hnarrow⟩
  have hw' : Model.NarrowWitness cfg L₀ a ((L₀ + 1) * a) s τ H ρ' β n' C tag u v G :=
    ⟨hτ, hH, hsub, hρ', hslice, hnarrow⟩
  rcases hf L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw' with
    hc | ⟨r, hr, hrU, hrows⟩
  · exact Or.inl hc
  · exact Or.inr ⟨r, hr, hrU, (rawRowParents_iff cfg r).mpr hrows⟩

end Submission.Obl.k4_narrow_projected_row_parents
