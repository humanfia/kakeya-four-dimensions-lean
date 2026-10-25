import Submission.Obl.k4_general_parent_wide_layer_candidates.Model

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Every original sample object is pulled back along the same subsequence. -/
def reindex (τ : ℕ → ℕ) : Parent α where
  N := fun k => p.N (τ k)
  K := fun k => p.K (τ k)
  d := p.d
  κ := p.κ
  ℓ := p.ℓ
  S := p.S
  U := p.U
  e₀ := p.e₀
  ν := fun k => p.ν (τ k)
  μ := fun k => p.μ (τ k)
  ρ := fun k => p.ρ (τ k)
  π := fun k => p.π (τ k)
  b := fun k => p.b (τ k)
  P := fun k => p.P (τ k)
  T := fun k => p.T (τ k)
  n := fun k => p.n (τ k)
  j := fun k => p.j (τ k)
  A := fun k => p.A (τ k)
  B := fun k => p.B (τ k)
  c := fun k => p.c (τ k)
  F := fun k => p.F (τ k)

theorem Valid.reindex (hp : p.Valid) {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    (p.reindex τ).Valid where
  scale k := hp.scale (τ k)
  scale_limit := hp.scale_limit.comp hτ
  subpower := ⟨fun k => hp.subpower.1 (τ k),
    fun ε hε => hτ.eventually (hp.subpower.2 ε hε)⟩
  dimension_nonneg := hp.dimension_nonneg
  dimension_lt_one := hp.dimension_lt_one
  rate_pos := hp.rate_pos
  rate_le_one := hp.rate_le_one
  transverse_pos := hp.transverse_pos
  palette_pos := hp.palette_pos
  palette_le_one := hp.palette_le_one
  depth_pos := hp.depth_pos
  defect_pos := hp.defect_pos
  basic k := hp.basic (τ k)
  caps R hR := hτ.eventually (hp.caps R hR)
  prepared R hR := hτ.eventually (hp.prepared R hR)
  nested R hR := hτ.eventually (hp.nested R hR)

/-- Eventual preparation on a cofinal subsequence is sufficient for the
original frequently-quantified candidate conclusion. -/
theorem candidates_of_reindex {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop)
    (hc : (p.reindex τ).Candidates) : p.Candidates := by
  obtain ⟨R, hR, hfreq⟩ := hc
  refine ⟨R, hR, ?_⟩
  intro ε hε
  have hf := hfreq ε hε
  rw [Filter.frequently_atTop]
  intro n
  obtain ⟨k, hk, hn⟩ := (hf.and_eventually (hτ.eventually (Filter.eventually_ge_atTop n))).exists
  exact ⟨τ k, hn, hk⟩

end Parent
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
