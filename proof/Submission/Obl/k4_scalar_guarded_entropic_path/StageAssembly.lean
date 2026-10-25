import Submission.Obl.k4_scalar_guarded_entropic_path.RawStage

/-! Separate the original geometry from the reference-law conclusions
while keeping precisely the same stage data. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.RawStage

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

structure GeometryGood (st : RawStage) (d κ : ℝ) (k : ℕ) (R δ : ℝ) : Prop where
  exact : Split.Exact st.p
  budgets : 0 < st.scale ∧ st.scale ≤ 1 ∧ 2 ≤ st.H ∧ 0 < st.buffer ∧
    1 ≤ st.M ∧ st.p.M ≤ st.M ∧ st.p.D ≤ st.M ∧ st.p.L ≤ (st.M : ℝ) ∧
    st.p.K st.sample ≤ st.H ∧ (st.count : ℝ) ≤ st.H ∧
    st.H ≤ st.N₀ ^ (st.M : ℝ) ∧ st.H ≤ st.B
  scale_le : st.scale ≤ δ
  buffer_le : st.buffer ≤ δ
  actual_le : st.actual k ≤ st.N ^ δ
  length_gt : st.scale * R < st.p.L
  resolution_ge : (k : ℝ) + 2 ≤ st.N
  B_ge_one : 1 ≤ st.B
  B_le : st.B ≤ st.N ^ δ
  sigma_le : ∀ g, st.σ g ≤ Split.mu st.p st.sample g
  sigma_mass : ENNReal.ofReal (2 * st.H⁻¹) ≤ ENNReal.ofReal (1 / 2 : ℝ) *
    ∑ g, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g univ
  layer_good : ∀ j, st.LayerGood d κ j
  node_round : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → st.N ^ |st.depth (st.node s) - s| ≤ st.B
  guard : ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - st.buffer →
    ¬Split.Chart st.p (st.guard k) (st.scale * r) st.p.L (st.scale * h)
      (st.loss k) false st.sample

theorem Good.of_geometry {st : RawStage} {d κ S : ℝ} {k : ℕ} {R δ : ℝ}
    (g : st.GeometryGood d κ k R δ) (hm : (k : ℝ) + 1 ≤ st.m)
    (hα : 0 < st.α) (hαtwo : 2 ≤ st.N ^ st.α) (hαle : st.α ≤ δ)
    (hcode : ∀ a, st.CodeGood d a)
    (hfrostman : ∀ a b, R⁻¹ ≤ b → b ≤ R → ∀ e : ℤ,
      st.π₀ a {v | velocityBin st.N b v = e} ≤ ENNReal.ofReal (st.B * st.N ^ (-S * b)))
    (hinfo : st.InfoBudget) : st.Good d κ S k R δ where
  exact := g.exact
  budgets := g.budgets
  scale_le := g.scale_le
  buffer_le := g.buffer_le
  actual_le := g.actual_le
  length_gt := g.length_gt
  resolution_ge := g.resolution_ge
  B_ge_one := g.B_ge_one
  B_le := g.B_le
  sigma_le := g.sigma_le
  sigma_mass := g.sigma_mass
  layer_good := g.layer_good
  node_round := g.node_round
  guard := g.guard
  m_ge := hm
  α_pos := hα
  α_two := hαtwo
  α_le := hαle
  code_good := hcode
  frostman := hfrostman
  info := hinfo

theorem Good.mono_delta {st : RawStage} {d κ S : ℝ} {k : ℕ} {R δ δ' : ℝ}
    (h : st.Good d κ S k R δ) (hδ : δ ≤ δ') : st.Good d κ S k R δ' := by
  have hN : 1 ≤ st.N := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [h.resolution_ge]
  exact { h with
    scale_le := h.scale_le.trans hδ
    buffer_le := h.buffer_le.trans hδ
    actual_le := h.actual_le.trans (Real.rpow_le_rpow_of_exponent_le hN hδ)
    B_le := h.B_le.trans (Real.rpow_le_rpow_of_exponent_le hN hδ)
    α_le := h.α_le.trans hδ }

end

end Submission.Obl.k4_scalar_guarded_entropic_path.RawStage
