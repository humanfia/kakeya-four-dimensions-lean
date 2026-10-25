/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/RawStage.lean.
The original source is work of this tree; its provenance comments are retained.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.RawGeometry

/-!
# One stage of the entropic path construction

`RawGeometry ∧ ReferenceLaws` (the output of `EntropicPathConstruction`) is asymptotic in
the stage index. `RawStage` is the data of one stage: one exact parent, one sample, one
scale, finite true layers, the reference law `σ`, and the finite codes of the entropy
window. `RawStage.Good` is the list of finite bounds at stage index `k`, on the tangent
depth range `[R⁻¹, R]` with vanishing exponent `δ`. `RawStage.assemble` turns a sequence of
good stages with `R → ∞`, `δ → 0` into `RawGeometry ∧ ReferenceLaws`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

/-- The data of one stage of the entropic path construction. -/
structure RawStage where
  p : Code
  sample : ℕ
  scale : ℝ
  H : ℝ
  buffer : ℝ
  B : ℝ
  M : ℕ
  count : ℕ
  node : ℝ → Fin count
  depth : Fin count → ℝ
  time : Fin count → ℝ
  layers : Fin count → Layer (p.1 sample)
  σ : Fin (p.1 sample) → Measure Incidence
  m : ℕ
  n : Fin (p.1 sample) → ℕ
  X : (g : Fin (p.1 sample)) → Incidence → Fin (n g)
  Y : (g : Fin (p.1 sample)) → Fin (n g) → ℕ
  Z : (g : Fin (p.1 sample)) → Fin (n g) → ℤ
  q : Fin (p.1 sample) → Fin (m ^ 2 + 1) → ℕ → Fin 2 → ℤ
  c : Fin (p.1 sample) → Fin (m ^ 2 + 1) → ℕ → ℤ
  α : ℝ
  π₀ : Fin (p.1 sample) → Measure ℝ

namespace RawStage

variable (st : RawStage)

abbrev N₀ : ℝ := st.p.N st.sample
abbrev N : ℝ := st.N₀ ^ st.scale
abbrev actual (k : ℕ) : ℝ := (st.H * Real.log st.N₀) ^ (k + 1)
abbrev loss (k : ℕ) : ℝ := Real.log (st.actual k) / Real.log st.N₀
abbrev guard (k : ℕ) : ℕ := 2 ^ ((st.M + k + 1) ^ 2)
abbrev W : ℕ := st.p.1 st.sample

/-- The layer clause of `RawGeometry` for one layer. -/
def LayerGood (d κ : ℝ) (ℓ : Fin st.count) : Prop :=
  let f := st.layers ℓ
  0 ≤ st.depth ℓ ∧ st.scale * st.depth ℓ < st.p.L ∧
    Split.ChartData st.p st.M (st.scale * st.depth ℓ) st.p.L
      (st.scale * st.time ℓ) (Real.log st.H / Real.log st.N₀) true st.sample
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list ∧
    (∀ i, (st.H * (2 : ℝ) ^ f.T)⁻¹ ≤ f.width i) ∧
    (∀ g, st.σ g {z | ∃ i, f.world i = g ∧ z ∈ f.witness i}ᶜ = 0) ∧
    st.N₀ ^ |st.p.profile (st.scale * st.depth ℓ) - d * (st.scale * st.depth ℓ)| ≤ st.B ∧
    st.N ^ (κ * st.depth ℓ) / st.B ≤ (2 : ℝ) ^ f.T ∧
    (2 : ℝ) ^ f.T ≤ st.B * st.N ^ (κ * st.depth ℓ) ∧
    (∀ g, MeasureTheory.Measure.map
        (pureObservation st.N₀ (st.scale * st.depth ℓ)) (st.σ g) ≤
      ENNReal.ofReal (st.B * st.N₀ ^ (-st.p.profile (st.scale * st.depth ℓ))) •
        (MeasureTheory.volume.prod MeasureTheory.Measure.count))

/-- The finite code clause of `ReferenceLaws` in one world. -/
def CodeGood (d : ℝ) (g : Fin st.W) : Prop :=
  Measurable (st.X g) ∧ IsProbabilityMeasure (st.π₀ g) ∧
    MeasureTheory.Measure.map (fun z : Incidence => z.1.2 1) (st.σ g) =
      (st.σ g Set.univ) • st.π₀ g ∧
    (∀ᵐ z ∂st.σ g,
      st.Z g (st.X g z) = velocityBin st.N (st.m : ℝ) (z.1.2 1) ∧
      ∀ j : Fin (st.m ^ 2 + 1),
        baseBin st.N ((j : ℝ) / (st.m : ℝ)) z = st.q g j (st.Y g (st.X g z)) ∧
        hiddenBin st.N ((j : ℝ) / (st.m : ℝ)) z = st.c g j (st.Y g (st.X g z))) ∧
    ∀ j : Fin (st.m ^ 2 + 1),
      MeasureTheory.Measure.map (pureObservation st.N ((j : ℝ) / (st.m : ℝ))) (st.σ g) ≤
        ENNReal.ofReal (st.B * st.N ^ (-d * ((j : ℝ) / (st.m : ℝ)))) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)

/-- The weighted information budget of the entropy window. -/
def InfoBudget : Prop :=
  (∑ g : Fin st.W, st.p.weight st.sample g *
      ∑ i : Fin (st.n g),
        (st.σ g {z | st.X g z = i}).toReal *
          max 0 (Real.log
            (((st.σ g {z | st.Y g (st.X g z) = st.Y g i ∧
                st.Z g (st.X g z) = st.Z g i}).toReal * (st.σ g Set.univ).toReal) /
              ((st.σ g {z | st.Y g (st.X g z) = st.Y g i}).toReal *
                (st.σ g {z | st.Z g (st.X g z) = st.Z g i}).toReal)))) ≤
    ((∑ g : Fin st.W, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g Set.univ).toReal / 2) *
      Real.log (st.N ^ st.α)

/-- Everything one stage of the entropic path construction provides, at stage index
`k`, on the tangent depth range `[R⁻¹, R]` with vanishing exponent `δ`. -/
structure Good (d κ S : ℝ) (k : ℕ) (R δ : ℝ) : Prop where
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
    ∑ g, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g Set.univ
  layer_good : ∀ ℓ, st.LayerGood d κ ℓ
  node_round : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → st.N ^ |st.depth (st.node s) - s| ≤ st.B
  guard : ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - st.buffer →
    ¬Split.Chart st.p (st.guard k) (st.scale * r) st.p.L (st.scale * h)
      (st.loss k) false st.sample
  m_ge : (k : ℝ) + 1 ≤ st.m
  α_pos : 0 < st.α
  α_two : 2 ≤ st.N ^ st.α
  α_le : st.α ≤ δ
  code_good : ∀ g, st.CodeGood d g
  frostman : ∀ (g : Fin st.W) (b : ℝ), R⁻¹ ≤ b → b ≤ R → ∀ e : ℤ,
    st.π₀ g {v | velocityBin st.N b v = e} ≤ ENNReal.ofReal (st.B * st.N ^ (-S * b))
  info : st.InfoBudget

end RawStage

/-- Every incidence law of an exact problem has mass at most one. -/
theorem mu_univ_le_one' {p : Code} (hp : Split.Exact p) (k : ℕ) (g : Fin (p.1 k)) :
    Split.mu p k g Set.univ ≤ 1 := by
  obtain ⟨hprob, _, _, _, hEsub, _⟩ := (hp.2.1 k).2.2.2.1 g
  have hprob' : IsProbabilityMeasure (p.prior k g) := hprob
  calc Split.mu p k g Set.univ = ((p.prior k g).prod volume) (p.support k g) := by
        show (((p.prior k g).prod volume).restrict (p.support k g)) Set.univ = _
        rw [Measure.restrict_apply_univ]
    _ ≤ ((p.prior k g).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hEsub
    _ = 1 := by
        rw [Measure.prod_prod, measure_univ, Real.volume_Icc]
        simp

/-- Fixed compact depth ranges eventually lie inside a growing range. -/
theorem eventually_range_subset {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    {R₀ : ℝ} (hR₀ : 1 < R₀) :
    ∀ᶠ k in atTop, ∀ x : ℝ, R₀⁻¹ ≤ x → x ≤ R₀ → (R k)⁻¹ ≤ x ∧ x ≤ R k := by
  filter_upwards [hR.eventually_ge_atTop R₀] with k hk x hx1 hx2
  have hR₀pos : 0 < R₀ := by linarith
  exact ⟨le_trans (inv_anti₀ hR₀pos hk) hx1, hx2.trans hk⟩

/-- A sequence of good raw stages gives the output of the entropic path construction. -/
theorem RawStage.assemble {d κ S : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hS0 : 0 < S) (hS1 : S ≤ 1)
    (st : ℕ → RawStage) (R δ : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hδ : Tendsto δ atTop (𝓝 0))
    (hgood : ∀ k, (st k).Good d κ S k (R k) (δ k)) :
    RawGeometry (fun k => (st k).p) (fun k => (st k).sample) (fun k => (st k).scale)
        (fun k => (st k).H) (fun k => (st k).buffer) (fun k => (st k).B)
        (fun k => (st k).M) (fun k => (st k).count) (fun k => (st k).node)
        (fun k => (st k).depth) (fun k => (st k).time) (fun k => (st k).layers)
        (fun k => (st k).σ) d κ S ∧
      ReferenceLaws (fun k => (st k).p.N (st k).sample ^ (st k).scale) (fun k => (st k).B) d S
        (fun k => (st k).p.W (st k).sample) (fun k => (st k).p.weight (st k).sample)
        (fun k => (st k).σ) := by
  have hN1 : ∀ k, 1 ≤ (st k).N := fun k => by
    have := (hgood k).resolution_ge
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hδ_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, δ k ≤ ε := fun ε hε =>
    hδ.eventually (ge_mem_nhds hε)
  have hNtend : Tendsto (fun k => (st k).N) atTop atTop := by
    apply tendsto_atTop_mono (fun k => (hgood k).resolution_ge)
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hN2 : ∀ k, 2 ≤ (st k).N := fun k => by
    have := (hgood k).resolution_ge
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hBsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (st k).B ≤ (st k).N ^ ε := by
    intro ε hε
    filter_upwards [hδ_small ε hε] with k hk
    exact ((hgood k).B_le).trans (Real.rpow_le_rpow_of_exponent_le (hN1 k) hk)
  refine ⟨?_, ?_⟩
  · refine ⟨fun k => (hgood k).exact, fun k => (hgood k).budgets, ?_, ?_, ?_, ?_, hN2,
      hNtend, fun k => (hgood k).B_ge_one, hBsub, hd0, hd1, hκ0, hκ1, hS0,
      fun k => (hgood k).sigma_le, fun k => (hgood k).sigma_mass,
      fun k ℓ => (hgood k).layer_good ℓ, ?_, ?_⟩
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
      · exact fun k => (hgood k).budgets.1.le
      · exact fun k => (hgood k).scale_le
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
      · exact fun k => (hgood k).budgets.2.2.2.1.le
      · exact fun k => (hgood k).buffer_le
    · intro ε hε
      filter_upwards [hδ_small ε hε] with k hk
      exact ((hgood k).actual_le).trans (Real.rpow_le_rpow_of_exponent_le (hN1 k) hk)
    · intro R₀ hR₀
      filter_upwards [hR.eventually_ge_atTop R₀] with k hk
      have hsc := (hgood k).budgets.1
      calc (st k).scale * R₀ ≤ (st k).scale * R k := by gcongr
        _ < (st k).p.L := (hgood k).length_gt
    · intro R₀ hR₀
      filter_upwards [eventually_range_subset hR hR₀] with k hk s hs1 hs2
      exact (hgood k).node_round s (hk s hs1 hs2).1 (hk s hs1 hs2).2
    · intro R₀ hR₀
      filter_upwards [eventually_range_subset hR hR₀] with k hk r h hr1 hr2 hh
      exact (hgood k).guard r h (hk r hr1 hr2).1 (hk r hr1 hr2).2 hh
  · refine ⟨hN2, hNtend, fun k => (hgood k).B_ge_one, hBsub, hd0, hd1, hS0, hS1,
      fun k => ?_, fun k => (st k).m, fun k => (st k).n, fun k => (st k).X,
      fun k => (st k).Y, fun k => (st k).Z, fun k => (st k).q, fun k => (st k).c,
      fun k => (st k).α, fun k => (st k).π₀, ?_, ?_, ?_, ?_, fun k g => (hgood k).code_good g,
      ?_, fun k => (hgood k).info⟩
    · have hw := ((hgood k).exact.2.1 (st k).sample)
      exact ⟨hw.2.1, hw.2.2.1, fun g => ((hgood k).sigma_le g Set.univ).trans
        (mu_univ_le_one' (hgood k).exact _ g)⟩
    · intro k
      have := (hgood k).m_ge
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact_mod_cast (show (1 : ℝ) ≤ (st k).m by linarith)
    · apply tendsto_atTop_mono (fun k => (hgood k).m_ge)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    · exact fun k => ⟨(hgood k).α_pos, (hgood k).α_two⟩
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
      · exact fun k => (hgood k).α_pos.le
      · exact fun k => (hgood k).α_le
    · intro R₀ hR₀
      filter_upwards [eventually_range_subset hR hR₀] with k hk g b hb1 hb2 e
      exact (hgood k).frostman g b (hk b hb1 hb2).1 (hk b hb1 hb2).2 e

end

end Submission.Obl.k4_scalar_guarded_entropic_path
