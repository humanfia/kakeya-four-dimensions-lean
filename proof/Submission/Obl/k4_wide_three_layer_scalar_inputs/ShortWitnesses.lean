import Submission.Obl.k4_wide_three_layer_scalar_inputs.LayerBridge
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Short

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core

noncomputable section

open scoped Classical

/-- The original three layers viewed over one original true block. All
short domains use the time length of this same coarse depth. -/
structure Context (α : Type) [MeasurableSpace α] where
  cfg : Data α
  k : ℕ
  s : ℝ
  u : ℝ
  v : ℝ
  ε : ℝ
  R : ℝ
  χ : ℝ
  D : ℝ
  K₁ : ℝ
  Mst : ℝ
  layers : ComparedLayers cfg k ε R χ D ![s, s + u, s + v] s u
  i : Fin (cfg.n k s)
  KB : Finset (Fin 3 → ℤ)

namespace Context

variable {α : Type} [MeasurableSpace α] (W : Context α)

abbrev datum := W.layers.comparisonDatum

def q : ℝ := slotLen W.cfg.comparisonData W.k W.s
def t₀ : ℝ := slotStart W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
def g : ℝ := W.cfg.N W.k ^ (-W.cfg.κ * W.s)
def a : ℝ := W.cfg.N W.k ^ (-W.s)
def m : ℝ := W.q * W.g
def ζ : ℝ := W.cfg.N W.k ^ (-W.cfg.e₀)
def E : ℝ := W.cfg.N W.k ^ (W.ε + (10 / (1 - W.cfg.d)) * W.u) * W.a

def coarseValid (x : (↑W.KB) × Fin (W.layers.np 0)) : Prop :=
  pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ 0 x.2
      (W.cfg.j W.k W.s W.i) x.1.1 ∧
  ¬ pairBad W.cfg.comparisonData W.k W.s W.datum W.m W.Mst W.i x.2 x.1.1 ∧
  ∃ l, l ∈ W.cfg.B W.k W.s W.i ∧ l ∈ W.layers.C 0 x.2 ∧
    slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = x.1.1 ∧
    |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ

abbrev Coarse := {x : (↑W.KB) × Fin (W.layers.np 0) // W.coarseValid x}

def key (γ : W.Coarse) : Fin 3 → ℤ := γ.1.1.1
def coarseIndex (γ : W.Coarse) : Fin (W.layers.np 0) := γ.1.2
def chart (γ : W.Coarse) : ℤ × ℤ := (W.key γ 0, W.key γ 1)

def fineValid (γ : W.Coarse) (h : Fin 3) (ih : Fin (W.layers.np h)) : Prop :=
  pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ h ih
      (W.cfg.j W.k W.s W.i) (W.key γ) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
    |MvPolynomial.eval ![t, (W.layers.qp 0 (W.coarseIndex γ) 2 : ℝ) * W.D -
      t * ((W.layers.qp 0 (W.coarseIndex γ) 1 : ℝ) * W.χ) + W.D * w]
        (W.layers.G h ih - W.layers.G 0 (W.coarseIndex γ))| ≤ W.E) ∧
  ∃ l, l ∈ W.layers.C 0 (W.coarseIndex γ) ∧ l ∈ W.layers.C h ih ∧
    slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = W.key γ ∧
    |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ

abbrev Label := {x : W.Coarse × Fin (W.layers.np 1) × Fin (W.layers.np 2) //
  W.fineValid x.1 1 x.2.1 ∧ W.fineValid x.1 2 x.2.2}

def occurrence (x : W.Label) : Set α :=
  {l | l ∈ W.cfg.B W.k W.s W.i ∧ l ∈ W.layers.C 0 (W.coarseIndex x.1.1) ∧
    l ∈ W.layers.C 1 x.1.2.1 ∧ l ∈ W.layers.C 2 x.1.2.2 ∧
    slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = W.key x.1.1}

theorem occurrence_measurable {R' : ℝ}
    (hB : BlocksAt W.cfg.comparisonData W.k W.s R') (hb : Measurable (W.cfg.b W.k))
    (x : W.Label) : MeasurableSet (W.occurrence x) :=
  (hB.sets W.i).2.1.inter ((W.layers.meas 0 _).inter ((W.layers.meas 1 _).inter
    ((W.layers.meas 2 _).inter (measurableSet_slotKey hb _ _ _ _))))

theorem coarse_eq {x y : W.Coarse} (hk : W.key x = W.key y)
    (hi : W.coarseIndex x = W.coarseIndex y) : x = y := by
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hk) hi

theorem occurrence_disjoint (x y : W.Label) (hne : x ≠ y) :
    Disjoint (W.occurrence x) (W.occurrence y) := by
  rw [Set.disjoint_left]
  intro l hx hy
  have hc : W.coarseIndex x.1.1 = W.coarseIndex y.1.1 := by
    by_contra h
    exact Set.disjoint_left.mp (W.layers.disj 0 _ _ h) hx.2.1 hy.2.1
  have h1 : x.1.2.1 = y.1.2.1 := by
    by_contra h
    exact Set.disjoint_left.mp (W.layers.disj 1 _ _ h) hx.2.2.1 hy.2.2.1
  have h2 : x.1.2.2 = y.1.2.2 := by
    by_contra h
    exact Set.disjoint_left.mp (W.layers.disj 2 _ _ h) hx.2.2.2.1 hy.2.2.2.1
  apply hne
  exact Subtype.ext (Prod.ext (W.coarse_eq (hx.2.2.2.2.symm.trans hy.2.2.2.2) hc)
    (Prod.ext h1 h2))

/-- Off the single comparison exception, the actual three original
labels determine an eligible finite witness. -/
theorem occurrence_cover (lam : Measure (α × ℝ)) (hle : lam ≤ W.layers.ρs)
    (hsupp : ∀ᵐ p ∂lam, p.1 ∈ W.cfg.B W.k W.s W.i ∧ p.2 ∈ Icc W.t₀ (W.t₀ + W.q))
    (hhor : ∀ᵐ p ∂lam, |W.cfg.b W.k p.1 4 + W.cfg.b W.k p.1 0| ≤ W.ζ)
    (hkeys : ∀ᵐ p ∂lam, slotKey (W.cfg.b W.k) W.χ W.m W.t₀ p.1 ∈ W.KB)
    (hgood : ∀ᵐ p ∂lam, p ∉ shortBad W.cfg.comparisonData W.k W.s W.datum
      W.m W.K₁ W.Mst W.KB) :
    ∀ᵐ p ∂lam, ∃ x : W.Label, p.1 ∈ W.occurrence x := by
  filter_upwards [ae_mono hle W.layers.cover, ae_mono hle W.layers.agree,
    hsupp, hhor, hkeys, hgood] with p hc ha hs hh hk hg
  obtain ⟨i₀, hi₀⟩ := hc 0
  obtain ⟨i₁, hi₁⟩ := hc 1
  obtain ⟨i₂, hi₂⟩ := hc 2
  have ht : p.2 ∈ W.cfg.comparisonData.I (W.cfg.T W.k W.s) (W.cfg.j W.k W.s W.i) := by
    change p.2 ∈ W.cfg.comparisonData.I (W.cfg.comparisonData.T W.k W.s)
      (W.cfg.comparisonData.j W.k W.s W.i)
    rw [I_eq_slot]
    exact hs.2
  have hshort := short_good W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ W.Mst W.KB
    hg (mem_iUnion.mpr ⟨i₀, hi₀⟩) W.i hs.1 ht hk
  let γ : W.Coarse := ⟨(⟨_, hk⟩, i₀), hshort.2.1 0 i₀ hi₀,
    hshort.2.2 i₀ hi₀, p.1, hs.1, hi₀, rfl, hh⟩
  have hf1 : W.fineValid γ 1 i₁ :=
    ⟨hshort.2.1 1 i₁ hi₁, ha 1 (by decide) i₀ i₁ hi₀ hi₁,
      p.1, hi₀, hi₁, rfl, hh⟩
  have hf2 : W.fineValid γ 2 i₂ :=
    ⟨hshort.2.1 2 i₂ hi₂, ha 2 (by decide) i₀ i₂ hi₀ hi₂,
      p.1, hi₀, hi₂, rfl, hh⟩
  exact ⟨⟨(γ, i₁, i₂), hf1, hf2⟩, hs.1, hi₀, hi₁, hi₂, rfl⟩

end Context

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses
