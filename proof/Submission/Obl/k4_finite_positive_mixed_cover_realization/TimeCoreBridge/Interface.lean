-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/Interface.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Interface.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Interface.lean.

import Mathlib
import Submission.Lib.K4XInterface.Basic

set_option linter.unusedVariables false

/-! Named versions of the immediately applied lambdas in the frozen statement. -/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

noncomputable section

abbrev x := Submission.Lib.K4XInterface.gx

abbrev y := Submission.Lib.K4XInterface.gy

abbrev v := Submission.Lib.K4XInterface.gv

abbrev δ := Submission.Lib.K4XInterface.gδ

abbrev obs := Submission.Lib.K4XInterface.gobs

abbrev fmt := Submission.Lib.K4XInterface.gfmt

abbrev chart := Submission.Lib.K4XInterface.gchart

def prob : (ℕ→ ℝ)→ (ℕ→ ℝ)→ ℝ→ ℝ→ ℝ→ ℝ→ (W:ℕ→ ℕ)→ ((k:ℕ)→ Fin (W k)→ ℝ)→ ((k:ℕ)→ Fin (W k)→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ)))→ ((k:ℕ)→ Fin (W k)→ Set ((ℕ×(Fin 6→ ℝ))×ℝ))→ ((k:ℕ)→ Fin (W k)→ MvPolynomial (Fin 4) ℝ)→ ((k:ℕ)→ Fin (W k)→ ℝ)→ (ℝ→ ℝ)→ ((k:ℕ)→ Fin (W k)→ ℝ→ (EuclideanSpace ℝ (Fin 3)×ℤ)→ ENNReal)→ ((k:ℕ)→ Fin (W k)→ ℝ→ ((EuclideanSpace ℝ (Fin 3)×ℤ)×(Fin 2→ ℤ))→ ENNReal)→ Prop :=
  fun N K L d S η W ω ν E P B f g G=>(∀ k,2 ≤ N k)∧
    Filter.Tendsto N Filter.atTop Filter.atTop∧
    ((∀ k,1 ≤ K k)∧
    ∀ ε:ℝ,0 < ε→
    ∀ᶠ k in Filter.atTop,K k ≤ N k^ε)∧
    0 < L∧
    0 < d∧
    d < 1∧
    0 < S∧
    0 < η∧
    (fun μ:(k:ℕ)→ Fin (W k)→ MeasureTheory.Measure ((ℕ×(Fin 6→ ℝ))×ℝ)=>(∃ M D:ℕ,∀ k,(W k:ℝ) ≤ N k^M∧
    (∀ γ,0 ≤ ω k γ)∧
    (∑ γ,ω k γ)=1∧
    (∀ γ,MeasureTheory.IsProbabilityMeasure (ν k γ)∧
    0 < B k γ∧
    B k γ ≤ N k^M∧
    (B k γ)⁻¹ ≤ N k^M∧
    (P k γ).totalDegree ≤ 2∧
    (∀ b, |(P k γ).coeff b| ≤ N k^M)∧
    (∃ m:ℕ,(m:ℝ) ≤ N k^M∧
    ∃ (c:Fin m→ ℝ) (i:Fin m→ ℕ) (A:Fin m→ Set (Fin 6→ ℝ)),(∀ j,0 ≤ c j∧
    c j ≤ N k^M∧
    (i j:ℝ) ≤ N k^M∧
    (fmt 6 (N k^M) D (A j))∧
    (∀ x ∈ A j,∀ b, |x b| ≤ N k^M))∧
    ν k γ=∑ j,(ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x=>(i j,x)) (MeasureTheory.volume.restrict (A j)))∧
    MeasurableSet (E k γ)∧
    E k γ ⊆ Set.univ×ˢ Set.Icc (0:ℝ) 1∧
    (∀ p ∈ E k γ,(p.1.1:ℝ) ≤ N k^M∧
    ∀ e, |p.1.2 e| ≤ N k^M)∧
    (∀ i,(fmt 7 (N k^M) D ({x₁:Fin 7→ ℝ | ((i,fun j₁:Fin 6=>x₁ j₁.castSucc),x₁ 6) ∈ (E k γ)})))∧
    (∀ᵐ l ∂ν k γ,∀ t ∈ Set.Icc (0:ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k∧
     |MvPolynomial.eval (x l t) (P k γ)| ≤ K k∧
     |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (P k γ))| ≤ K k*B k γ∧
     |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k γ)))| ≤ K k*(B k γ)^2)∧
    (∀ᵐ p ∂(μ k γ),B k γ/K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k γ))|))∧
    ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) Set.univ)∧
    (∀ k γ r,0 ≤ r→ r ≤ L→ Measurable (g k γ r)∧
    MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ)=(MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r))∧
    (∀ k γ u,0 < u→ u ≤ η*L→ Measurable (G k γ u)∧
    MeasureTheory.Measure.map (fun p:((ℕ×(Fin 6→ ℝ))×ℝ)=>((obs (B k γ) (δ (N k) L)) p,fun j:Fin 2=>⌊(v p.1) j/(δ (N k) u)⌋)) (μ k γ)=((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u))∧
    (∀ r s:ℝ,0 ≤ r→ r ≤ s→ s ≤ L→ 0 ≤ f s - f r∧
    f s - f r ≤ s - r)∧
    (∀ r τ:ℝ,0 ≤ r→ r ≤ L→ 0 < τ→ ∃ c:ℝ,0 < c∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k^(-f r - τ))∨ENNReal.ofReal (N k^(-f r+τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k^(-c)))∧
    (∀ r:ℝ,0 ≤ r→ r ≤ L→ f L - f r ≤ d*(L - r))∧
    (∀ u τ:ℝ,0 < u→ u ≤ η*L→ 0 < τ→ ∃ c:ℝ,0 < c∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) {p | ENNReal.ofReal (N k^(-f L - S*u+τ)) < G k γ u ((fun p:((ℕ×(Fin 6→ ℝ))×ℝ)=>((obs (B k γ) (δ (N k) L)) p,fun j:Fin 2=>⌊(v p.1) j/(δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k^(-c)))) (fun k γ=>((ν k γ).prod MeasureTheory.volume).restrict (E k γ))

def path : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ)))→ (Fin W→ Set ((ℕ×(Fin 6→ ℝ))×ℝ))→ (Fin W→ ℝ)→ (ℝ→ ℝ)→ ℝ→ ℕ→ (ℕ→ ℝ)→ ℝ→ ℕ→ ℕ→ ℝ→ (ℕ→ ℝ)→ (ℕ→ ℕ)→ (ℕ→ ℝ)→ ℝ→ (C:ℕ)→ (Fin C→ ℕ)→ (Fin C→ Fin C)→ (Fin C→ Fin W)→ (Fin C→ ℕ)→ (Fin C→ EuclideanSpace ℝ (Fin 2))→ (Fin C→ EuclideanSpace ℝ (Fin 2))→ (Fin C→ Matrix (Fin 2) (Fin 2) ℝ)→ (Fin C→ MvPolynomial (Fin 4) ℝ)→ (Fin C→ Set (ℕ×(Fin 6→ ℝ)))→ (Fin C→ Set ((ℕ×(Fin 6→ ℝ))×ℝ))→ (ℕ→ Fin W→ (EuclideanSpace ℝ (Fin 3)×ℤ)→ Finset (Fin C))→ Prop :=
  fun Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst=>(1 ≤ κ)∧
    (κ ≤ Nk^σ)∧
    ((C:ℝ) ≤ Nk^Mp)∧
    (r (m - 1)=L)∧
    ((∀ i,i < m→ |r i - s i*L| ≤ δ₀*L∧
    0 < r i∧
    Nk^((κ₁*s i - δ₀)*L) ≤ (2:ℝ)^T i∧
    (2:ℝ)^T i ≤ Nk^((κ₁*s i+δ₀)*L)∧
     True∧
    ENNReal.ofReal κ⁻¹ ≤ ∑ b,if lev b=i then ENNReal.ofReal (ω (γ b))*((ν (γ b)).prod MeasureTheory.volume) (F b) else 0))∧
    ((∀ i γ₁ o,((lst i γ₁ o).card:ℝ) ≤ κ))∧
    ((∀ b b',b ≠ b'→ lev b=lev b'→ γ b=γ b'→ j b=j b'→ Disjoint (A b) (A b')))∧
    ((∀ b,lev b < m∧
    j b < 2^T (lev b)∧
    chart (Nk) Mp Dp κ (T (lev b)) (j b:ℝ) (r (lev b)) (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (Nk^(-f (r (lev b)))* |Matrix.det (Q b)| /((2:ℝ)^T (lev b)*κ)) ≤ ((ν (γ b)).prod MeasureTheory.volume) (F b)∧
    ν (γ b) (A b) ≤ ENNReal.ofReal (κ*Nk^(-f (r (lev b)))* |Matrix.det (Q b)|)∧
    Nk^(-(nw (lev b)+δ₀*L)) ≤ |Matrix.det (Q b)| *(4:ℝ)^T (lev b)∧
     |Matrix.det (Q b)| *(4:ℝ)^T (lev b) ≤ Nk^(-(nw (lev b) - δ₀*L))∧
    (∀ p ∈ F b,b ∈ lst (lev b) (γ b) (obs (B (γ b)) (δ (Nk) (r (lev b))) p))∧
    (0 < lev b→ lev (par b)+1=lev b∧
    γ (par b)=γ b∧
    A b ⊆ A (par b)∧
    F b ⊆ F (par b)∧
    (j (par b):ℝ)/(2:ℝ)^T (lev (par b)) ≤ (j b:ℝ)/(2:ℝ)^T (lev b)∧
    ((j b:ℝ)+1)/(2:ℝ)^T (lev b) ≤ ((j (par b):ℝ)+1)/(2:ℝ)^T (lev (par b))))))

def greedyCover : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ)))→ (Fin W→ ℝ)→ ℝ→ ℝ→ ℝ→ ℕ→ (ℕ→ ℝ)→ (ℕ→ ℕ)→ (C:ℕ)→ (Fin C→ ℕ)→ (Fin C→ Fin W)→ (Fin C→ ℕ)→ (Fin C→ Set (ℕ×(Fin 6→ ℝ)))→ (Fin C→ Set ((ℕ×(Fin 6→ ℝ))×ℝ))→ ℕ→ ℕ→ ℝ→ Prop :=
  fun (Nk L:ℝ) (W:ℕ) (ω:Fin W→ ℝ) (ν:Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ))) (B:Fin W→ ℝ) (d₁ ρ gain:ℝ) (m:ℕ) (r:ℕ→ ℝ) (T:ℕ→ ℕ) (C:ℕ) (lev:Fin C→ ℕ) (γ:Fin C→ Fin W) (j:Fin C→ ℕ) (A:Fin C→ Set (ℕ×(Fin 6→ ℝ))) (F:Fin C→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (Mg Dg:ℕ) (ε:ℝ)=>∃ (i:ℕ) (h:ℝ) (n:ℕ) (old:Fin n→ Fin C) (R':Fin n→ MvPolynomial (Fin 4) ℝ) (A':Fin n→ Set (ℕ×(Fin 6→ ℝ))) (V:Fin n→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)),i < m∧
    gain ≤ h∧
    h ≤ 1/8∧
    (∃ z:ℕ,h=gain+(z:ℝ)*(ρ*gain))∧
    r i+2*h*L ≤ L∧
    (n:ℝ) ≤ Nk^Mg∧
    (∀ a,lev (old a)=i∧
    0 < ν (γ (old a)) (A (old a))∧
    (R' a).totalDegree ≤ 2∧
    (∀ e, |(R' a).coeff e| ≤ Nk^Mg)∧
    MeasurableSet (A' a)∧
    A' a ⊆ A (old a)∧
    (∀ q,fmt 6 (Nk^Mg) Dg {z | (q,z) ∈ A' a})∧
    (∀ l ∈ A' a,∀ t ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i), |MvPolynomial.eval (x l t) (R' a)| ≤ Nk^(4*ρ*gain*L+4*ε)*δ Nk (r i+h*L)∧
     |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (R' a))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))∧
     |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (R' a)))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))^2/δ Nk (r i+h*L))∧
    MeasurableSet (V a)∧
    V a ⊆ {p | (∃ b:Fin C,lev b=m - 1∧
    γ b=γ (old a)∧
    p ∈ F b)∧
    p.1 ∈ A' a∧
    p.2 ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i)∧
    B (γ (old a))/Nk^(4*ρ*gain*L+4*ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (R' a))|}∧
    ENNReal.ofReal (Nk^(-((d₁*h+4*ρ*gain)*L) - 4*ε)/(2:ℝ)^T i)*ν (γ (old a)) (A (old a)) ≤ ((ν (γ (old a))).prod MeasureTheory.volume) (V a))∧
    (∀ a a',a ≠ a'→ old a=old a'→ Disjoint (A' a) (A' a'))∧
    (∀ b:Fin C,((Finset.univ.filter (fun a=>old a=b)).card:ℝ) ≤ Nk^((d₁*h+4*ρ*gain)*L+4*ε))∧
    (∀ a a',a ≠ a'→ γ (old a)=γ (old a')→ Disjoint (V a) (V a'))∧
    ENNReal.ofReal (Nk^(-ε)) ≤ ∑ a,ENNReal.ofReal (ω (γ (old a)))*((ν (γ (old a))).prod MeasureTheory.volume) (V a)

def preImprovementAt : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ)))→ (Fin W→ Set ((ℕ×(Fin 6→ ℝ))×ℝ))→ (Fin W→ ℝ)→ ℝ→ ℝ→ ℕ→ (ℕ→ ℝ)→ (ℕ→ ℕ)→ (ℕ→ ℝ)→ ℕ→ ℕ→ ℝ→ Prop :=
  fun (Nk L:ℝ) (W:ℕ) (ω:Fin W→ ℝ) (ν:Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ))) (E:Fin W→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (B:Fin W→ ℝ) (κ₁ Δ:ℝ) (m:ℕ) (r:ℕ→ ℝ) (T:ℕ→ ℕ) (nw:ℕ→ ℝ) (M D:ℕ) (ε:ℝ)=>∃ (r₂:ℝ) (T₂ C₂:ℕ) (γ₂:Fin C₂→ Fin W) (j₂:Fin C₂→ Fin (2^T₂)) (c₂ u₂:Fin C₂→ EuclideanSpace ℝ (Fin 2)) (Q₂:Fin C₂→ Matrix (Fin 2) (Fin 2) ℝ) (R₂:Fin C₂→ MvPolynomial (Fin 4) ℝ) (A₂:Fin C₂→ Set (ℕ×(Fin 6→ ℝ))) (F₂:Fin C₂→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (lst₂:Fin W→ (EuclideanSpace ℝ (Fin 3)×ℤ)→ Finset (Fin C₂)),r₂+Δ*L ≤ L∧
    ((Δ*L ≤ r₂∧
    (2:ℝ)^T₂ ≤ Nk^(κ₁*Δ*L/2))∨∃ i,i < m∧
    r i+Δ*L ≤ r₂∧
    (2:ℝ)^T₂ ≤ (2:ℝ)^T i*Nk^(κ₁*Δ*L/2))∧
    (C₂:ℝ) ≤ Nk^M∧
    (∀ b b',b ≠ b'→ γ₂ b=γ₂ b'→ j₂ b=j₂ b'→ Disjoint (A₂ b) (A₂ b'))∧
    (∀ w o,((lst₂ w o).card:ℝ) ≤ Nk^ε)∧
    (∀ w b,MeasurableSet {o | b ∈ lst₂ w o})∧
    (∀ b,chart Nk M D (Nk^ε) T₂ ((j₂ b:ℕ):ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True)∧
    ENNReal.ofReal (Nk^(-ε)) ≤ ∑ b,ENNReal.ofReal (ω (γ₂ b))*((ν (γ₂ b)).prod MeasureTheory.volume) {p | p ∈ F₂ b∧
    b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)}

def localGraph : Prop :=
  ∀ D:ℕ,∀ d₀:ℝ,0 ≤ d₀→ d₀ < 1→ ∃ ε₀:ℝ,0 < ε₀∧
    ∃ R₀:ℝ,2 ≤ R₀∧
    ∀ R M ε:ℝ,R₀ ≤ R→ 0 < M→ 0 < ε→ ε ≤ ε₀→
    ∀ n₁ n₂:ℕ,∀ (f₁:Fin n₁→ EuclideanSpace ℂ (Fin 3)→ ℂ) (f₂:Fin n₂→ EuclideanSpace ℂ (Fin 3)→ ℂ) (P₁:Fin n₁→ MvPolynomial (Fin 4) ℂ) (P₂:Fin n₂→ MvPolynomial (Fin 4) ℂ) (f₀:EuclideanSpace ℝ (Fin 3)→ ℂ) (π₁:Fin n₁→ ℝ) (π₂:Fin n₂→ ℝ) (μ:MeasureTheory.Measure ((Fin n₁×Fin n₂)×EuclideanSpace ℝ (Fin 3))),(fun emb:EuclideanSpace ℝ (Fin 3)→ EuclideanSpace ℂ (Fin 3)=>(n₁:ℝ) ≤ R^(d₀+ε)→ (n₂:ℝ) ≤ R^(d₀+ε)→ (∀ i,P₁ i ≠ 0∧
    (P₁ i).totalDegree ≤ D∧
    DifferentiableOn ℂ (f₁ i) (Metric.ball 0 4)∧
    (∀ z ∈ Metric.ball (0:EuclideanSpace ℂ (Fin 3)) 4,MvPolynomial.eval (Fin.snoc (fun j:Fin 3=>z j) (f₁ i z)) (P₁ i)=0)∧
    ∀ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1→ (f₁ i (emb x)).im=0∧
     ‖f₁ i (emb x) - f₀ x‖ ≤ M*R^ε)→ (∀ i,P₂ i ≠ 0∧
    (P₂ i).totalDegree ≤ D∧
    DifferentiableOn ℂ (f₂ i) (Metric.ball 0 4)∧
    (∀ z ∈ Metric.ball (0:EuclideanSpace ℂ (Fin 3)) 4,MvPolynomial.eval (Fin.snoc (fun j:Fin 3=>z j) (f₂ i z)) (P₂ i)=0)∧
    ∀ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1→ (f₂ i (emb x)).im=0∧
     ‖f₂ i (emb x) - f₀ x‖ ≤ M*R^ε)→ (∀ i,0 ≤ π₁ i)→ (∀ i,0 ≤ π₂ i)→ (∑ i,π₁ i)=1→ (∑ i,π₂ i)=1→ ENNReal.ofReal (R^(-ε)) ≤ μ Set.univ→ μ Set.univ ≤ 1→ (∀ (i:Fin n₁) (U:Set (EuclideanSpace ℝ (Fin 3))),MeasurableSet U→ μ {p | p.1.1=i∧
    p.2 ∈ U} ≤ ENNReal.ofReal (R^ε*π₁ i)*MeasureTheory.volume U)→ (∀ (i:Fin n₂) (U:Set (EuclideanSpace ℝ (Fin 3))),MeasurableSet U→ μ {p | p.1.2=i∧
    p.2 ∈ U} ≤ ENNReal.ofReal (R^ε*π₂ i)*MeasureTheory.volume U)→ ¬ μ {p | ‖p.2‖ ≤ (1:ℝ)/2∧
     ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M*R^(-1+ε)∧
    ∃ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1:ℝ)/2∧
    M*R^(-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}ᶜ=0) (fun x=>WithLp.toLp 2 (fun i=>(x i:ℂ)))

def algebraicJets : Prop :=
  ∀ D:ℕ,1 ≤ D→ ∃ K:ℕ,1 ≤ K∧
    ∃ V:Finset (EuclideanSpace ℝ (Fin 3)),(∀ v ∈ V, ‖v‖ =1)∧
    ∃ c:ℝ,0 < c∧
    ∃ B:ℕ→ ℝ,(∀ m,0 < B m)∧
    ∀ (f:EuclideanSpace ℂ (Fin 3)→ ℂ) (P:MvPolynomial (Fin 4) ℂ),P ≠ 0→ P.totalDegree ≤ D→ DifferentiableOn ℂ f (Metric.ball 0 4)→ (∀ z ∈ Metric.ball (0:EuclideanSpace ℂ (Fin 3)) 4,MvPolynomial.eval (Fin.snoc (fun j:Fin 3=>z j) (f z)) P=0)→ (fun emb:EuclideanSpace ℝ (Fin 3)→ EuclideanSpace ℂ (Fin 3)=>(∀ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1→ (f (emb x)).im=0)→ (∀ A:ℝ,0 < A→ (∀ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1→ ‖f (emb x)‖ ≤ A)→
    ∀ v ∈ V,∀ m:ℕ,m ≤ K→ |iteratedDeriv m (fun t:ℝ=>(f (emb (t • v))).re) 0| ≤ B m*A)∧
    ∀ x:EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1/2→ c* ‖f (emb x)‖ ≤ ∑ v ∈ V,∑ j ∈ Finset.range (K+1), |iteratedDeriv j (fun t:ℝ=>(f (emb (t • v))).re) 0|) (fun x=>WithLp.toLp 2 (fun j=>(x j:ℂ)))

def stableSheets : Prop :=
  ∃ C:ℕ,20 ≤ C∧
    ∀ (A a_fit a:ℝ),2 ≤ A→ 0 < a_fit→
    ∀ (b c:MvPolynomial (Fin 3) ℝ),b.totalDegree ≤ 1→ c.totalDegree ≤ 2→ (∀ e, |(b*b - MvPolynomial.C (4*a)*c).coeff e| ≤ A)→ |a| *a_fit ≤ A^(-20:ℝ)→
    ∀ (u₀:EuclideanSpace ℝ (Fin 3)) (w₀:ℝ), ‖u₀‖ ≤ A→ |a*w₀^2+MvPolynomial.eval (fun j=>u₀ j) b*w₀+MvPolynomial.eval (fun j=>u₀ j) c| ≤ a_fit*A→ A^(-1:ℝ) ≤ |2*a*w₀+MvPolynomial.eval (fun j=>u₀ j) b| → |2*a*w₀+MvPolynomial.eval (fun j=>u₀ j) b| ≤ A→ ∃ f:EuclideanSpace ℂ (Fin 3)→ ℂ,DifferentiableOn ℂ f (Metric.ball (WithLp.toLp 2 (fun j=>(u₀ j:ℂ))) (A^(-(C:ℝ))))∧
    (∀ z ∈ Metric.ball (WithLp.toLp 2 (fun j=>(u₀ j:ℂ))) (A^(-(C:ℝ))),(a:ℂ)*(f z)^2+MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j=>z j) b*f z+MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j=>z j) c=0)∧
    (∀ u:EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < A^(-(C:ℝ))→ (f (WithLp.toLp 2 (fun j=>(u j:ℂ)))).im=0∧
    A^(-(C:ℝ)) ≤ |2*a*(f (WithLp.toLp 2 (fun j=>(u j:ℂ)))).re+MvPolynomial.eval (fun j=>u j) b| ∧
     |2*a*(f (WithLp.toLp 2 (fun j=>(u j:ℂ)))).re+MvPolynomial.eval (fun j=>u j) b| ≤ A^(C:ℝ)∧
    0 < (2*a*(f (WithLp.toLp 2 (fun j=>(u j:ℂ)))).re+MvPolynomial.eval (fun j=>u j) b)*(2*a*w₀+MvPolynomial.eval (fun j=>u₀ j) b))∧
    (∀ (u:EuclideanSpace ℝ (Fin 3)) (w:ℝ), ‖u - u₀‖ < A^(-(C:ℝ))→ |a*w^2+MvPolynomial.eval (fun j=>u j) b*w+MvPolynomial.eval (fun j=>u j) c| ≤ a_fit*A→ 0 < (2*a*w+MvPolynomial.eval (fun j=>u j) b)*(2*a*w₀+MvPolynomial.eval (fun j=>u₀ j) b)→ |w - (f (WithLp.toLp 2 (fun j=>(u j:ℂ)))).re| ≤ a_fit*A^(C:ℝ))

def algebraicRemez : Prop :=
  ∀ n D:ℕ,∃ C:ℝ,1 ≤ C∧
    ∀ (P:MvPolynomial (Fin (n+1)) ℂ) (f:EuclideanSpace ℂ (Fin n)→ ℂ),P ≠ 0→ P.totalDegree ≤ D→ DifferentiableOn ℂ f (Metric.ball 0 4)→ (∀ z ∈ Metric.ball (0:EuclideanSpace ℂ (Fin n)) 4,MvPolynomial.eval (Fin.snoc (fun j:Fin n=>z j) (f z)) P=0)→ (∀ x:EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1→ (f (WithLp.toLp 2 (fun j=>(x j:ℂ)))).im=0)→
    ∀ (E:Set (EuclideanSpace ℝ (Fin n))) (θ V:ℝ),MeasurableSet E→ E ⊆ Metric.closedBall 0 (1/2)→ 0 < θ→ θ ≤ 1→ 0 ≤ V→ ENNReal.ofReal θ*MeasureTheory.volume (Metric.closedBall (0:EuclideanSpace ℝ (Fin n)) (1/2)) ≤ MeasureTheory.volume E→ (∀ x ∈ E, ‖f (WithLp.toLp 2 (fun j=>(x j:ℂ)))‖ ≤ V)→
    ∀ x:EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1/2→ ‖f (WithLp.toLp 2 (fun j=>(x j:ℂ)))‖ ≤ C*θ^(-C)*V

def Statement : Prop :=
  localGraph→ algebraicJets→ stableSheets→ algebraicRemez→
    ∀ d₁ κ₁:ℝ,0 ≤ d₁→ d₁ < 1→ 0 < κ₁→ κ₁ ≤ 1→ ∃ α ρ:ℝ,0 < α∧
    α ≤ 1/4∧
    0 < ρ∧
    d₁+ρ < 1∧
    ∀ S η:ℝ,0 < S→ 0 < η→
    ∀ (m:ℕ) (s:ℕ→ ℝ) (gain δ₀:ℝ),(0 < m∧
    0 < s 0∧
    (∀ i,i+1 < m→ s i < s (i+1))∧
    s (m - 1)=1)→ 0 < gain→ gain ≤ 1/8→ 0 < δ₀→ δ₀ ≤ ρ*gain→
    ∀ N K L d W ω ν E P B f g G,prob N K L d S η W ω ν E P B f g G→ (∀ q:ℝ,0 ≤ q→ q ≤ L→ |f q - f 0 - d₁*q| ≤ δ₀*L)→
    ∀ Mp Dp Mg Dg:ℕ,∃ Mi Di:ℕ,∀ ζ:ℝ,0 < ζ→ ζ ≤ 1→ ∃ ε σ:ℝ,0 < ε∧
    ε ≤ 1∧
    ε ≤ ζ∧
    0 < σ∧
    ∃ k₀:ℕ,∀ k,k₀ ≤ k→
    ∀ r T nw κ C lev par γ j c u Q R A F lst,path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst→ greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε→ preImprovementAt (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α*gain) m r T nw Mi Di ζ

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
