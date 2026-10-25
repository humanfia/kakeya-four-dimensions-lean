-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Interface.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential

noncomputable section

abbrev Ln := (ℕ × (Fin 6 → ℝ) : Type)

abbrev Ev := (Ln × ℝ : Type)

abbrev P2 := (EuclideanSpace ℝ (Fin 2) : Type)

abbrev P3 := (EuclideanSpace ℝ (Fin 3) : Type)

abbrev P3c := (EuclideanSpace ℂ (Fin 3) : Type)

abbrev Po := (MvPolynomial (Fin 4) ℝ : Type)

abbrev Ob := (P3 × ℤ : Type)

def exf := ((fun (D:ℕ) (f:P3→ ℝ)=>∃(F:P3c→ ℂ) (P:MvPolynomial (Fin 4) ℂ),P≠0∧P.totalDegree≤ D∧ContDiffOn ℂ ⊤ F (Metric.ball 0 4)∧(∀z∈Metric.ball (0:P3c) 4,MvPolynomial.eval (Fin.snoc (fun i:Fin 3=> z i) (F z)) P=0)∧∀x∈Metric.ball (0:P3) 4,F (WithLp.toLp 2 (fun i:Fin 3=> (x i:ℂ)))=(f x:ℂ)) : ℕ→ (P3→ ℝ)→ Prop)

def xp := ((fun (l:Ln) (t:ℝ)=> ![t,l.2 0+t*l.2 3,l.2 1+t*l.2 4,l.2 2+t*l.2 5]) : Ln→ ℝ→ Fin 4→ ℝ)

def mk := (((∀n:ℕ,2≤ n→ n≤ 4→ ∃C:ℝ,0 < C∧∀r:ℝ,0 < r→ ∀(N:Fin n→ ℕ) (a e:(i:Fin n)→ Fin (N i)→ EuclideanSpace ℝ (Fin n)) (w:(i:Fin n)→ Fin (N i)→ ℝ),(∀(i:Fin n) (k:Fin (N i)),‖e i k‖=1)→ (∀(i:Fin n) (k:Fin (N i)),0≤ w i k)→ MeasureTheory.lintegral MeasureTheory.volume (fun x:EuclideanSpace ℝ (Fin n)=> ENNReal.ofReal ((∑ T:((i:Fin n)→ Fin (N i)),|Matrix.det (Matrix.of fun i j:Fin n=> e i (T i) j)| *∏ i:Fin n,(w i (T i)*(Metric.thickening r (Set.range fun t:ℝ=> a i (T i)+t • e i (T i))).indicator (fun _=> (1:ℝ)) x))^((1:ℝ)/((n:ℝ) - 1))))≤ ENNReal.ofReal (C*r^n*∏ i:Fin n,(∑ k:Fin (N i),w i k)^((1:ℝ)/((n:ℝ) - 1))))) : Prop)

def x := ((fun l t=> ![t,l.2 0+t*l.2 3,l.2 1+t*l.2 4,l.2 2+t*l.2 5]) : Ln→ ℝ→ Fin 4→ ℝ)

def y := ((fun l t=> WithLp.toLp 2 ![(x l t) 1,(x l t) 2]) : Ln→ ℝ→ P2)

def v := ((fun l=> WithLp.toLp 2 ![l.2 3,l.2 4]) : Ln→ P2)

def δ := ((fun N r=> (2:ℝ)^(-(⌊r*Real.log N/Real.log 2⌋:ℤ))) : ℝ→ ℝ→ ℝ)

def obs := ((fun B a p=> (WithLp.toLp 2 ![p.2,(x p.1 p.2) 1,(x p.1 p.2) 2],⌊B*(x p.1 p.2) 3/a⌋)) : ℝ→ ℝ→ Ev→ Ob)

def fmt := ((fun n H D A=>∃m₀:ℕ,(m₀:ℝ)≤ H∧∃p₀:Fin m₀→ MvPolynomial (Fin n) ℝ,(∀i₀,(p₀ i₀).totalDegree≤ D)∧∃b₀:(Fin m₀→ Bool)→ Bool,∀x₀,x₀∈A ↔ b₀ (fun i₀=> decide (0≤ MvPolynomial.eval x₀ (p₀ i₀)))=true) : (n:ℕ)→ ℝ→ ℕ→ Set (Fin n→ ℝ)→ Prop)

def ch := ((fun Nk M D κ T j r Bv Ev c u Q R A F ex=> Matrix.det Q≠0∧‖c‖ +‖u‖≤ Nk^M∧(∑ e:Fin 2,∑ e':Fin 2,(|Q e e'| +|Q⁻¹ e e'|))≤ Nk^M∧(∑ e:Fin 2,∑ e':Fin 2,|Q e e'|)≤ κ/(2:ℝ)^T∧R.totalDegree≤ 2∧(∀e,|R.coeff e|≤ Nk^M)∧MeasurableSet A∧MeasurableSet F∧(∀i,fmt 6 (Nk^M) D {x | (i,x)∈A}∧fmt 7 (Nk^M) D {x₁:Fin 7→ ℝ | ((i,fun j₁:Fin 6=> x₁ j₁.castSucc),x₁ 6)∈F})∧(∀l∈A,(l.1:ℝ)≤ Nk^M∧(∀e,|l.2 e|≤ Nk^M)∧∀t∈Set.Icc (j/(2:ℝ)^T) ((j+1)/(2:ℝ)^T),‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖≤ κ∧|MvPolynomial.eval (x l t) R|≤ κ*δ Nk r∧|MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) R)|≤ κ*Bv∧|MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) R))|≤ κ*Bv^2/δ Nk r)∧(∀p∈F,p∈Ev∧p.1∈A∧p.2∈Set.Icc (j/(2:ℝ)^T) ((j+1)/(2:ℝ)^T)∧Bv/κ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) R)|)∧ex) : ℝ→ ℕ→ ℕ→ ℝ→ ℕ→ ℝ→ ℝ→ ℝ→ Set Ev→ P2→ P2→ Matrix (Fin 2) (Fin 2) ℝ→ Po→ Set Ln→ Set Ev→ Prop→ Prop)

def pb := ((fun N K L d S η W ω ν E P B f g G=> (∀k,2≤ N k)∧Filter.Tendsto N Filter.atTop Filter.atTop∧((∀k,1≤ K k)∧∀ε:ℝ,0 < ε→ ∀ᶠ k in Filter.atTop,K k≤ N k^ε)∧0 < L∧0 < d∧d < 1∧0 < S∧0 < η∧(fun μ:(k:ℕ)→ Fin (W k)→ MeasureTheory.Measure Ev=> (∃M D:ℕ,∀k,(W k:ℝ)≤ N k^M∧(∀γ,0≤ ω k γ)∧(∑ γ,ω k γ)=1∧(∀γ,MeasureTheory.IsProbabilityMeasure (ν k γ)∧0 < B k γ∧B k γ≤ N k^M∧(B k γ)⁻¹≤ N k^M∧(P k γ).totalDegree≤ 2∧(∀b,|(P k γ).coeff b|≤ N k^M)∧(∃m:ℕ,(m:ℝ)≤ N k^M∧∃(c:Fin m→ ℝ) (i:Fin m→ ℕ) (A:Fin m→ Set (Fin 6→ ℝ)),(∀j,0≤ c j∧c j≤ N k^M∧(i j:ℝ)≤ N k^M∧(fmt 6 (N k^M) D (A j))∧(∀x∈A j,∀b,|x b|≤ N k^M))∧ν k γ=∑ j,(ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x=> (i j,x)) (MeasureTheory.volume.restrict (A j)))∧MeasurableSet (E k γ)∧E k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1∧(∀p∈E k γ,(p.1.1:ℝ)≤ N k^M∧∀e,|p.1.2 e|≤ N k^M)∧(∀i,(fmt 7 (N k^M) D ({x₁:Fin 7→ ℝ | ((i,fun j₁:Fin 6=> x₁ j₁.castSucc),x₁ 6)∈(E k γ)})))∧(∀ᵐ l ∂ν k γ,∀t∈Set.Icc (0:ℝ) 1,‖(y l t)‖ +‖(v l)‖≤ K k∧|MvPolynomial.eval (x l t) (P k γ)|≤ K k∧|MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (P k γ))|≤ K k*B k γ∧|MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k γ)))|≤ K k*(B k γ)^2)∧(∀ᵐ p ∂(μ k γ),B k γ/K k≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k γ))|))∧ENNReal.ofReal ((K k)⁻¹)≤ ∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) Set.univ)∧(∀k γ r,0≤ r→ r≤ L→ Measurable (g k γ r)∧MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ)=(MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r))∧(∀k γ u,0 < u→ u≤ η*L→ Measurable (G k γ u)∧MeasureTheory.Measure.map (fun p:Ev=> ((obs (B k γ) (δ (N k) L)) p,fun j:Fin 2=> ⌊(v p.1) j/(δ (N k) u)⌋)) (μ k γ)=((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u))∧(∀r s:ℝ,0≤ r→ r≤ s→ s≤ L→ 0≤ f s - f r∧f s - f r≤ s - r)∧(∀r τ:ℝ,0≤ r→ r≤ L→ 0 < τ→ ∃c:ℝ,0 < c∧∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k^(-f r - τ))∨ENNReal.ofReal (N k^(-f r+τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)})≤ ENNReal.ofReal (N k^(-c)))∧(∀r:ℝ,0≤ r→ r≤ L→ f L - f r≤ d*(L - r))∧(∀u τ:ℝ,0 < u→ u≤ η*L→ 0 < τ→ ∃c:ℝ,0 < c∧∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (ω k γ)*(μ k γ) {p | ENNReal.ofReal (N k^(-f L - S*u+τ)) < G k γ u ((fun p:Ev=> ((obs (B k γ) (δ (N k) L)) p,fun j:Fin 2=> ⌊(v p.1) j/(δ (N k) u)⌋)) p)})≤ ENNReal.ofReal (N k^(-c)))) (fun k γ=> ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) : (ℕ→ ℝ)→ (ℕ→ ℝ)→ ℝ→ ℝ→ ℝ→ ℝ→ (W:ℕ→ ℕ)→ ((k:ℕ)→ Fin (W k)→ ℝ)→ ((k:ℕ)→ Fin (W k)→ MeasureTheory.Measure Ln)→ ((k:ℕ)→ Fin (W k)→ Set Ev)→ ((k:ℕ)→ Fin (W k)→ Po)→ ((k:ℕ)→ Fin (W k)→ ℝ)→ (ℝ→ ℝ)→ ((k:ℕ)→ Fin (W k)→ ℝ→ Ob→ ENNReal)→ ((k:ℕ)→ Fin (W k)→ ℝ→ (Ob × (Fin 2→ ℤ))→ ENNReal)→ Prop)

def path := ((fun Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst=> (1≤ κ)∧(κ≤ Nk^σ)∧((C:ℝ)≤ Nk^Mp)∧(r (m - 1)=L)∧((∀i,i < m→ |r i - s i*L|≤ δ₀*L∧0 < r i∧Nk^((κ₁*s i - δ₀)*L)≤ (2:ℝ)^T i∧(2:ℝ)^T i≤ Nk^((κ₁*s i+δ₀)*L)∧|nw i - (0:ℝ)*s i*L|≤ δ₀*L∧ENNReal.ofReal κ⁻¹≤ ∑ b,if lev b=i then ENNReal.ofReal (ω (γ b))*((ν (γ b)).prod MeasureTheory.volume) (F b) else 0))∧((∀i γ₁ o,((lst i γ₁ o).card:ℝ)≤ κ))∧((∀b b',b≠b'→ lev b=lev b'→ γ b=γ b'→ j b=j b'→ Disjoint (A b) (A b')))∧((∀b,lev b < m∧j b < 2^T (lev b)∧ch (Nk) Mp Dp κ (T (lev b)) (j b:ℝ) (r (lev b)) (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (Nk^(-f (r (lev b)))*|Matrix.det (Q b)| /((2:ℝ)^T (lev b)*κ))≤ ((ν (γ b)).prod MeasureTheory.volume) (F b)∧ν (γ b) (A b)≤ ENNReal.ofReal (κ*Nk^(-f (r (lev b)))*|Matrix.det (Q b)|)∧Nk^(-(nw (lev b)+δ₀*L))≤ |Matrix.det (Q b)| *(4:ℝ)^T (lev b)∧|Matrix.det (Q b)| *(4:ℝ)^T (lev b)≤ Nk^(-(nw (lev b) - δ₀*L))∧(∀p∈F b,b∈lst (lev b) (γ b) (obs (B (γ b)) (δ (Nk) (r (lev b))) p))∧(0 < lev b→ lev (par b)+1=lev b∧γ (par b)=γ b∧A b ⊆ A (par b)∧F b ⊆ F (par b)∧(j (par b):ℝ)/(2:ℝ)^T (lev (par b))≤ (j b:ℝ)/(2:ℝ)^T (lev b)∧((j b:ℝ)+1)/(2:ℝ)^T (lev b)≤ ((j (par b):ℝ)+1)/(2:ℝ)^T (lev (par b))))))) : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure Ln)→ (Fin W→ Set Ev)→ (Fin W→ ℝ)→ (ℝ→ ℝ)→ ℝ→ ℕ→ (ℕ→ ℝ)→ ℝ→ ℕ→ ℕ→ ℝ→ (ℕ→ ℝ)→ (ℕ→ ℕ)→ (ℕ→ ℝ)→ ℝ→ (C:ℕ)→ (Fin C→ ℕ)→ (Fin C→ Fin C)→ (Fin C→ Fin W)→ (Fin C→ ℕ)→ (Fin C→ P2)→ (Fin C→ P2)→ (Fin C→ Matrix (Fin 2) (Fin 2) ℝ)→ (Fin C→ Po)→ (Fin C→ Set Ln)→ (Fin C→ Set Ev)→ (ℕ→ Fin W→ Ob→ Finset (Fin C))→ Prop)

def atlas := ((fun Nk L W ω ν E B Mi Di τ r₂ T₂ extra aux massFloor mass=>∃(C₂:ℕ) (γ₂:Fin C₂→ Fin W) (j₂:Fin C₂→ Fin (2^T₂)) (c₂ u₂:Fin C₂→ P2) (Q₂:Fin C₂→ Matrix (Fin 2) (Fin 2) ℝ) (R₂:Fin C₂→ Po) (A₂:Fin C₂→ Set Ln) (F₂:Fin C₂→ Set Ev) (lst₂:Fin W→ Ob→ Finset (Fin C₂)),(C₂:ℝ)≤ Nk^Mi∧(∀b b',b≠b'→ γ₂ b=γ₂ b'→ j₂ b=j₂ b'→ Disjoint (A₂ b) (A₂ b'))∧(∀γ₁ o,((lst₂ γ₁ o).card:ℝ)≤ Nk^τ)∧(∀b,ch Nk Mi Di (Nk^τ) T₂ ((j₂ b:ℕ):ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) (aux (γ₂ b) (j₂ b) (A₂ b) (F₂ b) (∀p∈F₂ b,b∈lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)))∧extra (Q₂ b))∧massFloor≤ ∑ b,ENNReal.ofReal (ω (γ₂ b))*mass (γ₂ b) (F₂ b)) : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure Ln)→ (Fin W→ Set Ev)→ (Fin W→ ℝ)→ ℕ→ ℕ→ ℝ→ ℝ→ (T₂:ℕ)→ (Matrix (Fin 2) (Fin 2) ℝ→ Prop)→ (Fin W→Fin (2^T₂)→Set Ln→Set Ev→Prop→Prop)→ENNReal→(Fin W→Set Ev→ENNReal)→Prop)

def sy := ((fun Nk L W ω ν E B Mi Di τ r₂ T₂ extra=>atlas Nk L W ω ν E B Mi Di τ r₂ T₂ extra (fun _ _ _ _ known=>known) (ENNReal.ofReal (Nk^(-τ))) (fun w F=>((ν w).prod MeasureTheory.volume) F)) : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure Ln)→ (Fin W→ Set Ev)→ (Fin W→ ℝ)→ ℕ→ ℕ→ ℝ→ ℝ→ ℕ→ (Matrix (Fin 2) (Fin 2) ℝ→ Prop)→ Prop)

def wi := ((fun Nk L W ω ν E B m r T nw c Mi Di τ=>∃i,i < m∧r i+2*c*L≤ L∧sy Nk L W ω ν E B Mi Di τ (r i) (T i) (fun Q=> |Matrix.det Q| *(4:ℝ)^T i≤ Nk^(-(nw i+c*L)))) : ℝ→ ℝ→ (W:ℕ)→ (Fin W→ ℝ)→ (Fin W→ MeasureTheory.Measure Ln)→ (Fin W→ Set Ev)→ (Fin W→ ℝ)→ ℕ→ (ℕ→ ℝ)→ (ℕ→ ℕ)→ (ℕ→ ℝ)→ ℝ→ ℕ→ ℕ→ ℝ→ Prop)

def grid := ((fun κ₁ ρ m s gain δ₀ u0 => (0 < m ∧ 0 < s 0 ∧ (∀ i, i+1 < m → s i < s (i+1)) ∧ s (m-1)=1) ∧ 0 < gain ∧ gain ≤ 1/8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ*gain ∧ Even m ∧ 2 ≤ m ∧ (∀ i, s i = ((i:ℝ)+1)/(m:ℝ)) ∧ 1/(m:ℝ) ≤ gain/κ₁ ∧ δ₀ ≤ gain/100 ∧ δ₀ ≤ u0/100 ∧ δ₀ ≤ ρ*gain/100 ∧ 0 < u0 ∧ u0 ≤ 4*gain) : ℝ → ℝ → ℕ → (ℕ → ℝ) → ℝ → ℝ → ℝ → Prop)

def narrow := ((fun Nk L W ω ν E B m s r T nw gain u0 κ Mw Dw α C lev γ j A F H => ∃ (i:ℕ) (β:ℝ), i < m ∧ 1/4 ≤ s i ∧ s i ≤ 1/2 ∧ u0 ≤ β ∧ β ≤ 4*gain ∧ atlas Nk L W ω ν E B Mw Dw α (r i) (T i) (fun Q=> |Matrix.det Q| *(4:ℝ)^T i≤Nk^(-(nw i+β*L))) (fun w jt At Ft known=>known ∧ ∃b:Fin C, lev b=i ∧ γ b=w ∧ j b=(jt:ℕ) ∧ At⊆A b ∧ Ft⊆F b) (ENNReal.ofReal (κ⁻¹/8)) (fun w F=>((ν w).prod MeasureTheory.volume) (F∩H w))) : ℝ → ℝ → (W:ℕ) → (Fin W → ℝ) → (Fin W → MeasureTheory.Measure Ln) → (Fin W→Set Ev)→(Fin W→ℝ)→ℕ→(ℕ→ℝ)→(ℕ→ℝ)→(ℕ→ℕ)→ (ℕ→ℝ)→ℝ→ℝ→ℝ→ℕ→ℕ→ℝ→(C:ℕ)→(Fin C→ℕ)→(Fin C→Fin W)→ (Fin C→ℕ)→(Fin C→Set Ln)→(Fin C→Set Ev)→(Fin W→Set Ev)→Prop)

def JointJetBound := ((fun (D J : ℕ) => ∀ (A : ℝ), 2 ≤ A → ∀ f : P3 → ℝ, exf D f → (∀ (E : Set P3) (v : ℝ), MeasurableSet E → E ⊆ Metric.closedBall 0 1 → ENNReal.ofReal A⁻¹ ≤ MeasureTheory.volume E → 0 ≤ v → (∀ x ∈ E, |f x| ≤ v) → ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Metric.closedBall 0 2, ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * v) ∧ (∀ (c : ℝ) (L : P3 →L[ℝ] ℝ) (ε : ℝ), 0 < ε → (∀ x ∈ Metric.closedBall 0 1, |f x - c - L x| ≤ ε) → ∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ x ∈ Metric.closedBall 0 2, ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * ε)) : ℕ → ℕ → Prop)

def packetBase := ((fun T j c u p => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with | h => (match (((j : ℝ) * h : ℝ)) with | t0 => WithLp.toLp 2 ![(p.2 - t0) / h, ((xp p.1 p.2) 1 - (c 0 + t0 * u 0)) / h, ((xp p.1 p.2) 2 - (c 1 + t0 * u 1)) / h]))) : ℕ → ℕ → P2 → P2 → Ev → P3)

def packetSignal := ((fun P p => MvPolynomial.eval (xp p.1 p.2) P) : Po → Ev → ℝ)

def physicalCode := ((fun z X ε p => (fun i => ⌊z p i / ε⌋, ⌊X p / ε⌋)) : (Ev → P3) → (Ev → ℝ) → ℝ → Ev → ((Fin 3 → ℤ) × ℤ))

def PhysicalPotentialPacket := ((fun q precision loss Nk L d₁ gain κ ν B r T j c u P A F H => (match (δ Nk r) with | a => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with | h => (match (δ Nk (precision * gain * L)) with | ζ => (match (packetBase T j c u) with | z => (match (packetSignal P) with | X => (match ((fun p => X p / a)) with | Xn => (match (ENNReal.ofReal h * ν A) with | ref => ∃ (K ε : ℝ) (S : Set Ev) (Pot : MvPolynomial (Fin 3) ℝ), 0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a / h) * ζ ∧ 0 < a ∧ a ≤ K * h ∧ h ≤ ζ ∧ 2 ≤ K ∧ κ ≤ K ∧ K ≤ Nk ^ (loss * gain * L) ∧ MeasurableSet S ∧ S ⊆ H ∩ F ∧ 0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod MeasureTheory.volume).restrict S) Set.univ ∧ Pot.totalDegree ≤ q ∧ (∀ e, |Pot.coeff e| ≤ K * h) ∧ (∀ p ∈ S, ‖z p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2) ∧ B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)| ∧ (∀ t ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), |(MvPolynomial.eval (xp p.1 t) P - MvPolynomial.eval (fun i => z (p.1, t) i) Pot) - (MvPolynomial.eval (xp p.1 ((j : ℝ) * h)) P - MvPolynomial.eval (fun i => z (p.1, (j : ℝ) * h) i) Pot)| ≤ a * ζ)) ∧ (∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 → ((ν.prod MeasureTheory.volume).restrict S) {p | physicalCode z Xn ε p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤ (1 / 1000000000000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict S) {p | physicalCode z Xn ε p = k}) ∧ (∀ U : Set P3, MeasurableSet U → ((ν.prod MeasureTheory.volume).restrict S) {p | z p ∈ U} ≤ ENNReal.ofReal K * ref * MeasureTheory.volume U) ∧ (∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U → ∀ f : P3 → ℝ, Measurable f → ((ν.prod MeasureTheory.volume).restrict S) {p | z p ∈ U ∧ |Xn p - f (z p)| ≤ w} ≤ ENNReal.ofReal (K * w ^ d₁) * ref * MeasureTheory.volume U) ∧ (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h * p ≤ a * w → Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k} ∧ (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁)))))))))) : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → MeasureTheory.Measure Ln → ℝ → ℝ → ℕ → ℕ → P2 → P2 → Po → Set Ln → Set Ev → Set Ev → Prop)

def PhysicalPotentialDiscoveryTail := ((fun q precision loss d₁ κ₁ S η _ρ m s gain δ₀ u0 => ∀ N K L d W ω ν E P B f g G, pb N K L d S η W ω ν E P B f g G → (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δ₀ * L) → ∀ Mp Dp : ℕ, ∃ M₀ D₀ : ℕ, ∀ Mi Di : ℕ, M₀ ≤ Mi → D₀ ≤ Di → ∀ τ : ℝ, 0 < τ → ∀ α : ℝ, 0 < α → α ≤ 1 → ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst, path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst → ∀ H : Fin (W k) → Set Ev, (∀ w, MeasurableSet (H w) ∧ H w ⊆ {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) → ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) → (wi (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ ∨ narrow (N k) L (W k) (ω k) (ν k) (E k) (B k) m s r T nw gain u0 κ M₀ D₀ α C lev γ j A F H) ∨ ∃ b : Fin C, lev b < m ∧ r (lev b) + 2 * gain * L ≤ L ∧ PhysicalPotentialPacket q precision loss (N k) L d₁ gain κ (ν k (γ b)) (B k (γ b)) (r (lev b)) (T (lev b)) (j b) (c b) (u b) (P k (γ b)) (A b) (F b) (H (γ b))) : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → (ℕ → ℝ) → ℝ → ℝ → ℝ → Prop)

def MainAssertion : Prop := mk → ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 → ∃ q : ℕ, 2 ≤ q ∧ ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧ max 5186 (864 * (2 * (q + 2)) + 2) ≤ D ∧ ∀ J : ℕ, 1 ≤ J → JointJetBound D J → ∀ precision : ℝ, 1 ≤ precision → ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 → ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ), grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧ PhysicalPotentialDiscoveryTail q precision loss d₁ κ₁ S η ρ m s gain δ₀ u0

end

end Submission.Obl.k4_physical_row_packet_potential
