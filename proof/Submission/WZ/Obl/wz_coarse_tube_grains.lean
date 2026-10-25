-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_coarse_tube_grains.Wrap
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_coarse_tube_grains`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_coarse_tube_grains`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_coarse_tube_grains/`
belong to this obligation.
-/

theorem WangZahlLot.wz_coarse_tube_grains : (∀ε:ℝ,0<ε→∃K:ℝ,1≤K∧∀δ:ℝ,0<δ→δ≤1→∀E:Set LeanEval.Analysis.WangZahlKakeya.Space,MeasurableSet E→ E⊆Metric.ball (0:LeanEval.Analysis.WangZahlKakeya.Space) 1→∃(L:ℕ)(Q:Fin L→ MvPolynomial (Fin 3) ℝ)(z:Fin L→ LeanEval.Analysis.WangZahlKakeya.Space)(G:Fin L→ Set LeanEval.Analysis.WangZahlKakeya.Space),(∀j,Q j≠0∧((Q j).totalDegree:ℝ)≤K∧MeasurableSet (G j)∧G j⊆E∧G j⊆Metric.thickening (100*δ) {p:LeanEval.Analysis.WangZahlKakeya.Space|MvPolynomial.eval (fun i=>p i) (Q j)=0}∧G j⊆Metric.closedBall (z j) (K*δ^(-ε)*(L:ℝ)^(-(1/3:ℝ))))∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧ENNReal.ofReal (K⁻¹*δ^ε)*MeasureTheory.volume E≤∑j,MeasureTheory.volume (G j)∧(∀j,ENNReal.ofReal (K⁻¹*δ^ε/L)*MeasureTheory.volume E≤MeasureTheory.volume (G j)∧MeasureTheory.volume (G j)≤ENNReal.ofReal (K*δ^(-ε)/L)*MeasureTheory.volume E)∧∀p u:LeanEval.Analysis.WangZahlKakeya.Space,‖u‖=1→(({j|(Metric.thickening δ (segment ℝ p (p+u))∩G j).Nonempty}.ncard:ℝ)≤K*δ^(-ε)*(L:ℝ)^(1/3:ℝ)))→(∀β τ ε:ℝ,0<β→0<τ→0<ε→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ ENNReal)(ι:V→ Fin 3→ℝ)(M:Set V→ Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j))) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet) := by
  intro _
  exact WangZahlLot.Obl.wz_coarse_tube_grains.tube_grains_frozen
