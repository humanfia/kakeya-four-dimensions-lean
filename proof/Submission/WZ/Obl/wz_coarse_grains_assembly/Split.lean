-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Split.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs

/-!
# The single-coarse-tube grains theorem (hypothesis of o178)

`TubeGrains` is the conclusion of the sibling obligation `wz_coarse_tube_grains` (o177):
Wang–Zahl Proposition 7.15 inside one coarse tube, in the frozen geometry.  The body of this
statement (after its bindings `O q T X P`) is the extra hypothesis of o178.  (Statement from
x0426's `Split.lean` on o151.)
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- Wang–Zahl, Proposition 7.15 inside one coarse tube, in the frozen geometry, with a
prescribed grain length. -/
def TubeGrains : Prop :=
  ∀β τ ε:ℝ,0<β→0<τ→0<ε→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ ENNReal)(ι:V→ Fin 3→ℝ)(M:Set V→ Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j))) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet

end WangZahlLot.Obl.wz_coarse_grains_assembly
