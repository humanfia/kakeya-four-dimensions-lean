-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_move_one.Split.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_move_one.Child

/-!
# The split of o151 into three children

* `PolyPartition` (child `wz_polynomial_grains_partition`): Wang–Zahl, Proposition A.4, the
  polynomial-partitioning grains decomposition of a measurable set `E ⊆ B(0,1)`: disjoint pieces
  `G j ⊆ E`, each in the `100 δ`-neighbourhood of the zero set of a nonzero polynomial of
  degree `≤ K` and in a ball of radius `K δ^(-ε) L^(-1/3)`, carrying comparable shares of `|E|`
  (total `≥ K⁻¹ δ^ε |E|`), and every `δ`-tube meets `≤ K δ^(-ε) L^(1/3)` pieces.
* `TubeGrains` (child `wz_coarse_tube_grains`, stated as `PolyPartition → TubeGrains`):
  Proposition 7.15 rescaled into one coarse tube `T ρ y w` (Corollary 7.17 for one fibre), in
  the frozen geometry: a dense, broad fibre of `δ`-tubes inside `T (ρ/2) y w` (of an essentially
  distinct family) has at least `4 δ^ε (ρ/δ)` tubes, and for every prescribed length `c` with
  `δ^(1-τ)/ρ ≤ c ≤ δ^ε (ρ/δ)/#F` it has a broad refinement with uniform multiplicity carrying
  exact grains `P (16 δ) (ρ c) c` inside `T ρ y w`, crossed end to end by their tubes.
* `AsmStmt` (child `wz_coarse_grains_assembly`): Corollary 7.17 for a whole broad cover, in the
  frozen predicates, assuming the body of `TubeGrains` (stated inside the same frozen context,
  to keep the type short) and an admissible family without the unused Katz–Tao clause.

`childGrains_of_children` gives x0417's `ChildGrains`, from which `frozen_of_child`
(`Child.lean`, `Glue.lean`) proves o151.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_move_one

/-- Wang–Zahl, Proposition A.4 (frozen form): the polynomial-partitioning grains
decomposition. -/
def PolyPartition : Prop :=
  ∀ε:ℝ,0<ε→∃K:ℝ,1≤K∧∀δ:ℝ,0<δ→δ≤1→∀E:Set LeanEval.Analysis.WangZahlKakeya.Space,MeasurableSet E→ E⊆Metric.ball (0:LeanEval.Analysis.WangZahlKakeya.Space) 1→∃(L:ℕ)(Q:Fin L→ MvPolynomial (Fin 3) ℝ)(z:Fin L→ LeanEval.Analysis.WangZahlKakeya.Space)(G:Fin L→ Set LeanEval.Analysis.WangZahlKakeya.Space),(∀j,Q j≠0∧((Q j).totalDegree:ℝ)≤K∧MeasurableSet (G j)∧G j⊆E∧G j⊆Metric.thickening (100*δ) {p:LeanEval.Analysis.WangZahlKakeya.Space|MvPolynomial.eval (fun i=>p i) (Q j)=0}∧G j⊆Metric.closedBall (z j) (K*δ^(-ε)*(L:ℝ)^(-(1/3:ℝ))))∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧ENNReal.ofReal (K⁻¹*δ^ε)*MeasureTheory.volume E≤∑j,MeasureTheory.volume (G j)∧(∀j,ENNReal.ofReal (K⁻¹*δ^ε/L)*MeasureTheory.volume E≤MeasureTheory.volume (G j)∧MeasureTheory.volume (G j)≤ENNReal.ofReal (K*δ^(-ε)/L)*MeasureTheory.volume E)∧∀p u:LeanEval.Analysis.WangZahlKakeya.Space,‖u‖=1→(({j|(Metric.thickening δ (segment ℝ p (p+u))∩G j).Nonempty}.ncard:ℝ)≤K*δ^(-ε)*(L:ℝ)^(1/3:ℝ))

/-- Wang–Zahl, Proposition 7.15 inside one coarse tube, in the frozen geometry, with a
prescribed grain length. -/
def TubeGrains : Prop :=
  ∀β τ ε:ℝ,0<β→0<τ→0<ε→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ ENNReal)(ι:V→ Fin 3→ℝ)(M:Set V→ Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j))) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet

/-- Corollary 7.17 for a broad cover, from the single-tube theorem (frozen form). -/
def AsmStmt : Prop :=
  ∀σ ω ζ:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→0<ζ→ζ≤ω/1000→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀U,U=(fun(d h ρ:ℝ)(n N:ℕ)(v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(f:Fin n→Fin N)=>∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})→(∀β τ ε:ℝ,0<β→0<τ→0<ε→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j)))→∀ε:ℝ,0<ε→ε≤ζ/100→∃α κ θ d₀:ℝ,0<α∧0<κ∧0<θ∧θ≤ε∧0<d₀∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ θ (δ^(-θ)) n x v Y→∀ρ:ℝ,δ^(1-ω/100)≤ρ→ρ≤1→∀S Z N y w f,C δ θ n x v Y S Z ρ N y w f True→U δ θ ρ n N v S Z f→δ/ρ≤δ^ζ*(ρ/δ)*N/n→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ' S' Z' N' y' w' f' a c g,ρ≤ρ'∧C δ ε n x v Y S' Z' ρ' N' y' w' f' True∧0<g∧U δ ε ρ' n N' v S' Z' f'∧H δ ε n x v S' Z' ρ' N' y' w' f' a c 0 g∧δ^ε*(ρ/δ)*N/n≤c) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet

set_option maxHeartbeats 1000000 in
/-- The three children give `ChildGrains`. -/
theorem childGrains_of_children (h1 : PolyPartition) (h2 : PolyPartition → TubeGrains)
    (h3 : AsmStmt) : ChildGrains := by
  have htg := h2 h1
  intro σ ω ζ hσ hσ2 hω hω1 hζ hζ1 O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP C hC
    H hH U hU
  subst hO hq hI hT hQ hX hK hF hA hP hC hH hU
  intro ε hε hεle
  obtain ⟨α, κ, θ, d₀, hα, hκ, hθ, hθε, hd₀, hmain⟩ :=
    h3 σ ω ζ hσ hσ2 hω hω1 hζ hζ1 _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
      _ rfl _ rfl (fun β τ ε' hβ hτ hε' => htg β τ ε' hβ hτ hε' _ rfl _ rfl _ rfl _ rfl _ rfl)
      ε hε hεle
  refine ⟨α, κ, θ, d₀, hα, hκ, hθ, hθε, hd₀, ?_⟩
  intro δ hδ hδd n x v Y hA
  exact hmain δ hδ hδd n x v Y ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.2⟩

end WangZahlLot.Obl.wz_broad_grains_move_one
