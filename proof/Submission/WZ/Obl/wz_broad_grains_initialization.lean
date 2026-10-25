-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_broad_grains_initialization.LocalCount
import Submission.WZ.Obl.wz_broad_grains_initialization.MassGain
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitCover
import Submission.WZ.Obl.wz_broad_grains_initialization.AngularPartition
import Submission.WZ.Obl.wz_broad_grains_initialization.AngularMax
import Submission.WZ.Obl.wz_broad_grains_initialization.MeasurablePackets
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketPower
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitBroad
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketLabels
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeGeometry
import Submission.WZ.Obl.wz_broad_grains_initialization.EndpointTrim
import Submission.WZ.Obl.wz_broad_grains_initialization.DominantClass
import Submission.WZ.Obl.wz_broad_grains_initialization.DirectionClass
import Submission.WZ.Obl.wz_broad_grains_initialization.SeparatedCubes
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeBudget
import Submission.WZ.Obl.wz_broad_grains_initialization.SparseCells
import Submission.WZ.Obl.wz_broad_grains_initialization.CommonMultiplicity
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainFamily
import Submission.WZ.Obl.wz_broad_grains_initialization.PolynomialCount
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainRefinement
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainState
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitGrains
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketGain
import Submission.WZ.Obl.wz_broad_grains_initialization.Initialization
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_broad_grains_initialization`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_broad_grains_initialization`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_broad_grains_initialization/`
belong to this obligation.
-/

theorem WangZahlLot.wz_broad_grains_initialization : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀D,D=(fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(t:Bool)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧(t=true→ρ≤d^(ω/100)∧d^ζ*(ρ/d)*N/n≤c∧g≤d^(-ζ)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀R,R=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ ρ:ℝ,0<δ→δ≤1/100→δ≤ρ→ρ≤1→∀m l:ℝ,1≤ m→1≤l→∀n(x v:Fin n→V)(Y:Fin n→Set V)(y w:V),0<n→‖w‖=1→(∀i,‖v i‖=1∧T δ (x i) (v i)⊆T ρ y w∧M (Y i)∧Y i⊆T δ (x i) (v i))→X δ n x v→O (δ^η*n*δ^2)≤∑i,μ (Y i)→K δ m n x v→B δ ρ l n 1 x v .univ (fun _=>y) (fun _=>w) (fun _=>0)→O (κ*δ^ε*(δ/ρ)^ω*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ/ρ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ c,D ω ζ δ ε ρ c n x v Y false)→E σ ω→R σ ω→∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→J σ ω ζ ε) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσ2 hω hω1
  intro O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP B hB C hC H hH D hD E hE R hR J hJ
  subst O q I T Q X K F A P B C H D E R J
  intro hEst hRst ζ hζ hζω ε hε
  exact WangZahlLot.Obl.wz_broad_grains_initialization.initialization hσ hσ2 hω hω1 hEst hζ hζω hε
