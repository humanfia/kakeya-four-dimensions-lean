-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Definitions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

noncomputable section

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space
abbrev μ (s : Set V) : ENNReal := MeasureTheory.volume s
abbrev ι (p : V) (i : Fin 3) : ℝ := p i
abbrev M (s : Set V) : Prop := MeasurableSet s

abbrev O := ENNReal.ofReal

abbrev q := (fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))

abbrev I := Metric.ball (0:V) 1

abbrev T := (fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))

abbrev Q := (fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})

abbrev X := (fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))

abbrev K := (fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)

abbrev F := (fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))

abbrev A := (fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)

abbrev P := (fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})

abbrev B := (fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))

abbrev C := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧B d ρ (d^(-h)) n N x v S y w f∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))

abbrev G := (fun(ω d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>C d h n x v Y S Z ρ N y w f∧d^(1-ω/100)≤ρ∧ρ≤d^(ω/100)∧∃(a c:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧d^h*(ρ/d)*N/n≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O (d^(-h))*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))

abbrev E := (fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))

abbrev J := (fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ:ℝ,δ≤ρ→ρ≤1→∀N y w f,C δ η n x v Y .univ Y ρ N y w f→∀a b c:ℝ,ρ≤a→a≤b→b≤c→1≤c→c≤8→∀(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L),(fun(U:Fin L→Set V)=>(∀k,T ρ (y k) (w k)⊆U (g k))→(∀j j',q N {k|g k=j}≤δ^(-η)*q N {k|g k=j'})→(∀k,q L {j|T ρ (y k) (w k)⊆U j}≤δ^(-η))→(∀W,Convex ℝ W→O (q L {j|U j⊆W}*(a*b*c))≤O (δ^(-η))*μ W)→(∀j W,Convex ℝ W→O (q N {k|g k=j∧T ρ (y k) (w k)⊆U j∩W})*μ (U j)≤O (δ^(-η)*q N {k|g k=j})*μ (U j∩W))→O (κ*δ^(ω+ε)*(b/a)^ω*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) (fun j=>P a b c (z j) (e j)))

abbrev R := (fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ ρ:ℝ,0<δ→δ≤1/100→δ≤ρ→ρ≤1→∀m l:ℝ,1≤ m→1≤l→∀n(x v:Fin n→V)(Y:Fin n→Set V)(y w:V),0<n→‖w‖=1→(∀i,‖v i‖=1∧T δ (x i) (v i)⊆T ρ y w∧M (Y i)∧Y i⊆T δ (x i) (v i))→X δ n x v→O (δ^η*n*δ^2)≤∑i,μ (Y i)→K δ m n x v→B δ ρ l n 1 x v .univ (fun _=>y) (fun _=>w) (fun _=>0)→O (κ*δ^ε*(δ/ρ)^ω*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ/ρ))^(-σ))≤μ (⋃i,Y i))

abbrev H := (fun(ρ K:ℝ)(N:ℕ)(y w:Fin N→V)(U:Finset (Fin N))(a b:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L)=>U.Nonempty∧0<L∧ρ≤a∧a≤b∧b≤8∧(∀k∈U,T ρ (y k) (w k)⊆P a b 8 (z (g k)) (e (g k)))∧(∀j j',q N {k|k∈U∧g k=j}≤K*q N {k|k∈U∧g k=j'})∧(∀W,Convex ℝ W→O (q L {j|P a b 8 (z j) (e j)⊆W}*(a*b*8))≤O K*μ W)∧∀j W,Convex ℝ W→O (q N {k|k∈U∧g k=j∧T ρ (y k) (w k)⊆P a b 8 (z j) (e j)∩W})*μ (P a b 8 (z j) (e j))≤O (K*q N {k|k∈U∧g k=j})*μ (P a b 8 (z j) (e j)∩W))

abbrev D (σ ω : ℝ) := (fun(δ α κ:ℝ)(n:ℕ)(Y:Fin n→Set V)=>O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i))

abbrev MR (σ ω : ℝ) := (fun(δ ε ρ b Cm:ℝ)(n N L:ℕ)(Y Z W:Fin n→Set V)(S:Finset (Fin n))(U:Finset (Fin N))(f:Fin n→Fin N)(g:Fin N→Fin L)=>(∀i,M (W i)∧W i⊆Z i∧(i∉S∨f i∉U→W i=∅))∧O (δ^ε)*∑i,μ (Y i)≤∑i,μ (W i)∧∀p j,q N {k|k∈U∧g k=j∧∃i∈S,f i=k∧p∈W i}≤Cm*δ^(-ε)*(ρ/b)^(-ω-σ))

abbrev UF := (fun(n:ℕ)(S:Finset (Fin n))(Z:Fin n→Set V)(N:ℕ)(f:Fin n→Fin N)=>∃r:ℝ,∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc r (2*r))

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
