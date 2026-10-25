-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Frozen.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

/-- Conversion to the exact frozen statement; all named predicates are definitions. -/
theorem frozen_of_conclusion
    (main : ∀ σ ω : ℝ, 0 < σ → σ ≤ 1 / 2 → 0 < ω → ω ≤ 1 →
      Estimate σ ω → Conclusion σ ω) : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧B d ρ (d^(-h)) n N x v S y w f∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ:ℝ,δ≤ρ→ρ≤1→∀N y w f,C δ η n x v Y .univ Y ρ N y w f→∀a b c:ℝ,ρ≤a→a≤b→b≤c→1≤c→c≤8→∀(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L),(fun(U:Fin L→Set V)=>(∀k,T ρ (y k) (w k)⊆U (g k))→(∀j j',q N {k|g k=j}≤δ^(-η)*q N {k|g k=j'})→(∀k,q L {j|T ρ (y k) (w k)⊆U j}≤δ^(-η))→(∀W,Convex ℝ W→O (q L {j|U j⊆W}*(a*b*c))≤O (δ^(-η))*μ W)→(∀j W,Convex ℝ W→O (q N {k|g k=j∧T ρ (y k) (w k)⊆U j∩W})*μ (U j)≤O (δ^(-η)*q N {k|g k=j})*μ (U j∩W))→O (κ*δ^(ω+ε)*(b/a)^ω*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) (fun j=>P a b c (z j) (e j)))→E σ ω→J σ ω) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσhalf hω hω1
  dsimp only
  rintro O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl P rfl B rfl C rfl E rfl J rfl hE
  change Estimate σ ω at hE
  have H := main σ ω hσ hσhalf hω hω1 hE
  intro ε hε
  obtain ⟨κ, hκ, η, hη, H⟩ := H ε hε
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hA ρ hδρ hρ1 N y w f hC a b c hρa hab hbc hc1 hc8 L z e g
    hcover hbalance hdegree hKT hrel
  exact H δ hδ hδ100 n x v Y hA ρ hδρ hρ1 N y w f hC a b c hρa hab hbc hc1 hc8
    L z e g ⟨hcover, hbalance, hdegree, hKT, hrel⟩

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
