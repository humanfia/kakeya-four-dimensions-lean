-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.FDFrozen.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.FD

/-!
# The frozen statement of o161 (`wz_coarse_fibre_slab_dichotomy`)

Verbatim frozen type of o161, derived from `fd_main`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

theorem fd_frozen : (fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(W:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆W∩Q u t r})*μ W≤O (l*q n {i|i∈S∧f i=k})*μ (W∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀Fl,Fl=(fun(d ρ c h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(N:ℕ)(f:Fin n→Fin N)=>∃(G:Finset (Fin n))(Z₁:Fin n→Set V)(u:Fin n→V)(t r:Fin n→ℝ),G⊆S∧(∀i,M (Z₁ i)∧Z₁ i⊆Z i∧(i∉G→Z₁ i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈G,μ (Z₁ i)∧(∀i∈G,‖u i‖=1∧T d (x i) (v i)⊆Q (u i) (t i) (r i)∧r i≤d^c*ρ)∧∀i∈G,∀j∈G,f i=f j→(Z₁ i∩Z₁ j).Nonempty→T d (x j) (v j)⊆Q (u i) (t i) (r i))→∀τ c h:ℝ,0<τ→0<c→c<τ→0<h→∃η₀:ℝ,0<η₀∧∃d₀:ℝ,0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀η:ℝ,0<η→η≤η₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ S Z N y w f,C δ η n x v Y S Z ρ N y w f True→δ≤ρ→ρ≤1→(∃(S' :Finset (Fin n))(Z' :Fin n→Set V),S'⊆S∧(∀i,M (Z' i)∧Z' i⊆Z i∧(i∉S'→Z' i=∅))∧O (δ^τ)*∑i,μ (Y i)≤∑i∈S',μ (Z' i)∧B δ ρ (δ^(-τ)) n N x v S' y w f)∨Fl δ ρ c h n x v Y S Z N f) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro O hO q hq I hI T hT Q hQ X hX K hK F hF A hA C hC B hB Fl hFl
  subst hO hq hI hT hQ hX hK hF hA hC hB hFl
  intro τ c h hτ hc hcτ hh
  obtain ⟨η₀, hη₀, d₀, hd₀, hd₀', hmain⟩ := fd_main hτ hc hcτ hh
  refine ⟨η₀, hη₀, d₀, hd₀, hd₀', ?_⟩
  intro δ hδ hδd η hη hηη₀ n x v Y hA' ρ S Z N y w f hC' hδρ hρ1
  obtain ⟨hn, hAi, hX', hmassY, hK', hF'⟩ := hA'
  obtain ⟨hZ, hmassZ, hw, hcov, hFρ, -, hbal, hXρ, hmult⟩ := hC'
  rcases hmain δ hδ hδd η hη hηη₀ n x v Y hAi hmassY hK' ρ S Z N y w f hZ hmassZ hw hcov
    hδρ hρ1 with ⟨S', Z', hS'S, hZ', hmass', hB'⟩ | ⟨G, Z₁, u, t, r, hGS, hZ₁, hmass₁, hslab, hnon⟩
  · exact Or.inl ⟨S', Z', hS'S, hZ', hmass', fun k u t r hu hr => hB' k u t r hu hr⟩
  · refine Or.inr ⟨G, Z₁, u, t, r, hGS, hZ₁, hmass₁, fun i hi => ?_, hnon⟩
    obtain ⟨h1, -, h3, h4⟩ := hslab i hi
    exact ⟨h1, h4, h3⟩

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
