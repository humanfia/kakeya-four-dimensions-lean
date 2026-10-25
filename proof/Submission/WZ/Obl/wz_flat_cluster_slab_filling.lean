-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Core
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_flat_cluster_slab_filling`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_flat_cluster_slab_filling/`
belong to this obligation.
-/

theorem WangZahlLot.wz_flat_cluster_slab_filling : (fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀Fl,Fl=(fun(d ρ c h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(N:ℕ)(f:Fin n→Fin N)=>∃(G:Finset (Fin n))(Z₁:Fin n→Set V)(u:Fin n→V)(t r:Fin n→ℝ),G⊆S∧(∀i,M (Z₁ i)∧Z₁ i⊆Z i∧(i∉G→Z₁ i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈G,μ (Z₁ i)∧(∀i∈G,‖u i‖=1∧T d (x i) (v i)⊆Q (u i) (t i) (r i)∧r i≤d^c*ρ)∧∀i∈G,∀j∈G,f i=f j→(Z₁ i∩Z₁ j).Nonempty→T d (x j) (v j)⊆Q (u i) (t i) (r i))→∀Sf,Sf=(fun(d b e:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>∃G:Finset (Fin n),d^e*n≤(G.card:ℝ)∧∀i∈G,∃(z:V)(g:V≃ₗᵢ[ℝ]V),T d (x i) (v i)⊆P (10*d) b 2 z g∧O (d^e)*μ (P (10*d) b 2 z g)≤μ (P (10*d) b 2 z g∩⋃j,Y j))→∀β c:ℝ,0<β→0<c→∃c':ℝ,0<c'∧∀e:ℝ,0<e→∃h:ℝ,0<h∧∃η₀:ℝ,0<η₀∧∃d₀:ℝ,0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀η:ℝ,0<η→η≤η₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ S Z N y w f,C δ η n x v Y S Z ρ N y w f True→δ≤ρ→ρ≤1→(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|i∈S∧f i=k∧p∈Z i})→Fl δ ρ c h n x v Y S Z N f→∃b:ℝ,δ^(1-c')≤b∧b≤1∧Sf δ b e n x v Y) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro O hO q hq I hI T hT Q hQ X hX K hK F hF A hA C hC P hP Fl hFl Sf hSf β c hβ hc
  subst hSf hFl hP hC hA hF hK hX hQ hT hI hq hO
  refine ⟨min c 1 / 2, by positivity, fun e he => ?_⟩
  obtain ⟨h, hh, η₀, hη₀, d₀, hd₀, hd₀1, hcore⟩ :=
    WangZahlLot.Obl.wz_flat_cluster_slab_filling.core hβ hc he
  refine ⟨h, hh, η₀, hη₀, d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd η hη hηη₀ n x v Y hAδ ρ S Z N y w f hCδ hδρ hρ1 hbroad hFlδ
  obtain ⟨hn, hv4, -, hmass, -, -⟩ := hAδ
  obtain ⟨hZ, -, hw, hcoarse, -⟩ := hCδ
  obtain ⟨G', hG'card, hG'⟩ := hcore δ hδ hδd η hη hηη₀ n x v Y hn (fun i => (hv4 i).1)
    (fun i => (hv4 i).2.2.1) (fun i => (hv4 i).2.2.2) hmass ρ S Z N y w f hZ hw hcoarse hδρ hρ1
    hbroad hFlδ
  have hδ1 : δ ≤ 1 := by linarith
  have hc1 : 0 ≤ 1 - min c 1 / 2 := by
    have := min_le_right c 1
    linarith
  refine ⟨δ ^ (1 - min c 1 / 2), le_rfl, Real.rpow_le_one hδ.le hδ1 hc1, G', hG'card, ?_⟩
  intro i hi
  obtain ⟨z, g, h1, h2⟩ := hG' i hi
  exact ⟨z, g, h1, h2⟩
