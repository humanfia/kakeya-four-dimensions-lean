-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_filling_volume_gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_slab_filling_volume_gain.Main
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_slab_filling_volume_gain`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_slab_filling_volume_gain`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_slab_filling_volume_gain/`
belong to this obligation.
-/

theorem WangZahlLot.wz_slab_filling_volume_gain : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀Sf,Sf=(fun(d b e:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>∃G:Finset (Fin n),d^e*n≤(G.card:ℝ)∧∀i∈G,∃(z:V)(g:V≃ₗᵢ[ℝ]V),T d (x i) (v i)⊆P (10*d) b 2 z g∧O (d^e)*μ (P (10*d) b 2 z g)≤μ (P (10*d) b 2 z g∩⋃j,Y j))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→E σ ω→∀c:ℝ,0<c→∃α:ℝ,0<α∧∃e:ℝ,0<e∧∃κ:ℝ,0<κ∧∃η₀:ℝ,0<η₀∧∃d₀:ℝ,0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀η:ℝ,0<η→η≤η₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀b:ℝ,δ^(1-c)≤b→b≤1→Sf δ b e n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσh hω hω1
  dsimp only
  rintro O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl P rfl Sf rfl E rfl hE
  change WangZahlLot.Obl.wz_flat_factored_improvement.TubeEstimate σ ω at hE
  intro c hc
  obtain ⟨α, hα, e, he, κ, hκ, η₀, hη₀, d₀, hd₀, hd₀100, H⟩ :=
    WangZahlLot.Obl.wz_slab_filling_volume_gain.main hσ hσh hω hE hc
  refine ⟨α, hα, e, he, κ, hκ, η₀, hη₀, d₀, hd₀, hd₀100, ?_⟩
  intro δ hδ hδd η hη hηη n x v Y hA b hb1 hb2 hSf
  exact H δ hδ hδd η hη hηη n x v Y hA b hb1 hb2 hSf
