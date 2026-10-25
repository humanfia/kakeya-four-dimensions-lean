-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_rescaled_tube_estimate.RescaleEstimate
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_rescaled_tube_estimate`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_rescaled_tube_estimate`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_rescaled_tube_estimate/`
belong to this obligation.

The proof is `Interfaces.local_rescaling_of_estimate` (`RescaleEstimate.lean`), ported from
o019's prover branch x0113 (commit fda2739, session x0113) with the namespace renamed.
-/

theorem WangZahlLot.wz_rescaled_tube_estimate : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V](μ:Set V→ENNReal)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀R,R=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ ρ:ℝ,0<δ→δ≤1/100→δ≤ρ→ρ≤1→∀m l:ℝ,1≤ m→1≤l→∀n(x v:Fin n→V)(Y:Fin n→Set V)(y w:V),0<n→‖w‖=1→(∀i,‖v i‖=1∧T δ (x i) (v i)⊆T ρ y w∧M (Y i)∧Y i⊆T δ (x i) (v i))→X δ n x v→O (δ^η*n*δ^2)≤∑i,μ (Y i)→K δ m n x v→B δ ρ l n 1 x v .univ (fun _=>y) (fun _=>w) (fun _=>0)→O (κ*δ^ε*(δ/ρ)^ω*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ/ρ))^(-σ))≤μ (⋃i,Y i))→E σ ω→R σ ω) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume MeasurableSet := by
  intro σ ω hσ hσu hω hωu O hO q hq I hI T hT Q hQ X hX K hK F hF A hA B hB E hE R hR
  subst hO hq hI hT hQ hX hK hF hA hB hE hR
  exact WangZahlLot.Obl.wz_rescaled_tube_estimate.Interfaces.local_rescaling_of_estimate
    hσ.le hσu hω.le
