-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SplitV3b.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SplitV3Main

/-!
# Split v3b: the flat-prism child with boxes matching Proposition 4.6

The flat child `J` of the proposed splits (o045) only accepts boxes `P a b 2` with `b ≤ 1`. The
factoring boxes of a family of unit `ρ`-tubes in `ball 0 R` (`Factor.factorFrozen`) are
`P a b (2R)` with `ρ ≤ a ≤ b ≤ 2R`, and `b` can exceed `1` (slab-like prisms), so a prover of the
gain child could not apply `J` to them. `Jb` is `J` for boxes `P a b c` with `ρ ≤ a ≤ b ≤ c` and
`1 ≤ c ≤ 8` (Katz–Tao count of the boxes normalised by `a b c`); it is WZ Proposition 5.2 for
prisms comparable to `a × b × 2` (its case `c = 2`, `b ≤ 1` is `J` up to a factor `2` in the
Katz–Tao count of the boxes). Split v3b is split v3 with `J`
replaced by `Jb` in the flat and gain children; the glue is the same (`glue_core_v3`).
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory

namespace Interfaces

/-- Proposition 5.2 for boxes `P a b c`, `ρ ≤ a ≤ b ≤ c`, `1 ≤ c ≤ 8`. -/
def Jb :=
  fun (σ ω : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ N y w f, C δ η n x v Y Finset.univ Y ρ N y w f → ∀ a b c : ℝ, ρ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 → ∀ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L), (fun (U : Fin L → Set V) => (∀ k, T ρ (y k) (w k) ⊆ U (g k)) → (∀ j j', q {k | g k = j} ≤ δ ^ (-η) * q {k | g k = j'}) → (∀ k, q {j | T ρ (y k) (w k) ⊆ U j} ≤ δ ^ (-η)) → (∀ W, Convex ℝ W → o (q {j | U j ⊆ W} * (a * b * c)) ≤ o (δ ^ (-η)) * μ W) → (∀ j W, Convex ℝ W → o (q {k | g k = j ∧ T ρ (y k) (w k) ⊆ U j ∩ W}) * μ (U j) ≤ o (δ ^ (-η) * q {k | g k = j}) * μ (U j ∩ W)) → o (κ * δ ^ (ω + ε) * (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)) (fun j => P a b c (z j) (e j))

/-- The flat child of split v3b. -/
def FlatChildB (σ ω : ℝ) : Prop := E σ ω → Jb σ ω

/-- The gain child of split v3b. -/
def GainChild3b (σ ω : ℝ) : Prop := E σ ω → Jb σ ω → GainBody σ ω

/-- The glue of split v3b. -/
theorem glue_of_children_v3b {σ ω : ℝ} (hσ : 0 < σ) (hE : E σ ω) (hflat : FlatChildB σ ω)
    (hgrains : GrainsChild σ ω) (hgain : GainChild3b σ ω) : Conclusion σ ω :=
  glue_core_v3 hσ hE hgrains (hgain hE (hflat hE))

end Interfaces

open Interfaces

/-- The frozen flat child of split v3b. -/
def flatBFrozen : Prop :=
  ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧B d ρ (d^(-h)) n N x v S y w f∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ:ℝ,δ≤ρ→ρ≤1→∀N y w f,C δ η n x v Y .univ Y ρ N y w f→∀a b c:ℝ,ρ≤a→a≤b→b≤c→1≤c→c≤8→∀(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L),(fun(U:Fin L→Set V)=>(∀k,T ρ (y k) (w k)⊆U (g k))→(∀j j',q N {k|g k=j}≤δ^(-η)*q N {k|g k=j'})→(∀k,q L {j|T ρ (y k) (w k)⊆U j}≤δ^(-η))→(∀W,Convex ℝ W→O (q L {j|U j⊆W}*(a*b*c))≤O (δ^(-η))*μ W)→(∀j W,Convex ℝ W→O (q N {k|g k=j∧T ρ (y k) (w k)⊆U j∩W})*μ (U j)≤O (δ^(-η)*q N {k|g k=j})*μ (U j∩W))→O (κ*δ^(ω+ε)*(b/a)^ω*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) (fun j=>P a b c (z j) (e j)))→E σ ω→J σ ω) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet

/-- The frozen gain child of split v3b. -/
def gain3BFrozen : Prop :=
  ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧B d ρ (d^(-h)) n N x v S y w f∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀G,G=(fun(ω d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>C d h n x v Y S Z ρ N y w f∧d^(1-ω/100)≤ρ∧ρ≤d^(ω/100)∧∃(a c:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧d^h*(ρ/d)*N/n≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O (d^(-h))*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ:ℝ,δ≤ρ→ρ≤1→∀N y w f,C δ η n x v Y .univ Y ρ N y w f→∀a b c:ℝ,ρ≤a→a≤b→b≤c→1≤c→c≤8→∀(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L),(fun(U:Fin L→Set V)=>(∀k,T ρ (y k) (w k)⊆U (g k))→(∀j j',q N {k|g k=j}≤δ^(-η)*q N {k|g k=j'})→(∀k,q L {j|T ρ (y k) (w k)⊆U j}≤δ^(-η))→(∀W,Convex ℝ W→O (q L {j|U j⊆W}*(a*b*c))≤O (δ^(-η))*μ W)→(∀j W,Convex ℝ W→O (q N {k|g k=j∧T ρ (y k) (w k)⊆U j∩W})*μ (U j)≤O (δ^(-η)*q N {k|g k=j})*μ (U j∩W))→O (κ*δ^(ω+ε)*(b/a)^ω*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) (fun j=>P a b c (z j) (e j)))→E σ ω→J σ ω→∀ζ:ℝ,0<ζ→∃h:ℝ,0<h∧h≤ζ/10∧∃α:ℝ,0<α∧∃κ:ℝ,0<κ∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ h (δ^(-h)) (δ^(-h)) n x v Y→∀S Z ρ N y w f,G ω δ h n x v Y S Z ρ N y w f→(∀U:Finset (Fin N),O (δ^(ζ/2))*∑i∈S,μ (Z i)≤∑i∈S.filter (fun i=>f i∈U),μ (Z i)→¬∀W,Convex ℝ W→O (q N {k|k∈U∧T ρ (y k) (w k)⊆W}*ρ^2)≤O (δ^(-ζ))*μ W)→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet

theorem flatChildB_of_frozen (h : flatBFrozen) {σ ω : ℝ} (hσ : 0 < σ) (hσu : σ ≤ 1 / 2)
    (hω : 0 < ω) (hωu : ω ≤ 1) : FlatChildB σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

theorem gainChild3b_of_frozen (h : gain3BFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GainChild3b σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

theorem main_of_frozen_children_v3b (hflat : flatBFrozen)
    (hgrains : SplitTypes.grainsFrozen) (hgain : gain3BFrozen) :
    ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ K, K = (fun (d m : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ F, F = (fun (d l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ ENNReal.ofReal (l * n) * MeasureTheory.volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ∀ A, A = (fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * MeasureTheory.volume (T d (x i) (v i))) ∧ ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, MeasureTheory.volume (Y i) ∧ K d m n x v ∧ F d l n x v) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) → (∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ ζ) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧ T δ (x i) (v i) ⊆ T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r}}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤ ENNReal.ofReal (δ ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r})) := by
  intro σ ω hσ hσu hω hωu T₀ hT K₀ hK F₀ hF A₀ hA
  subst T₀
  subst K₀
  subst F₀
  subst A₀
  intro hE
  exact glue_of_children_v3b hσ hE (flatChildB_of_frozen hflat hσ hσu hω hωu)
    (grainsChild_of_frozen hgrains hσ hσu hω hωu) (gainChild3b_of_frozen hgain hσ hσu hω hωu)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
