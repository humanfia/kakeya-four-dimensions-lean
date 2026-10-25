-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.GrainStateDefs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitCover

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (V μ ι M O q T P)

/-- The frozen initialization grain predicate. -/
abbrev Grains := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))

/-- The frozen initialization state, including its optional terminal bounds. -/
abbrev State := (fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(t:Bool)=>∃S Z N y w f a g,Cover d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧Grains d h n x v S Z ρ N y w f a c 0 g∧(t=true→ρ≤d^(ω/100)∧d^ζ*(ρ/d)*N/n≤c∧g≤d^(-ζ)))

end WangZahlLot.Obl.wz_broad_grains_initialization
