-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Defs.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

/-!
The additional predicates in the four-child split, from x0433's Defs.lean
(commit 8315927). The original frozen predicates are imported from Core.
-/

set_option linter.unusedVariables false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- Stage `j` with thin grains `a < 2 d^(1-b)` on the same witnesses (child `core`). -/
abbrev Jt := (fun(ω ζ d h ρ c b:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(j:ℕ)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧a<2*d^(1-b)∧((1 ≤ j → d^ζ*(ρ/d)*N/n ≤ c) ∧ (2 ≤ j → ρ ≤ d^(ω/100)) ∧ (3 ≤ j → g ≤ d^(-ζ))))

/-- Wide grains at scale `ρ` and length `c` (children `core`, `align`, `assembly`); with `b`,
there is moreover a cover by essentially distinct unit `ρ`-tubes such that every prism and every
fine tube crossing it lie in the prism's tube. -/
abbrev G := (fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(b:Prop)=>∃(S:Finset (Fin n))(Z:Fin n→Set V)(a:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀j,M (H j)∧H j⊆U j∧O (d^h)*μ (U j)≤μ (H j))∧(⋃j,H j)=⋃i∈S,Z i∧(∀i∈S,∀j,(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧(∀j(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧p∈Z i∩H j∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧p∈Z i∩H j})∧(b→∃(N:ℕ)(y w:Fin N→V)(γ:Fin L→Fin N),X ρ N y w∧(∀k,‖w k‖=1)∧∀j,U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2∧∀i∈S,(Z i∩H j).Nonempty→T d (x i) (v i)⊆T ρ (y (γ j)) (w (γ j)))) (fun j=>P a (ρ*c) c (z j) (e j)))

/-- The pointwise broadness clause of `J`, relative to the cover `f`. -/
abbrev Broad := (fun(ω ζ d h ρ:ℝ)(n N:ℕ)(v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(f:Fin n→Fin N)=>∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
