-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, Defs.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V μ ι M O q I T Q X K F A P E)

/-- The incidence-prism family used in Move 2, with stages 0, 1 and 2. -/
abbrev G (ω ζ : ℝ) := (fun(d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(o:ℕ)=>∃(a s:ℝ)(L N:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(W:Fin n→Fin L→Set V)(y w:Fin N→V)(γ:Fin L→Fin N),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀i j,M (W i j)∧W i j⊆Y i∩U j∧∀j',j≠j'→Disjoint (W i j) (W i j'))∧O (d^h)*∑i,μ (Y i)≤∑i,∑j,μ (W i j)∧(∀j,O (d^h)*μ (U j)≤μ (⋃i,W i j))∧(∀i j,(W i j).Nonempty→T d (x i) (v i)⊆T s (y (γ j)) (w (γ j))∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧(∀j(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|p∈W i j∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|p∈W i j})∧X s N y w∧(∀k,‖w k‖=1)∧(1≤o→s=ρ∧∀j,U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(2≤o→∀j j',j≠j'→γ j=γ j'→Disjoint (⋃i,W i j) (⋃i,W i j'))) (fun j=>P a (ρ*c) c (z j) (e j)))

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
