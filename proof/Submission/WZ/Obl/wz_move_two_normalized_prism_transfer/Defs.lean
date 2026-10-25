-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core
import Submission.WZ.Obl.wz_broad_grains_initialization.LocalCount
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space
abbrev O := ENNReal.ofReal
abbrev q (n : ℕ) (s : Set (Fin n)) : ℝ := s.ncard
abbrev I := WangZahlLot.Obl.wz_move_two_long_grains_gain.I
abbrev T := WangZahlLot.Obl.wz_move_two_long_grains_gain.T
abbrev X := WangZahlLot.Obl.wz_move_two_long_grains_gain.X
abbrev A := WangZahlLot.Obl.wz_move_two_long_grains_gain.A
abbrev P := WangZahlLot.Obl.wz_move_two_long_grains_gain.P
abbrev C := WangZahlLot.Obl.wz_move_two_long_grains_gain.C
abbrev H := WangZahlLot.Obl.wz_move_two_long_grains_gain.H
abbrev μ : Set V → ENNReal := MeasureTheory.volume
abbrev ι (p : V) (i : Fin 3) : ℝ := p i
abbrev M : Set V → Prop := MeasurableSet

/-- The prism-family predicate, with its original stage parameter. -/
abbrev G (ω ζ : ℝ) := (fun(d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(o:ℕ)=>∃(a s:ℝ)(L N:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(W:Fin n→Fin L→Set V)(y w:Fin N→V)(γ:Fin L→Fin N),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀i j,M (W i j)∧W i j⊆Y i∩U j∧∀j',j≠j'→Disjoint (W i j) (W i j'))∧O (d^h)*∑i,μ (Y i)≤∑i,∑j,μ (W i j)∧(∀j,O (d^h)*μ (U j)≤μ (⋃i,W i j))∧(∀i j,(W i j).Nonempty→T d (x i) (v i)⊆T s (y (γ j)) (w (γ j))∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧(∀j(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|p∈W i j∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|p∈W i j})∧X s N y w∧(∀k,‖w k‖=1)∧(1≤o→s=ρ∧∀j,U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(2≤o→∀j j',j≠j'→γ j=γ j'→Disjoint (⋃i,W i j) (⋃i,W i j'))) (fun j=>P a (ρ*c) c (z j) (e j)))

/-- Broadness of the incidences assigned to one coarse tube. -/
abbrev Broad (ω ζ d h ρ : ℝ) (n N : ℕ) (v : Fin n → V)
    (S : Finset (Fin n)) (Z : Fin n → Set V) (f : Fin n → Fin N) : Prop :=
  ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → d ≤ r → r ≤ ρ →
    q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      d ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
