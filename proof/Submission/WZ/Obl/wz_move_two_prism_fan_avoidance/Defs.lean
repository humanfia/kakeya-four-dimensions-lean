-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledPrismLocality
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CordobaSlab

/-!
# Frozen binders of o220 and the explicit data of the staged prism predicate `R`

`NData` is the data of `R δ h ρ c … 1` (stage-two prisms with normalized incidence caps).
Its first fields are x0570's `PrismData` (o198 branch x0570, `PrismData.lean`), copied with the
namespace renamed; the caps `B` and their clause are new.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_prism_fan_avoidance

open Set MeasureTheory

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space
abbrev O := ENNReal.ofReal
abbrev q (n : ℕ) (s : Set (Fin n)) : ℝ := s.ncard
abbrev I := WangZahlLot.Obl.wz_move_two_long_grains_gain.I
abbrev T := WangZahlLot.Obl.wz_move_two_long_grains_gain.T
abbrev X := WangZahlLot.Obl.wz_move_two_long_grains_gain.X
abbrev A := WangZahlLot.Obl.wz_move_two_long_grains_gain.A
abbrev P := WangZahlLot.Obl.wz_move_two_long_grains_gain.P
abbrev μ : Set V → ENNReal := MeasureTheory.volume
abbrev ι (p : V) (i : Fin 3) : ℝ := p i
abbrev M : Set V → Prop := MeasurableSet

/-- The frozen staged prism predicate `R` of o220. -/
abbrev R (ω ζ : ℝ) := (fun(d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(o:ℕ)=>∃(a:ℝ)(L N:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(W:Fin n→Fin L→Set V)(y w:Fin N→V)(γ:Fin L→Fin N)(B:Fin L→ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀i j,M (W i j)∧W i j⊆Y i∩U j∧∀j',j≠j'→Disjoint (W i j) (W i j'))∧O (d^h)*∑i,μ (Y i)≤∑i,∑j,μ (W i j)∧(∀j,O (d^h)*μ (U j)≤μ (⋃i,W i j))∧(∀i j,(W i j).Nonempty→T d (x i) (v i)⊆T ρ (y (γ j)) (w (γ j))∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧(∀j(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|p∈W i j∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|p∈W i j})∧X ρ N y w∧(∀k,‖w k‖=1)∧(∀j,U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (⋃i,W i j) (⋃i,W i j'))∧(1≤o→∀j,0<B j∧(∀p,q n {i|p∈W i j}≤B j)∧O (d^h*B j)*μ (U j)≤∑i,μ (W i j))∧(2≤o→∀i j j',j≠j'→γ j=γ j'→(W i j).Nonempty→Disjoint (W i j') (U j))) (fun j=>P a (ρ*c) c (z j) (e j)))

/-- Explicit data of `R … 1`: stage-two prisms at the coarse scale `ρ` with normalized
incidence caps `B`. -/
structure NData (ω ζ δ h ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) where
  a : ℝ
  L : ℕ
  N : ℕ
  z : Fin L → V
  e : Fin L → V ≃ₗᵢ[ℝ] V
  W : Fin n → Fin L → Set V
  y : Fin N → V
  w : Fin N → V
  γ : Fin L → Fin N
  B : Fin L → ℝ
  lower : δ ≤ a
  middle : a ≤ ρ * c
  upper : ρ * c ≤ c
  length : c ≤ 1
  pieces : ∀ i j, MeasurableSet (W i j) ∧ W i j ⊆ Y i ∩ P a (ρ * c) c (z j) (e j) ∧
    ∀ j', j ≠ j' → Disjoint (W i j) (W i j')
  mass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i, ∑ j, μ (W i j)
  dense : ∀ j, O (δ ^ h) * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (⋃ i, W i j)
  crossing : ∀ i j, (W i j).Nonempty →
    T δ (x i) (v i) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
      |ι (e j (p - z j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ * c) c (z j) (e j), ι (e j (p - z j)) 2 = t
  broad : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i j}
  distinct : X ρ N y w
  unit : ∀ k, ‖w k‖ = 1
  geometry : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2
  disjoint : ∀ j j', j ≠ j' → γ j = γ j' → Disjoint (⋃ i, W i j) (⋃ i, W i j')
  cap : ∀ j, 0 < B j ∧ (∀ p, q n {i | p ∈ W i j} ≤ B j) ∧
    O (δ ^ h * B j) * μ (P a (ρ * c) c (z j) (e j)) ≤ ∑ i, μ (W i j)

/-- Cross-prism avoidance (stage two of `R`). -/
def NData.Avoid {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (D : NData ω ζ δ h ρ c n x v Y) : Prop :=
  ∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
    Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j))

theorem ndata_of_R {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hR : R ω ζ δ h ρ c n x v Y 1) : Nonempty (NData ω ζ δ h ρ c n x v Y) := by
  obtain ⟨a, L, N, z, e, W, y, w, γ, B, hlo, hmid, hup, hlen, hW, hmass, hdense,
    hcross, hbr, hX, hw, hgeom, hdisj, hcap, -⟩ := hR
  exact ⟨⟨a, L, N, z, e, W, y, w, γ, B, hlo, hmid, hup, hlen, hW, hmass, hdense,
    hcross, hbr, hX, hw, hgeom, hdisj, hcap le_rfl⟩⟩

theorem R_of_ndata {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (D : NData ω ζ δ h ρ c n x v Y) (hav : D.Avoid) : R ω ζ δ h ρ c n x v Y 2 :=
  ⟨D.a, D.L, D.N, D.z, D.e, D.W, D.y, D.w, D.γ, D.B, D.lower, D.middle, D.upper, D.length,
    D.pieces, D.mass, D.dense, D.crossing, D.broad, D.distinct, D.unit, D.geometry,
    D.disjoint, fun _ => D.cap, fun _ => hav⟩

end WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
