-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_long_grains_gain.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# The frozen predicates of o174, unpacked grains and two small helpers

Named copies of the frozen binders (`A`, `C`, `H`, ...), the body `HB` of the grains
predicate for explicit grain data, an explicit cutoff making a positive power of `δ`
small, and a constant sum of real masses.  Ported from x0409's branch of o122
(`Core`, `DenseCut`, `ThickGrains`, commit 80668ab) with the namespace renamed.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_long_grains_gain

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space
abbrev μ : Set V → ENNReal := MeasureTheory.volume
abbrev ι (p : V) (i : Fin 3) : ℝ := p i
abbrev M : Set V → Prop := MeasurableSet

abbrev O := ENNReal.ofReal

abbrev q := (fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))

abbrev I := Metric.ball (0:V) 1

abbrev T := (fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))

abbrev Q := (fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})

abbrev X := (fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))

abbrev K := (fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)

abbrev F := (fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))

abbrev A := (fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)

abbrev P := (fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})

abbrev C := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))

abbrev H := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))

open MeasureTheory Set Metric
open scoped ENNReal

/-- The body of the frozen grains predicate for explicit grain data. -/
def HB (d h : ℝ) (n : ℕ) (x v : Fin n → V) (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ)
    (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N) (a c b g : ℝ) (L : ℕ) (z : Fin L → V)
    (e : Fin L → V ≃ₗᵢ[ℝ] V) (G : Fin L → Set V) (γ : Fin L → Fin N) (m : ℝ) : Prop :=
  d ≤ a ∧ a ≤ ρ * c ∧ ρ * c ≤ c ∧ c ≤ 1 ∧
  (∀ j, M (G j) ∧ G j ⊆ P a (ρ * c) c (z j) (e j) ∧
    P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2) ∧
  (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (G j) (G j')) ∧
  (∀ k, {p | ∃ j, γ j = k ∧ p ∈ G j} = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) ∧
  O (d ^ h * L * a * (ρ * c) * c) ≤ ∑ j, μ (G j) ∧
  (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
    q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2 * m)) ∧
  (∀ i ∈ S, ∀ j, f i = γ j → (Z i ∩ G j).Nonempty →
    Z i ∩ P a (ρ * c) c (z j) (e j) ⊆ G j ∧
    (∀ p ∈ T d (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
      |ι (e j (p - z j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T d (x i) (v i) ∩ P a (ρ * c) c (z j) (e j), ι (e j (p - z j)) 2 = t) ∧
  b ≤ c ∧
  ∀ j W, Convex ℝ W →
    O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
      P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g * μ W

theorem H_iff {d h : ℝ} {n : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {ρ : ℝ} {N : ℕ} {y w : Fin N → V} {f : Fin n → Fin N} {a c b g : ℝ} :
    H d h n x v S Z ρ N y w f a c b g ↔
      ∃ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (G : Fin L → Set V)
        (γ : Fin L → Fin N) (m : ℝ), HB d h n x v S Z ρ N y w f a c b g L z e G γ m :=
  Iff.rfl


/-- An explicit cutoff making a positive power of `δ` small. -/
lemma small_rpow {p K : ℝ} (hp : 0 < p) (hK : 0 < K) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ^ p ≤ K := by
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hK _, fun δ hδ hδd => ?_⟩
  calc δ ^ p ≤ (K ^ (1 / p)) ^ p := Real.rpow_le_rpow hδ.le hδd hp.le
    _ = K := by rw [← Real.rpow_mul hK.le, one_div_mul_cancel hp.ne', Real.rpow_one]

/-- A constant sum of real masses. -/
lemma sum_const_ofReal (L : ℕ) (x : ℝ) : (∑ _j : Fin L, O x) = O (L * x) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [O]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end WangZahlLot.Obl.wz_move_two_long_grains_gain
