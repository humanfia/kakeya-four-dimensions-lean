-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.LargeAssembly

/-!
# o178 from its two radius cases

`AsmCore σ ω ζ ε` is the conclusion of the frozen statement of o178 for one error `ε`, written
with the abbreviations of `Defs.lean` (`Broad ω ζ` is the binding `U`).  The volume-gain
alternative is never used: the grains alternative is always produced.

* `ρ ≥ 1/2`: x0448's `large_radius_grains` (one coarse tube of radius one).
* `ρ ≤ 1/2`: `SmallRadiusGrains ω ζ ε`, the same shape at a new scale `ρ' ≥ ρ`.

`core_of_small` combines the two cases (the input error `θ` is the smaller of the two, and the
inputs at `θ` give the inputs at each case's error by monotonicity); `frozen_of_small` gives the
frozen statement of o178.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

/-- The conclusion of o178 for one error `ε` (after the single-tube hypothesis). -/
def AsmCore (σ ω ζ ε : ℝ) : Prop :=
  ∃ α κ θ d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ θ (δ ^ (-θ)) n x v Y →
      ∀ ρ : ℝ, δ ^ (1 - ω / 100) ≤ ρ → ρ ≤ 1 →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N),
        C δ θ n x v Y S Z ρ N y w f True → Broad ω ζ δ θ ρ n N v S Z f →
        δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n →
        O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
        ∃ (ρ' : ℝ) (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ) (y' w' : Fin N' → V)
          (f' : Fin n → Fin N') (a c g : ℝ), ρ ≤ ρ' ∧
          C δ ε n x v Y S' Z' ρ' N' y' w' f' True ∧ 0 < g ∧ Broad ω ζ δ ε ρ' n N' v S' Z' f' ∧
          H δ ε n x v S' Z' ρ' N' y' w' f' a c 0 g ∧ δ ^ ε * (ρ / δ) * N / n ≤ c

/-- The small-radius case (`ρ ≤ 1/2`) of the assembly, in the shape of
`large_radius_grains`, with the whole admissibility predicate `A` as hypothesis. -/
def SmallRadiusGrains (ω ζ ε : ℝ) : Prop :=
  ∃ θ d₀ : ℝ, 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ θ (δ ^ (-θ)) n x v Y →
      ∀ ρ : ℝ, δ ^ (1 - ω / 100) ≤ ρ → ρ ≤ 1 / 2 →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N),
        C δ θ n x v Y S Z ρ N y w f True → Broad ω ζ δ θ ρ n N v S Z f →
        δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n →
        ∃ (ρ' : ℝ) (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ) (y' w' : Fin N' → V)
          (f' : Fin n → Fin N') (a c g : ℝ), ρ ≤ ρ' ∧
          C δ ε n x v Y S' Z' ρ' N' y' w' f' True ∧ 0 < g ∧ Broad ω ζ δ ε ρ' n N' v S' Z' f' ∧
          H δ ε n x v S' Z' ρ' N' y' w' f' a c 0 g ∧ δ ^ ε * (ρ / δ) * N / n ≤ c

/-- The two radius cases give the conclusion of o178 for one error `ε`. -/
theorem core_of_small (hTG : TubeGrains) {σ ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) (hS : SmallRadiusGrains ω ζ ε) :
    AsmCore σ ω ζ ε := by
  obtain ⟨θL, dL, hθL, hθLε, hdL, hdL100, hL⟩ := large_radius_grains hTG hω hω1 hζ hζω hε hεζ
  obtain ⟨θS, dS, hθS, hθSε, hdS, hSmain⟩ := hS
  refine ⟨1, 1, min θL θS, min (min dL dS) (1 / 100), one_pos, one_pos,
    lt_min hθL hθS, (min_le_left _ _).trans hθLε,
    lt_min (lt_min hdL hdS) (by norm_num), ?_⟩
  intro δ hδ hδd n x v Y hA ρ hρlo hρ1 S Z N y w f hC hbr hreg
  have hδL : δ ≤ dL := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδS : δ ≤ dS := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_right _ _)).trans (by norm_num)
  have hθθL : min θL θS ≤ θL := min_le_left _ _
  have hθθS : min θL θS ≤ θS := min_le_right _ _
  right
  rcases le_or_gt ρ (1 / 2) with hρh | hρh
  · -- small radius
    exact hSmain δ hδ hδS n x v Y (A_mono hδ hδ1 hθθS hA) ρ hρlo hρh S Z N y w f
      (C_mono hδ hδ1 hθθS hC) (Broad_mono hδ hδ1 hθθS hbr) hreg
  · -- large radius: one coarse tube of radius one
    have hAL := A_mono hδ hδ1 hθθL hA
    obtain ⟨hn, hY, hX, hmass, -⟩ := hAL
    obtain ⟨S', Z', y', w', c, g, hC', hg, hbr', hH', hlen⟩ :=
      hL δ hδ hδL n x v Y hn hY hX hmass ρ hρh.le hρ1 S Z N y w f
        (C_mono hδ hδ1 hθθL hC) (Broad_mono hδ hδ1 hθθL hbr) hreg
    exact ⟨1, S', Z', 1, fun _ => y', fun _ => w', fun _ => 0, 16 * δ, c, g, hρ1, hC', hg,
      hbr', hH', hlen⟩

/-- The single-tube hypothesis of o178, in its frozen form, is `TubeGrains`. -/
theorem tubeGrains_of_body
    (h : ∀β τ ε:ℝ,0<β→0<τ→0<ε→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j))) :
    TubeGrains := by
  intro β τ ε hβ hτ hε O' hO q' hq T' hT X' hX P' hP
  subst hO hq hT hX hP
  exact h β τ ε hβ hτ hε

/-- The frozen statement of o178 from the small-radius case. -/
theorem frozen_of_small
    (hsmall : ∀ ω ζ ε : ℝ, 0 < ω → ω ≤ 1 → 0 < ζ → ζ ≤ ω / 1000 → 0 < ε → ε ≤ ζ / 100 →
      TubeGrains → SmallRadiusGrains ω ζ ε) :
    ∀σ ω ζ:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→0<ζ→ζ≤ω/1000→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀U,U=(fun(d h ρ:ℝ)(n N:ℕ)(v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(f:Fin n→Fin N)=>∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})→(∀β τ ε:ℝ,0<β→0<τ→0<ε→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j)))→∀ε:ℝ,0<ε→ε≤ζ/100→∃α κ θ d₀:ℝ,0<α∧0<κ∧0<θ∧θ≤ε∧0<d₀∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ θ (δ^(-θ)) n x v Y→∀ρ:ℝ,δ^(1-ω/100)≤ρ→ρ≤1→∀S Z N y w f,C δ θ n x v Y S Z ρ N y w f True→U δ θ ρ n N v S Z f→δ/ρ≤δ^ζ*(ρ/δ)*N/n→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ' S' Z' N' y' w' f' a c g,ρ≤ρ'∧C δ ε n x v Y S' Z' ρ' N' y' w' f' True∧0<g∧U δ ε ρ' n N' v S' Z' f'∧H δ ε n x v S' Z' ρ' N' y' w' f' a c 0 g∧δ^ε*(ρ/δ)*N/n≤c) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω ζ hσ hσ2 hω hω1 hζ hζ1 O' hO q' hq I' hI T' hT Q' hQ X' hX F' hF A' hA P' hP C' hC
    H' hH U' hU hbody ε hε hεle
  subst hO hq hI hT hQ hX hF hA hP hC hH hU
  have hTG : TubeGrains := tubeGrains_of_body hbody
  exact core_of_small (σ := σ) hTG hω hω1 hζ hζ1 hε hεle
    (hsmall ω ζ ε hω hω1 hζ hζ1 hε hεle hTG)

end WangZahlLot.Obl.wz_coarse_grains_assembly
