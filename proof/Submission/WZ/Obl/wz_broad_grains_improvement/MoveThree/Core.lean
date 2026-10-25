-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Core.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# The frozen predicates of o153, as abbreviations

The abbreviations and the error-monotonicity lemmas are adapted from session
x0366's `Core.lean` on o122 (branch x0366 of o122, commit 4c3a205), the parent
of o153. They are written out here so that o153 does not import its parent.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

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

abbrev B := (fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))

abbrev C := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))

abbrev H := (fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))

abbrev D := (fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(t:Bool)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧(t=true→ρ≤d^(ω/100)∧d^ζ*(ρ/d)*N/n≤c∧g≤d^(-ζ)))

abbrev E := (fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))

abbrev R := (fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ ρ:ℝ,0<δ→δ≤1/100→δ≤ρ→ρ≤1→∀m l:ℝ,1≤ m→1≤l→∀n(x v:Fin n→V)(Y:Fin n→Set V)(y w:V),0<n→‖w‖=1→(∀i,‖v i‖=1∧T δ (x i) (v i)⊆T ρ y w∧M (Y i)∧Y i⊆T δ (x i) (v i))→X δ n x v→O (δ^η*n*δ^2)≤∑i,μ (Y i)→K δ m n x v→B δ ρ l n 1 x v .univ (fun _=>y) (fun _=>w) (fun _=>0)→O (κ*δ^ε*(δ/ρ)^ω*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ/ρ))^(-σ))≤μ (⋃i,Y i))

abbrev L := (fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ c,D ω ζ δ η ρ c n x v Y false→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨(∃ρ' c',D ω ζ δ ε ρ' c' n x v Y true)∨∃ρ' c',D ω ζ δ ε ρ' c' n x v Y false∧(δ^(-ζ/2)*c≤c'∨c≤c'∧δ^(-ζ/2000)*ρ≤ρ'))

abbrev J := (fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(j:ℕ)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧((1 ≤ j → d^ζ*(ρ/d)*N/n ≤ c) ∧ (2 ≤ j → ρ ≤ d^(ω/100)) ∧ (3 ≤ j → g ≤ d^(-ζ))))

/-- Increasing the error weakens the original-family admissibility assumptions. -/
theorem admissible_mono {d h h' : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (ha : A d h (d^(-h)) (d^(-h)) n x v Y) :
    A d h' (d^(-h')) (d^(-h')) n x v Y := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  have hi := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)
  rcases ha with ⟨hn, ht, hx, hm, hk, hf⟩
  refine ⟨hn, ht, hx, le_trans ?_ hm, ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro W hW
    exact (hk W hW).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hi) _)
  · intro u t r hu hr
    apply (hf u t r hu hr).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg n)

/-- All cover and retained-mass clauses are monotone in the error. -/
theorem cover_mono {d h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V}
    {f : Fin n → Fin N} {b : Prop} (hd : 0 < d) (hd1 : d ≤ 1)
    (hh : h ≤ h') (hc : C d h n x v Y S Z ρ N y w f b) :
    C d h' n x v Y S Z ρ N y w f b := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  have hi := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)
  rcases hc with ⟨hz, hm, hw, ht, hf, hb, hbal, hx, hov⟩
  refine ⟨hz, le_trans ?_ hm, hw, ht, ?_, hb, ?_, hx, ?_⟩
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hp) _
  · intro u t r hu hr
    apply (hf u t r hu hr).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg N)
  · intro k k'
    exact (hbal k k').trans
      (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))
  · intro i hiS
    exact (hov i hiS).trans hi

/-- Only the grain-mass lower bound depends on the error. -/
theorem grains_mono {d h h' ρ a c b g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hhg : H d h n x v S Z ρ N y w f a c b g) :
    H d h' n x v S Z ρ N y w f a c b g := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  rcases hhg with ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1,
    hgeom, hdisj, hunion, hmass, hmult, hcross, hb, hcount⟩
  have ha : 0 ≤ a := (hd.trans_le hda).le
  have hrc : 0 ≤ ρ*c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  refine ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1,
    hgeom, hdisj, hunion, le_trans ?_ hmass, hmult, hcross, hb, hcount⟩
  apply ENNReal.ofReal_le_ofReal
  gcongr

/-- All stages retain the same stopping witnesses when the error is weakened. -/
theorem stage_mono {ω ζ d h h' ρ c : ℝ} {n j : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hj : J ω ζ d h ρ c n x v Y j) : J ω ζ d h' ρ c n x v Y j := by
  have hi := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)
  rcases hj with ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, hstop⟩
  refine ⟨S, Z, N, y, w, f, a, g, cover_mono hd hd1 hh hc,
    hρ, hg, ?_, grains_mono hd hd1 hh hhg, hstop⟩
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hd.trans_le hdr
  have hρpos : 0 < ρ := hr.trans_le hrρ
  apply (hbr k p u r hu hdr hrρ).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right hi
    (Real.rpow_nonneg (div_nonneg hr.le hρpos.le) _)

theorem loose_to_stage_zero {ω ζ d h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : D ω ζ d h ρ c n x v Y false) : J ω ζ d h ρ c n x v Y 0 := by
  rcases hd with ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, _⟩
  exact ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg,
    by omega, by omega, by omega⟩

theorem stage_zero_to_loose {ω ζ d h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hj : J ω ζ d h ρ c n x v Y 0) : D ω ζ d h ρ c n x v Y false := by
  rcases hj with ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, _⟩
  exact ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, by simp⟩

theorem stage_three_to_terminal {ω ζ d h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hj : J ω ζ d h ρ c n x v Y 3) : D ω ζ d h ρ c n x v Y true := by
  rcases hj with ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, hstop⟩
  refine ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hhg, ?_⟩
  intro _
  exact ⟨hstop.2.1 (by decide), hstop.1 (by decide), hstop.2.2 (by decide)⟩

theorem loose_mono {ω ζ d h h' ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hs : D ω ζ d h ρ c n x v Y false) : D ω ζ d h' ρ c n x v Y false :=
  stage_zero_to_loose (stage_mono hd hd1 hh (loose_to_stage_zero hs))

/-- Minima of gain exponents and constants give a common lower bound. -/
theorem gain_mono {d ω σ α α' κ κ' : ℝ} {n : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : α ≤ α')
    (hκ : κ ≤ κ') (hκ0 : 0 ≤ κ) :
    O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤
      O (κ'*d^(ω-α')*(n*d^2)*(n*d)^(-σ)) := by
  have hκ'0 : 0 ≤ κ' := hκ0.trans hκ
  have hp : d^(ω-α) ≤ d^(ω-α') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (sub_le_sub_left hα ω)
  apply ENNReal.ofReal_le_ofReal
  gcongr

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
