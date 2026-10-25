-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_termination.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_grains_finite_terminal_iteration
import Submission.WZ.Obl.wz_broad_cover_slab_refinement
import Submission.WZ.Obl.wz_terminal_grains_restoration
import Submission.WZ.Obl.wz_grains_alternative_remove_cutoff
set_option linter.unusedVariables false

theorem WangZahlLot.wz_broad_grains_termination : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀D,D=(fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(t:Bool)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧(t=true→ρ≤d^(ω/100)∧d^ζ*(ρ/d)*N/n≤c∧g≤d^(-ζ)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ c,D ω ζ δ ε ρ c n x v Y false)→∀L,L=(fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ c,D ω ζ δ η ρ c n x v Y false→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨(∃ρ' c',D ω ζ δ ε ρ' c' n x v Y true)∨∃ρ' c',D ω ζ δ ε ρ' c' n x v Y false∧(δ^(-ζ/2)*c≤c'∨c≤c'∧δ^(-ζ/2000)*ρ≤ρ'))→∀G,G=(fun(ω d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>C d h n x v Y S Z ρ N y w f (∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O ((d^(-h))*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))∧d^(1-ω/100)≤ρ∧ρ≤d^(ω/100)∧∃a c,H d h n x v S Z ρ N y w f a c (d^h*(ρ/d)*N/n) (d^(-h)))→E σ ω→(∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→J σ ω ζ ε)→(∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→ε≤ζ/100→L σ ω ζ ε)→∀h:ℝ,0<h→∃α:ℝ,0<α∧∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧η≤h∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃S Z ρ N y w f,G ω δ h n x v Y S Z ρ N y w f) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσ₂ hω hω₁
  dsimp only
  intro O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP
    C hC H hH D hD E hE J hJ L hL G hG hAssumption hInit hImprove h hh
  let B := (fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→LeanEval.Analysis.WangZahlKakeya.Space)(S:Finset (Fin n))(y w:Fin N→LeanEval.Analysis.WangZahlKakeya.Space)(f:Fin n→Fin N)=>∀k,(fun(W:Set LeanEval.Analysis.WangZahlKakeya.Space)=>∀(u:LeanEval.Analysis.WangZahlKakeya.Space)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆W∩Q u t r})*MeasureTheory.volume W≤O (l*q n {i|i∈S∧f i=k})*MeasureTheory.volume (W∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))
  let R := (fun(σ ω β τ:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤τ∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ S Z N y w f,C δ η n x v Y S Z ρ N y w f True→δ≤ρ→ρ≤1→(∀(k:Fin N)(p u:LeanEval.Analysis.WangZahlKakeya.Space)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|i∈S∧f i=k∧p∈Z i})→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤MeasureTheory.volume (⋃i,Y i)∨∃(S' :Finset (Fin n))(Z' :Fin n→Set LeanEval.Analysis.WangZahlKakeya.Space),S'⊆S∧(∀i,MeasurableSet (Z' i)∧Z' i⊆Z i∧(i∉S'→Z' i=∅))∧O (δ^τ)*∑i,MeasureTheory.volume (Y i)≤∑i∈S',MeasureTheory.volume (Z' i)∧B δ ρ (δ^(-τ)) n N x v S' y w f)
  have hRefine := WangZahlLot.wz_broad_cover_slab_refinement σ ω hσ hσ₂ hω hω₁
    O hO q hq I hI T hT Q hQ X hX K hK F hF A hA C hC B rfl E hE R rfl
    hAssumption
  obtain ⟨ζ, αg, κg, ηg, dg, hζ, hζω, hαg, hκg, hηg, hηgh, hdg, hdg₁, hRestore⟩ :=
    WangZahlLot.wz_terminal_grains_restoration σ ω hσ hσ₂ hω hω₁
      O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP C hC H hH D hD
      B rfl G (by simpa only [B] using hG) R rfl hRefine h hh
  obtain ⟨αi, κi, ηi, di, hαi, hκi, hηi, hηig, hdi, hdi₁, hIter⟩ :=
    WangZahlLot.wz_grains_finite_terminal_iteration σ ω hσ hσ₂ hω hω₁
      O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP C hC H hH D hD
      J hJ L hL hInit hImprove ζ hζ hζω ηg hηg
  have admissible_mono {δ η η' : ℝ} {n : ℕ}
      {x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space}
      {Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space}
      (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ η')
      (hFam : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) :
      A δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
    rw [hA, hK, hF, hO] at hFam ⊢
    have hp : δ ^ (-η) ≤ δ ^ (-η') :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hη)
    have hd : δ ^ η' ≤ δ ^ η :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hη
    refine ⟨hFam.1, hFam.2.1, hFam.2.2.1, ?_, ?_, ?_⟩
    · exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)) (sq_nonneg δ))).trans
        hFam.2.2.2.1
    · intro W hW
      exact (hFam.2.2.2.2.1 W hW).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl)
    · intro u t r hu hr
      exact (hFam.2.2.2.2.2 u t r hu hr).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n))) le_rfl)
  have gain_mono {δ α α' κ κ' : ℝ} {n : ℕ}
      {Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space}
      (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hα : α' ≤ α) (hκ : κ' ≤ κ) (hκ' : 0 ≤ κ')
      (hv : O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) :
      O (κ'*δ^(ω-α')*(n*δ^2)*(n*δ)^(-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) := by
    rw [hO] at hv ⊢
    apply le_trans (ENNReal.ofReal_le_ofReal _) hv
    have hp : δ ^ (ω-α') ≤ δ ^ (ω-α) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (by linarith)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hκ hp (Real.rpow_nonneg hδ.le _) (hκ'.trans hκ)
  apply WangZahlLot.wz_grains_alternative_remove_cutoff σ ω hσ hσ₂ hω hω₁
    O hO q hq I hI T hT Q hQ X hX K hK F hF A hA
    (fun δ n x v Y => ∃ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f) h hh
  refine ⟨min αi αg, min κi κg, ηi, min di dg,
    lt_min hαi hαg, lt_min hκi hκg, hηi, lt_min hdi hdg,
    (min_le_left di dg).trans hdi₁, ?_⟩
  intro δ hδ hδcut n x v Y hFam
  have hδi : δ ≤ di := hδcut.trans (min_le_left _ _)
  have hδg : δ ≤ dg := hδcut.trans (min_le_right _ _)
  have hδ₁ : δ ≤ 1 := by linarith [hδi.trans hdi₁]
  have hκ : 0 ≤ min κi κg := (lt_min hκi hκg).le
  rcases hIter δ hδ hδi n x v Y hFam with hv | ⟨ρ, c, hTerminal⟩
  · exact Or.inl (gain_mono hδ hδ₁ (min_le_left _ _) (min_le_left _ _) hκ hv)
  · rcases hRestore δ hδ hδg n x v Y
        (admissible_mono hδ hδ₁ hηig hFam) ρ c hTerminal with hv | hGrains
    · exact Or.inl (gain_mono hδ hδ₁ (min_le_right _ _) (min_le_right _ _) hκ hv)
    · exact Or.inr hGrains
