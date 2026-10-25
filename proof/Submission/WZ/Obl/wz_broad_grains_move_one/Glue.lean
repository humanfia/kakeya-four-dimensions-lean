-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_move_one.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_move_one.Mono

/-!
# o151 from Corollary 7.17 (the grains construction)

Wang–Zahl, Lemma 8.1 (Move #1): if the length stopping condition
`d^ζ (ρ/d) N/n ≤ c` already holds for the witnesses of the input state, keep them and
weaken the error (stage `J_1`).  Otherwise rerun the grains construction (Corollary 7.17)
on the input cover: either the volume gain holds, or there are new grains whose length
`c'` satisfies `d^ε (ρ/d) N/n ≤ c'`, hence `d^(-ζ/2) c ≤ c'` (`length_progress`).

`GrainsCore σ ω ζ` is that grains construction in the frozen predicates, with an optional
volume-gain alternative.  It is only asked for when the length condition fails, which
together with `d ≤ a ≤ ρ c` (from `H`) gives `d/ρ ≤ d^ζ (ρ/d) N/n`; the new coarse scale
`ρ'` may be any `ρ' ≥ ρ`.  `main_of_core` and `frozen_of_core` derive the frozen statement
of o151 from it.  (Glue by x0417, adapted by x0426.)
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_move_one

/-- Corollary 7.17 (via Proposition 7.15), in the frozen predicates: a broad cover at a small
input error `θ`, in the regime `d/ρ ≤ d^ζ (ρ/d) N/n`, is either a volume-gain configuration,
or it can be refined to a broad cover at error `ε` (coarse scale `ρ' ≥ ρ`) carrying grains of
length `c ≥ d^ε (ρ/d) N/n`, where `N` is the size of the input cover. -/
def GrainsCore (σ ω ζ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ ζ / 100 → ∃ α κ θ d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ θ (δ ^ (-θ)) (δ ^ (-θ)) n x v Y →
      ∀ ρ : ℝ, δ ^ (1 - ω / 100) ≤ ρ → ρ ≤ 1 →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N),
        C δ θ n x v Y S Z ρ N y w f True → Broad ω ζ δ θ ρ n N v S Z f →
        δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n →
        O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
        ∃ (ρ' : ℝ) (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ) (y' w' : Fin N' → V)
          (f' : Fin n → Fin N') (a c g : ℝ), ρ ≤ ρ' ∧
          C δ ε n x v Y S' Z' ρ' N' y' w' f' True ∧ 0 < g ∧ Broad ω ζ δ ε ρ' n N' v S' Z' f' ∧
          H δ ε n x v S' Z' ρ' N' y' w' f' a c 0 g ∧ δ ^ ε * (ρ / δ) * N / n ≤ c

/-- The grains of `H` have width at least the fine scale: `d ≤ ρ c`. -/
theorem H_fine_le {d h ρ a c b g : ℝ} {n N : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hH : H d h n x v S Z ρ N y w f a c b g) : d ≤ ρ * c := by
  obtain ⟨L, z, e, G, γ, m, hda, hab, -⟩ := hH
  exact hda.trans hab

/-- Move #1 (Lemma 8.1) from the grains construction. -/
theorem main_of_core {σ ω ζ : ℝ} (hζ : 0 < ζ) (hcore : GrainsCore σ ω ζ) :
    ∀ ε : ℝ, 0 < ε → ε ≤ ζ / 100 → ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V), A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ∀ ρ c : ℝ, J ω ζ δ η ρ c n x v Y 0 →
        O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
        J ω ζ δ ε ρ c n x v Y 1 ∨
        ∃ ρ' c' : ℝ, J ω ζ δ ε ρ' c' n x v Y 0 ∧ δ ^ (-ζ / 2) * c ≤ c' := by
  intro ε hε hεζ
  obtain ⟨α, κ, θ, d₀, hα, hκ, hθ, hθε, hd₀, hmain⟩ := hcore ε hε hεζ
  refine ⟨α, κ, θ, min d₀ (1 / 100), hα, hκ, hθ, hθε, lt_min hd₀ (by norm_num),
    min_le_right _ _, ?_⟩
  intro δ hδ hδd n x v Y hA ρ c hJ
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρ, hg, hbr, hH, -⟩ := J_iff.1 hJ
  obtain ⟨hc0, hc1, hρ0, hρ1⟩ := H_scales hδ hH
  by_cases hlen : δ ^ ζ * (ρ / δ) * N / n ≤ c
  · exact Or.inr (Or.inl (J_mono hδ hδ1 hθε (J_zero_to_one S Z N y w f a g hC hρ hg hbr hH hlen)))
  · have hreg : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n := by
      have h1 : δ / ρ ≤ c := by
        rw [div_le_iff₀ hρ0]
        linarith [H_fine_le hH]
      linarith [lt_of_not_ge hlen]
    rcases hmain δ hδ (hδd.trans (min_le_left _ _)) n x v Y hA ρ hρ hρ1 S Z N y w f hC hbr
        hreg with
      hgain | ⟨ρ', S', Z', N', y', w', f', a', c', g', hρρ', hC', hg', hbr', hH', hc'⟩
    · exact Or.inl hgain
    · refine Or.inr (Or.inr ⟨ρ', c', J_zero_of S' Z' N' y' w' f' a' g' hC' (hρ.trans hρρ') hg'
        hbr' hH', ?_⟩)
      have hr : (0 : ℝ) ≤ (ρ / δ) * N / n := by positivity
      refine length_progress (e := ε) (r := (ρ / δ) * N / n) hδ hδ1 (by linarith) hr ?_ ?_
      · have : δ ^ ζ * (ρ / δ * N / n) = δ ^ ζ * (ρ / δ) * N / n := by ring
        rw [this]
        exact lt_of_not_ge hlen
      · have : δ ^ ε * (ρ / δ * N / n) = δ ^ ε * (ρ / δ) * N / n := by ring
        rw [this]
        exact hc'

/-- The frozen statement of o151, from the grains construction. -/
theorem frozen_of_core
    (hcore : ∀ σ ω ζ : ℝ, 0 < σ → σ ≤ 1 / 2 → 0 < ω → ω ≤ 1 → 0 < ζ → ζ ≤ ω / 1000 →
      E σ ω → R σ ω → GrainsCore σ ω ζ) :
    ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀R,R=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ ρ:ℝ,0<δ→δ≤1/100→δ≤ρ→ρ≤1→∀m l:ℝ,1≤ m→1≤l→∀n(x v:Fin n→V)(Y:Fin n→Set V)(y w:V),0<n→‖w‖=1→(∀i,‖v i‖=1∧T δ (x i) (v i)⊆T ρ y w∧M (Y i)∧Y i⊆T δ (x i) (v i))→X δ n x v→O (δ^η*n*δ^2)≤∑i,μ (Y i)→K δ m n x v→B δ ρ l n 1 x v .univ (fun _=>y) (fun _=>w) (fun _=>0)→O (κ*δ^ε*(δ/ρ)^ω*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ/ρ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(j:ℕ)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧((1 ≤ j → d^ζ*(ρ/d)*N/n ≤ c) ∧ (2 ≤ j → ρ ≤ d^(ω/100)) ∧ (3 ≤ j → g ≤ d^(-ζ))))→E σ ω→R σ ω→∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→ε≤ζ/100→∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ c,J ω ζ δ η ρ c n x v Y 0→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨J ω ζ δ ε ρ c n x v Y 1∨∃ρ' c',J ω ζ δ ε ρ' c' n x v Y 0∧(δ^(-ζ/2)*c≤c')) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσle hω hωle O' hO q' hq I' hI T' hT Q' hQ X' hX K' hK F' hF A' hA P' hP B' hB
    C' hC H' hH E' hE R' hR J' hJ hEst hRes ζ hζ hζle ε hε hεle
  subst hO hq hI hT hQ hX hK hF hA hP hB hC hH hE hR hJ
  exact main_of_core hζ (hcore σ ω ζ hσ hσle hω hωle hζ hζle hEst hRes) ε hε hεle

end WangZahlLot.Obl.wz_broad_grains_move_one
