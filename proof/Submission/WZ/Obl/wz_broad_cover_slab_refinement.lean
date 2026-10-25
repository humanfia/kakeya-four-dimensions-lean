-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_cover_slab_refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_slab_filling_volume_gain
import Submission.WZ.Obl.wz_flat_cluster_slab_filling
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_broad_cover_slab_refinement`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_broad_cover_slab_refinement`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_broad_cover_slab_refinement/`
belong to this obligation.

Glue of the split (WZ Lemma 7.14): the per-fibre slab dichotomy
`wz_coarse_fibre_slab_dichotomy` returns the refinement alternative or flat clusters;
flat clusters of a broad cover fill slabs (`wz_flat_cluster_slab_filling`), and filled
slabs gain volume under E (`wz_slab_filling_volume_gain`, WZ Lemma 5.17).
-/

theorem WangZahlLot.wz_broad_cover_slab_refinement : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(W:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆W∩Q u t r})*μ W≤O (l*q n {i|i∈S∧f i=k})*μ (W∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀R,R=(fun(σ ω β τ:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤τ∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ S Z N y w f,C δ η n x v Y S Z ρ N y w f True→δ≤ρ→ρ≤1→(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|i∈S∧f i=k∧p∈Z i})→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃(S' :Finset (Fin n))(Z' :Fin n→Set V),S'⊆S∧(∀i,M (Z' i)∧Z' i⊆Z i∧(i∉S'→Z' i=∅))∧O (δ^τ)*∑i,μ (Y i)≤∑i∈S',μ (Z' i)∧B δ ρ (δ^(-τ)) n N x v S' y w f)→E σ ω→(∀β:ℝ,0<β→∀τ:ℝ,0<τ→R σ ω β τ)) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσ2 hω hω1 O hO q hq I hI T hT Q hQ X hX K hK F hF A hA C hC B hB E hE R hR hEσ
    β hβ τ hτ
  have hSG := WangZahlLot.wz_slab_filling_volume_gain σ ω hσ hσ2 hω hω1 O hO q hq I hI T hT Q hQ
    X hX K hK F hF A hA _ rfl _ rfl E hE hEσ
  have hFS := WangZahlLot.wz_flat_cluster_slab_filling O hO q hq I hI T hT Q hQ
    X hX K hK F hF A hA C hC _ rfl _ rfl _ rfl
  have hFD := WangZahlLot.wz_coarse_fibre_slab_dichotomy O hO q hq I hI T hT Q hQ
    X hX K hK F hF A hA C hC B hB _ rfl
  have hc : (0:ℝ) < τ / 2 := by positivity
  have hcτ : τ / 2 < τ := by linarith
  -- flatness of the filled slabs, then the gain parameters, then the cluster mass exponent
  obtain ⟨c', hc', hFS₁⟩ := hFS β (τ / 2) hβ hc
  obtain ⟨α, hα, e, he, κ, hκ, η₁, hη₁, d₁, hd₁, hd₁', hSG₁⟩ := hSG c' hc'
  obtain ⟨h, hh, η₂, hη₂, d₂, hd₂, hd₂', hFS₂⟩ := hFS₁ e he
  obtain ⟨η₃, hη₃, d₃, hd₃, hd₃', hFD₁⟩ := hFD τ (τ / 2) h hτ hc hcτ hh
  subst hR
  refine ⟨α, κ, min (min η₁ η₂) (min η₃ τ), min (min d₁ d₂) d₃, hα, hκ,
    lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hτ), (min_le_right _ _).trans (min_le_right _ _),
    lt_min (lt_min hd₁ hd₂) hd₃, (min_le_right _ _).trans hd₃', ?_⟩
  intro δ hδ hδd n x v Y hAδ ρ S Z N y w f hCδ hδρ hρ1 hbroad
  have hδ₁ : δ ≤ d₁ := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₂ : δ ≤ d₂ := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₃ : δ ≤ d₃ := hδd.trans (min_le_right _ _)
  have hηpos : 0 < min (min η₁ η₂) (min η₃ τ) := lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hτ)
  have hη₁' : min (min η₁ η₂) (min η₃ τ) ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hη₂' : min (min η₁ η₂) (min η₃ τ) ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hη₃' : min (min η₁ η₂) (min η₃ τ) ≤ η₃ := (min_le_right _ _).trans (min_le_left _ _)
  rcases hFD₁ δ hδ hδ₃ _ hηpos hη₃' n x v Y hAδ ρ S Z N y w f hCδ hδρ hρ1 with hB' | hFl
  · exact Or.inr hB'
  · obtain ⟨b, hb₁, hb₂, hSf⟩ :=
      hFS₂ δ hδ hδ₂ _ hηpos hη₂' n x v Y hAδ ρ S Z N y w f hCδ hδρ hρ1 hbroad hFl
    exact Or.inl (hSG₁ δ hδ hδ₁ _ hηpos hη₁' n x v Y hAδ b hb₁ hb₂ hSf)
