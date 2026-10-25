-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_finite_terminal_iteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_grains_finite_terminal_iteration`

Finite iteration with backward error budgets (o123, child 1).

Fix `ζ` and the terminal error `ε`. Starting from the terminal budget `e₀ = min ε (ζ/100)`,
the budgets `b 0 = e₀`, `b (j+1) = ηL (b j)` record the input tolerance of the improvement
step `L` at each budget. The initialization `J` is applied at `b Tn`, and the original
admissibility exponent is the input tolerance of `J`; the gain constants and the cutoff are
minima over the finitely many steps. If neither a gain nor a terminal D-state occurs, `Tn`
improvement steps produce D-states at the budgets `b (Tn - s)` whose potential
`4 * log c + ζ * log ρ` (which lies in `[(4 + ζ) * log δ, 0]`) rises by at least
`-ζ * (ζ / 2000) * log δ` per step; the horizon `Tn` is chosen so that this is impossible.
-/


namespace WangZahlLot.Obl.wz_grains_finite_terminal_iteration

/-- A positive real below finitely many given positive reals. -/
theorem exists_pos_le_of_lt (g : ℕ → ℝ) :
    ∀ T : ℕ, (∀ j < T, 0 < g j) → ∃ m : ℝ, 0 < m ∧ ∀ j < T, m ≤ g j
  | 0 => fun _ => ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | T + 1 => fun h => by
    obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_lt g T (fun j hj => h j (Nat.lt_succ_of_lt hj))
    refine ⟨min m (g T), lt_min hm (h T (Nat.lt_succ_self T)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact (min_le_left _ _).trans (hmle j hj)
    · exact min_le_right _ _

/-- One step of the potential `4 * log c + ζ * log ρ` (with `L = log δ < 0`): a width step
(`c` grows by `δ^(-ζ/2)`, `ρ` arbitrary in `[δ,1]`) or a length step (`c` does not decrease and
`ρ` grows by `δ^(-ζ/2000)`) raises it by at least `-ζ*(ζ/2000)*L`. -/
theorem potential_step {L ζ lc lρ lc' lρ' : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 2000) (hL : L < 0)
    (hlρ : lρ ≤ 0) (hlρ' : L ≤ lρ')
    (h : -ζ / 2 * L + lc ≤ lc' ∨ (lc ≤ lc' ∧ -ζ / 2000 * L + lρ ≤ lρ')) :
    4 * lc + ζ * lρ - ζ * (ζ / 2000) * L ≤ 4 * lc' + ζ * lρ' := by
  rcases h with h | ⟨h1, h2⟩
  · have e1 : ζ * L ≤ ζ * lρ' := mul_le_mul_of_nonneg_left hlρ' hζ.le
    have e2 : ζ * lρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hζ.le hlρ
    have e3 : -(ζ * (ζ / 2000) * L) ≤ -(ζ * L) := by
      have h0 : 0 ≤ -(ζ * L) := by nlinarith
      have h1' : ζ / 2000 ≤ 1 := by linarith
      nlinarith
    nlinarith
  · have e1 : ζ * (-ζ / 2000 * L + lρ) ≤ ζ * lρ' := mul_le_mul_of_nonneg_left h2 hζ.le
    nlinarith

end WangZahlLot.Obl.wz_grains_finite_terminal_iteration

theorem WangZahlLot.wz_grains_finite_terminal_iteration : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(b:Prop)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧b∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀H,H=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)=>∃(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀D,D=(fun(ω ζ d h ρ c:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(t:Bool)=>∃S Z N y w f a g,C d h n x v Y S Z ρ N y w f True∧d^(1-ω/100)≤ρ∧0<g∧(∀(k:Fin N)(p u:V)(r:ℝ),‖u‖=1→d≤r→ r≤ρ→q n {i|i∈S∧f i=k∧p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤d^(-h)*(r/ρ)^(ω*ζ/100)*q n {i|i∈S∧f i=k∧p∈Z i})∧H d h n x v S Z ρ N y w f a c 0 g∧(t=true→ρ≤d^(ω/100)∧d^ζ*(ρ/d)*N/n≤c∧g≤d^(-ζ)))→∀J,J=(fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ c,D ω ζ δ ε ρ c n x v Y false)→∀L,L=(fun(σ ω ζ ε:ℝ)=>∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ c,D ω ζ δ η ρ c n x v Y false→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨(∃ρ' c',D ω ζ δ ε ρ' c' n x v Y true)∨∃ρ' c',D ω ζ δ ε ρ' c' n x v Y false∧(δ^(-ζ/2)*c≤c'∨c≤c'∧δ^(-ζ/2000)*ρ≤ρ'))→(∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→J σ ω ζ ε)→(∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→ε≤ζ/100→L σ ω ζ ε)→∀ζ:ℝ,0<ζ→ζ≤ω/1000→∀ε:ℝ,0<ε→∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨∃ρ c,D ω ζ δ ε ρ c n x v Y true) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσ' hω hω' O hO q hq I hI T hT Q hQ X hX K hK F hF A hA P hP C hC H hH D hD J hJ L hL
    hJall hLall ζ hζ hζω ε hε
  have hζ1 : ζ ≤ 1 / 1000 := by linarith
  -- monotonicity of `O`
  have hOmono : ∀ a b : ℝ, a ≤ b → O a ≤ O b := by
    subst hO; exact fun a b h => ENNReal.ofReal_le_ofReal h
  -- the gain expression is monotone in `α` and `κ`
  have hgainR : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ α κ α' κ' : ℝ, α' ≤ α → 0 ≤ κ' → κ' ≤ κ → ∀ n : ℕ,
      κ' * δ ^ (ω - α') * (n * δ ^ 2) * (n * δ) ^ (-σ) ≤
        κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
    intro δ hδ hδ1 α κ α' κ' hα hκ0 hκ n
    have h1 : δ ^ (ω - α') ≤ δ ^ (ω - α) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h2 : (0:ℝ) ≤ (n * δ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    have h3 : (0:ℝ) ≤ n * δ ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ δ ^ (ω - α') := (Real.rpow_pos_of_pos hδ _).le
    apply mul_le_mul_of_nonneg_right _ h2
    apply mul_le_mul_of_nonneg_right _ h3
    exact mul_le_mul hκ h1 h4 (hκ0.trans hκ)
  -- admissibility is monotone in its exponent
  have hAmono : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η η' : ℝ, η ≤ η' → ∀ n x v Y,
      A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → A δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
    intro δ hδ hδ1 η η' hηη' n x v Y hAδ
    have hp : δ ^ η' ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηη'
    have hpn : δ ^ (-η) ≤ δ ^ (-η') := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηη')
    subst hA
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hAδ
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · refine le_trans (hOmono _ _ ?_) h4
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have : δ ^ η' * n ≤ δ ^ η * n := mul_le_mul_of_nonneg_right hp hn
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · subst hK
      intro W hW
      refine le_trans (h5 W hW) ?_
      gcongr
      exact hOmono _ _ hpn
    · subst hF
      intro u t r hu hr
      refine le_trans (h6 u t r hu hr) ?_
      gcongr
      exact hOmono _ _ (mul_le_mul_of_nonneg_right hpn (Nat.cast_nonneg n))
  -- D is monotone in its error exponent
  have hDmono : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ h h' : ℝ, h ≤ h' → ∀ ρ c n x v Y t,
      D ω ζ δ h ρ c n x v Y t → D ω ζ δ h' ρ c n x v Y t := by
    intro δ hδ hδ1 h h' hhh' ρ c n x v Y t hDh
    have hp : δ ^ h' ≤ δ ^ h := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh'
    have hpn : δ ^ (-h) ≤ δ ^ (-h') := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh')
    subst hD
    obtain ⟨S, Z, N, y, w, f, a, g, hCh, hρ, hg, hbr, hHh, ht⟩ := hDh
    have hρpos : 0 < ρ := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) hρ
    refine ⟨S, Z, N, y, w, f, a, g, ?_, hρ, hg, ?_, ?_, ht⟩
    · subst hC
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hCh
      refine ⟨c1, ?_, c3, c4, ?_, c6, ?_, c8, ?_⟩
      · refine le_trans ?_ c2
        gcongr
        exact hOmono _ _ hp
      · subst hF
        intro u t' r hu hr
        refine le_trans (c5 u t' r hu hr) ?_
        gcongr
        exact hOmono _ _ (mul_le_mul_of_nonneg_right hpn (Nat.cast_nonneg N))
      · subst hq
        intro k k'
        refine le_trans (c7 k k') ?_
        exact mul_le_mul_of_nonneg_right hpn (Nat.cast_nonneg _)
      · intro i hi
        exact le_trans (c9 i hi) hpn
    · intro k p u r hu hr hrρ
      refine le_trans (hbr k p u r hu hr hrρ) ?_
      have h0 : (0:ℝ) ≤ (r / ρ) ^ (ω * ζ / 100) :=
        Real.rpow_nonneg (div_nonneg (hδ.le.trans hr) hρpos.le) _
      subst hq
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hpn h0
    · subst hH
      obtain ⟨Lc, z, e, Hs, γ, m, hU⟩ := hHh
      refine ⟨Lc, z, e, Hs, γ, m, ?_⟩
      obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := hU
      refine ⟨u1, u2, u3, u4, u5, u6, u7, ?_, u9, u10, u11, u12⟩
      refine le_trans (hOmono _ _ ?_) u8
      have ha : 0 ≤ a := hδ.le.trans u1
      have hρc : 0 ≤ ρ * c := ha.trans u2
      have hc : 0 ≤ c := hρc.trans u3
      have hL0 : (0:ℝ) ≤ Lc := Nat.cast_nonneg Lc
      apply mul_le_mul_of_nonneg_right _ hc
      apply mul_le_mul_of_nonneg_right _ hρc
      apply mul_le_mul_of_nonneg_right _ ha
      exact mul_le_mul_of_nonneg_right hp hL0
  -- a D-state has `δ ≤ c ≤ 1` and `δ ≤ ρ ≤ 1`
  have hDbd : ∀ δ h ρ c n x v Y t, 0 < δ → D ω ζ δ h ρ c n x v Y t →
      δ ≤ c ∧ c ≤ 1 ∧ δ ≤ ρ ∧ ρ ≤ 1 := by
    intro δ h ρ c n x v Y t hδ hDh
    subst hD
    obtain ⟨S, Z, N, y, w, f, a, g, -, -, -, -, hHh, -⟩ := hDh
    subst hH
    obtain ⟨Lc, z, e, Hs, γ, m, u1, u2, u3, u4, -⟩ := hHh
    have hc : 0 < c := by linarith
    refine ⟨by linarith, u4, ?_, ?_⟩
    · nlinarith
    · nlinarith
  -- the terminal budget
  obtain ⟨e₀, he₀pos, he₀ε, he₀ζ⟩ : ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ ε ∧ e₀ ≤ ζ / 100 :=
    ⟨min ε (ζ / 100), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  -- the improvement step, as functions of the admissible budget
  have hL3 : ∀ e : {e : ℝ // 0 < e ∧ e ≤ ζ / 100}, L σ ω ζ e.1 :=
    fun e => hLall ζ hζ hζω e.1 e.2.1 e.2.2
  subst hL
  beta_reduce at hL3
  choose αL κL ηL dL hLs using hL3
  -- the backward chain of budgets: `b (j+1)` is the input tolerance of the step at `b j`
  obtain ⟨b, hb0, hbs⟩ : ∃ b : ℕ → {e : ℝ // 0 < e ∧ e ≤ ζ / 100},
      (b 0).1 = e₀ ∧ ∀ j, (b (j + 1)).1 = ηL (b j) :=
    ⟨fun j => Nat.rec ⟨e₀, he₀pos, he₀ζ⟩
      (fun _ e => ⟨ηL e, (hLs e).2.2.1, (hLs e).2.2.2.1.trans e.2.2⟩) j, rfl, fun j => rfl⟩
  have hbanti : Antitone (fun j => (b j).1) :=
    antitone_nat_of_succ_le (fun j => by rw [hbs]; exact (hLs (b j)).2.2.2.1)
  -- the horizon
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℕ, 4 + ζ < Tn * (ζ * (ζ / 2000)) := by
    obtain ⟨Tn, hTn⟩ := exists_nat_gt ((4 + ζ) / (ζ * (ζ / 2000)))
    exact ⟨Tn, by rwa [div_lt_iff₀ (by positivity)] at hTn⟩
  -- initialization at the last budget
  have hJ' := hJall ζ hζ hζω (b Tn).1 (b Tn).2.1
  subst hJ
  beta_reduce at hJ'
  obtain ⟨αJ, κJ, ηJ, dJ, hαJ, hκJ, hηJ, hηJb, hdJ, hdJ1, hJs⟩ := hJ'
  -- the final gain constants and cutoff lie below those of every step
  obtain ⟨mα, hmα, hmαle⟩ :=
    WangZahlLot.Obl.wz_grains_finite_terminal_iteration.exists_pos_le_of_lt
      (fun j => αL (b j)) Tn (fun j _ => (hLs (b j)).1)
  obtain ⟨mκ, hmκ, hmκle⟩ :=
    WangZahlLot.Obl.wz_grains_finite_terminal_iteration.exists_pos_le_of_lt
      (fun j => κL (b j)) Tn (fun j _ => (hLs (b j)).2.1)
  obtain ⟨md, hmd, hmdle⟩ :=
    WangZahlLot.Obl.wz_grains_finite_terminal_iteration.exists_pos_le_of_lt
      (fun j => dL (b j)) Tn (fun j _ => (hLs (b j)).2.2.2.2.1)
  have hηJε : ηJ ≤ ε :=
    calc ηJ ≤ (b Tn).1 := hηJb
      _ ≤ (b 0).1 := hbanti (Nat.zero_le Tn)
      _ = e₀ := hb0
      _ ≤ ε := he₀ε
  refine ⟨min αJ mα, min κJ mκ, ηJ, min dJ md, lt_min hαJ hmα, lt_min hκJ hmκ, hηJ, hηJε,
    lt_min hdJ hmd, (min_le_left _ _).trans hdJ1, ?_⟩
  intro δ hδ hδd n x v Y hAδ
  have hδ1 : δ < 1 := by
    have := (min_le_left dJ md).trans hdJ1
    linarith
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hng, hnt⟩ := hcon
  have hlogmul : ∀ y z : ℝ, 0 < z → Real.log (δ ^ y * z) = y * Real.log δ + Real.log z :=
    fun y z hz => by
      rw [Real.log_mul (Real.rpow_pos_of_pos hδ y).ne' hz.ne', Real.log_rpow hδ]
  -- the invariant after `s` improvement steps
  have key : ∀ s : ℕ, s ≤ Tn → ∃ ρ c, D ω ζ δ (b (Tn - s)).1 ρ c n x v Y false ∧
      (4 + ζ - s * (ζ * (ζ / 2000))) * Real.log δ ≤ 4 * Real.log c + ζ * Real.log ρ := by
    intro s
    induction s with
    | zero =>
      intro _
      rcases hJs δ hδ (hδd.trans (min_le_left _ _)) n x v Y hAδ with hg | ⟨ρ, c, hDρc⟩
      · exact absurd (le_trans (hOmono _ _ (hgainR δ hδ hδ1.le αJ κJ _ _ (min_le_left _ _)
          (lt_min hκJ hmκ).le (min_le_left _ _) n)) hg) hng
      · refine ⟨ρ, c, by simpa using hDρc, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hDbd δ _ ρ c n x v Y false hδ hDρc
        have l1 : Real.log δ ≤ Real.log c := Real.log_le_log hδ h1
        have l2 : Real.log δ ≤ Real.log ρ := Real.log_le_log hδ h3
        have l3 : ζ * Real.log δ ≤ ζ * Real.log ρ := mul_le_mul_of_nonneg_left l2 hζ.le
        simp only [Nat.cast_zero, zero_mul, sub_zero]
        nlinarith
    | succ s ih =>
      intro hs
      obtain ⟨ρ, c, hDs, hpot⟩ := ih (Nat.le_of_succ_le hs)
      obtain ⟨j, hj⟩ : ∃ j, j = Tn - (s + 1) := ⟨_, rfl⟩
      have hjs : Tn - s = j + 1 := by omega
      have hjlt : j < Tn := by omega
      rw [← hj]
      rw [hjs, hbs] at hDs
      have hηle : ηJ ≤ ηL (b j) := by
        rw [← hbs]
        exact hηJb.trans (hbanti (Nat.succ_le_of_lt hjlt))
      have hAj := hAmono δ hδ hδ1.le ηJ (ηL (b j)) hηle n x v Y hAδ
      have hδj : δ ≤ dL (b j) := hδd.trans ((min_le_right _ _).trans (hmdle j hjlt))
      obtain ⟨hc1, hc2, hρ1, hρ2⟩ := hDbd δ _ ρ c n x v Y false hδ hDs
      rcases (hLs (b j)).2.2.2.2.2.2 δ hδ hδj n x v Y hAj ρ c hDs with
        hg | ⟨ρ', c', hDt⟩ | ⟨ρ', c', hDf, hprog⟩
      · exact absurd (le_trans (hOmono _ _ (hgainR δ hδ hδ1.le (αL (b j)) (κL (b j)) _ _
          ((min_le_right _ _).trans (hmαle j hjlt)) (lt_min hκJ hmκ).le
          ((min_le_right _ _).trans (hmκle j hjlt)) n)) hg) hng
      · refine absurd ⟨ρ', c', hDmono δ hδ hδ1.le _ ε ?_ ρ' c' n x v Y true hDt⟩ hnt
        calc (b j).1 ≤ (b 0).1 := hbanti (Nat.zero_le j)
          _ = e₀ := hb0
          _ ≤ ε := he₀ε
      · refine ⟨ρ', c', hDf, ?_⟩
        obtain ⟨hc1', hc2', hρ1', hρ2'⟩ := hDbd δ _ ρ' c' n x v Y false hδ hDf
        have hcpos : 0 < c := lt_of_lt_of_le hδ hc1
        have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ1
        have hlρ : Real.log ρ ≤ 0 := Real.log_nonpos hρpos.le hρ2
        have hlρ' : Real.log δ ≤ Real.log ρ' := Real.log_le_log hδ hρ1'
        have hstep := WangZahlLot.Obl.wz_grains_finite_terminal_iteration.potential_step
          (lc := Real.log c) (lρ := Real.log ρ) (lc' := Real.log c') (lρ' := Real.log ρ')
          hζ (by linarith) hlogδ hlρ hlρ' (by
            rcases hprog with hw | ⟨hc', hr'⟩
            · left
              have := Real.log_le_log (by positivity) hw
              rwa [hlogmul _ _ hcpos] at this
            · right
              refine ⟨Real.log_le_log hcpos hc', ?_⟩
              have := Real.log_le_log (by positivity) hr'
              rwa [hlogmul _ _ hρpos] at this)
        push_cast
        nlinarith
  obtain ⟨ρ, c, hDf, hpot⟩ := key Tn le_rfl
  obtain ⟨h1, h2, h3, h4⟩ := hDbd δ _ ρ c n x v Y false hδ hDf
  have l1 : Real.log c ≤ 0 := Real.log_nonpos (by linarith) h2
  have l2 : Real.log ρ ≤ 0 := Real.log_nonpos (by linarith) h4
  have l3 : ζ * Real.log ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hζ.le l2
  have l4 : 0 < (4 + ζ - Tn * (ζ * (ζ / 2000))) * Real.log δ :=
    mul_pos_of_neg_of_neg (by linarith) hlogδ
  linarith
