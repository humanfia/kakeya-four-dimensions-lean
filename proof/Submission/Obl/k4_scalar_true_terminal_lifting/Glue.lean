import Submission.Obl.k4_scalar_true_terminal_lifting.Lift

/-!
# From the terminal floor comparison to the lifting theorem

`liftStatement_of_badWorldsSmall : BadWorldsSmall → LiftStatement`.

For a requested loss `ε''`, take the ratio threshold `δ = ε''/4`, the power `c` of the bad
mass, and the q-loss `ε' = min (ε''/8) (c/2)`. At every index `k` where `q` has a true terminal
chart with loss `ε'` and where the bad mass, the refinement loss and `N` are under control,
delete the pieces in bad q-worlds (the chart keeps loss `2ε'`), lift the remaining chart
through the `k`-th index of the refinement and relax its exponents. Frequent occurrence passes
to the original indices along the strictly monotone `φ`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

section

variable {p q : Code} {r b h : ℝ} {φ : ℕ → ℕ} {ε : ℕ → ℝ} {B : ℕ} {T : ℕ → ℕ}
  {γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k))}
  {j : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k)}
  {A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ))}
  {C : (k : ℕ) → Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
  {u v J : (k : ℕ) → Fin (W q k) → ℝ}
  {P : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ}
  {Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k))}
  {θ : (k : ℕ) → Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))}

/-- The `k`-th index of a refinement body. -/
noncomputable def RefBody.step (hR : RefBody p q r b h φ ε B T γ j A C u v J P Λ θ)
    (k : ℕ) : RefStep p q r b k (φ k) where
  B₁ := B
  T₁ := T k
  h₁ := h + ε k
  ε₁ := ε k
  γ₁ := γ k
  j₁ := j k
  A₁ := A k
  C₁ := C k
  u₁ := u k
  v₁ := v k
  J₁ := J k
  P₁ := P k
  Λ₁ := Λ k
  θ := θ k
  hN := (hR.2.2.2.2.1 k).1
  hcd := (hR.2.2.2.2.1 k).2
  hθ := hR.2.2.2.2.2.1 k
  hZ := hR.2.2.2.2.2.2 k

end

theorem chart_mono {p : Code} {B B' : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool} {k : ℕ}
    (hc : Chart p B r b h ε isTrue k) (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h')
    (hε : ε ≤ ε') : Chart p B' r b h' ε' isTrue k := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩ := hc
  exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ, chartData_mono hcd hN hB hh hε⟩

open Classical in
/-- Deleting the pieces in bad worlds of a chart whose bad worlds carry weighted mass at most
`N ^ (-2ε')` keeps a chart with loss `2ε'`. -/
theorem select_good {q : Code} {B' : ℕ} {h₂ ε' : ℝ} {k : ℕ}
    (Q : ChartW q B' (L q) (L q) h₂ ε' true k) (bad : Fin (W q k) → Prop) (hε' : 0 ≤ ε')
    (hN1 : 1 ≤ N q k) (hN : 2 ≤ N q k ^ ε')
    (hbad : (∑ a : Fin (W q k), if bad a then ENNReal.ofReal (ω q k a) * mu q k a Set.univ
      else 0) ≤ ENNReal.ofReal (N q k ^ (-(2 * ε')))) :
    ∃ Q' : ChartW q B' (L q) (L q) h₂ (2 * ε') true k, ∀ d, ¬ bad (Q'.γ d) := by
  set s : Finset (Fin Q.n) := Finset.univ.filter (fun d => ¬ bad (Q.γ d)) with hs
  let σ : Fin s.card → Fin Q.n := fun i => s.orderEmbOfFin rfl i
  have hσinj : Function.Injective σ := (s.orderEmbOfFin rfl).injective
  have hσmem : ∀ i, σ i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  have hσsurj : ∀ d ∈ s, ∃ i, σ i = d := by
    intro d hd
    have : d ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hd
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  have hcd := Q.hcd
  have hfull : ENNReal.ofReal (N q k ^ (-ε')) ≤ ∑ a : Fin (W q k),
      ENNReal.ofReal (ω q k a) * mu q k a {z | ∃ i, Q.γ i = a ∧ z ∈ Q.C i} := by
    unfold ChartData at hcd
    exact hcd.2.2.2.2.2.2.2.2.2
  have hsplit := mass_le_good_add_bad Q.γ Q.C bad
  have hgood_eq : (∑ a : Fin (W q k), ENNReal.ofReal (ω q k a) *
      mu q k a {z | ∃ i, Q.γ i = a ∧ ¬ bad (Q.γ i) ∧ z ∈ Q.C i}) =
      ∑ a : Fin (W q k), ENNReal.ofReal (ω q k a) *
        mu q k a {z | ∃ i, Q.γ (σ i) = a ∧ z ∈ Q.C (σ i)} := by
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext z
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨d, hd, hb, hz⟩
      obtain ⟨i, rfl⟩ := hσsurj d (by simp [hs, hb])
      exact ⟨i, hd, hz⟩
    · rintro ⟨i, hi, hz⟩
      have := hσmem i
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact ⟨σ i, hi, this, hz⟩
  have hN0 : 0 < N q k := by linarith
  have hx : 2 * N q k ^ (-(2 * ε')) ≤ N q k ^ (-ε') := by
    have h1 : N q k ^ (-(2 * ε')) = N q k ^ (-ε') * N q k ^ (-ε') := by
      rw [← Real.rpow_add hN0]
      ring_nf
    have h2 : N q k ^ (-ε') ≤ 1 / 2 := by
      rw [Real.rpow_neg hN0.le, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hN
    have h3 : 0 ≤ N q k ^ (-ε') := (Real.rpow_pos_of_pos hN0 _).le
    rw [h1]
    nlinarith
  have hmass : ENNReal.ofReal (N q k ^ (-(2 * ε'))) ≤ ∑ a : Fin (W q k),
      ENNReal.ofReal (ω q k a) * mu q k a {z | ∃ i, Q.γ (σ i) = a ∧ z ∈ Q.C (σ i)} := by
    rw [← hgood_eq]
    have hpos : 0 ≤ N q k ^ (-(2 * ε')) := (Real.rpow_pos_of_pos hN0 _).le
    have key : ENNReal.ofReal (N q k ^ (-(2 * ε'))) + ENNReal.ofReal (N q k ^ (-(2 * ε'))) ≤
        (∑ a : Fin (W q k), ENNReal.ofReal (ω q k a) *
          mu q k a {z | ∃ i, Q.γ i = a ∧ ¬ bad (Q.γ i) ∧ z ∈ Q.C i}) +
          ENNReal.ofReal (N q k ^ (-(2 * ε'))) := by
      calc ENNReal.ofReal (N q k ^ (-(2 * ε'))) + ENNReal.ofReal (N q k ^ (-(2 * ε')))
          = ENNReal.ofReal (2 * N q k ^ (-(2 * ε'))) := by
            rw [← ENNReal.ofReal_add hpos hpos]
            congr 1
            ring
        _ ≤ ENNReal.ofReal (N q k ^ (-ε')) := ENNReal.ofReal_le_ofReal hx
        _ ≤ _ := hfull
        _ ≤ _ := hsplit
        _ ≤ _ := add_le_add le_rfl hbad
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top key
  refine ⟨⟨Q.T, s.card, fun i => Q.γ (σ i), fun i => Q.j (σ i), fun i => Q.A (σ i),
    fun i => Q.C (σ i), fun i => Q.u (σ i), fun i => Q.v (σ i), fun i => Q.J (σ i),
    fun i => Q.P (σ i), fun a z => Finset.univ.filter (fun i => σ i ∈ Q.Λ a z),
    chartData_select (chartData_mono Q.hcd hN1 le_rfl le_rfl (by linarith)) σ hσinj hmass⟩,
    ?_⟩
  intro i
  have := hσmem i
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem liftStatement_of_badWorldsSmall (hbad : BadWorldsSmall) : LiftStatement := by
  intro p q r b h a hp hq hr hrL hrb hbL hh hLq hRef hCost
  obtain ⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ, hR⟩ := (refinement_iff p q r b h).1 hRef
  have hR' := hR
  unfold RefBody at hR'
  obtain ⟨hφ, hεpos, hεt, hB, -, -, -⟩ := hR'
  obtain ⟨ha, B', hB', hcharts⟩ := hCost
  have hp' := hp
  unfold Exact at hp'
  have hq' := hq
  unfold Exact at hq'
  have hpN : ∀ k, 2 ≤ N p k := hp'.1.1
  have hqNt : Tendsto (N q) atTop atTop := hq'.1.2.1
  have hpω : ∀ k a, 0 ≤ ω p k a := fun k a => (hp'.2.1 k).2.1 a
  have hpν : ∀ k a, IsProbabilityMeasure (ν p k a) := fun k a => ((hp'.2.1 k).2.2.2.1 a).1
  refine ⟨by linarith, 2 * B' + 2 * B + 9, by omega, ?_⟩
  intro ε'' hε''
  obtain ⟨c, hc, hbadev⟩ := hbad p q r b h hp hq hr hrL hrb hbL hh hLq φ ε B T γ j A C u v J P
    Λ θ hR (ε'' / 4) (by linarith)
  set ε' : ℝ := min (ε'' / 8) (c / 2) with hε'def
  have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
  have hε'1 : ε' ≤ ε'' / 8 := min_le_left _ _
  have hε'2 : ε' ≤ c / 2 := min_le_right _ _
  have hfreq := hcharts ε' hε'pos
  have hev1 : ∀ᶠ k in atTop, ε k < ε'' / 8 := (tendsto_order.1 hεt).2 _ (by linarith)
  have hev2 : ∀ᶠ k in atTop, ε k < 1 := (tendsto_order.1 hεt).2 _ one_pos
  have hev3 : ∀ᶠ k in atTop, 2 ≤ N q k ^ ε' :=
    ((tendsto_rpow_atTop hε'pos).comp hqNt).eventually_ge_atTop 2
  have hev4 : ∀ᶠ k in atTop, 4 ≤ N q k ^ (ε'' / 4) :=
    ((tendsto_rpow_atTop (by linarith)).comp hqNt).eventually_ge_atTop 4
  have hfin : ∃ᶠ k in atTop,
      Chart p (2 * B' + 2 * B + 9) (L p) (L p) (h + a + ε'') ε'' true (φ k) := by
    refine (hfreq.and_eventually (hbadev.and (hev1.and (hev2.and (hev3.and hev4))))).mono ?_
    rintro k ⟨hch, hbk, he1, he2, he3, he4⟩
    let S := hR.step k
    have hSN : N q k = N p (φ k) := S.hN
    have hN2 : 2 ≤ N p (φ k) := hpN (φ k)
    have hNq2 : 2 ≤ N q k := hSN ▸ hN2
    have hNq0 : 0 < N q k := by linarith
    have hNq1 : 1 ≤ N q k := by linarith
    obtain ⟨Q⟩ := (chart_iff_nonempty _ _ _ _ _ _ _ _).1 hch
    classical
    let bad : Fin (W q k) → Prop := fun i => ν p (φ k) (γ k i) (A k i) <
      ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - ε'' / 4) * J k i)
    have hbad_le : (∑ i : Fin (W q k), if bad i then ENNReal.ofReal (ω q k i) * mu q k i Set.univ
        else 0) ≤ ENNReal.ofReal (N q k ^ (-(2 * ε'))) := by
      have heq : (∑ i : Fin (W q k), if bad i then ENNReal.ofReal (ω q k i) *
          mu q k i Set.univ else 0) = badMass p q φ γ A J (ε'' / 4) k := by
        unfold badMass
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : bad i
        · have hi' : ν p (φ k) (γ k i) (A k i) <
              ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - ε'' / 4) * J k i) := hi
          simp [hi, hi']
        · have hi' : ¬ ν p (φ k) (γ k i) (A k i) <
              ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - ε'' / 4) * J k i) := hi
          simp [hi, hi']
      rw [heq]
      refine hbk.trans (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow_of_exponent_le hNq1 (by linarith)
    have hbad_le' : (∑ i : Fin (W q k), @ite _ (bad i) (Classical.propDecidable (bad i))
        (ENNReal.ofReal (ω q k i) * mu q k i Set.univ) 0) ≤
        ENNReal.ofReal (N q k ^ (-(2 * ε'))) := by
      refine le_trans (le_of_eq ?_) hbad_le
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : bad i <;> simp [hi]
    obtain ⟨Q', hQ'⟩ := select_good Q bad hε'pos.le hNq1 he3 hbad_le'
    have hgood : ∀ d, ENNReal.ofReal (N p (φ k) ^ (f q (L q) - f p (L p) - ε'' / 4) *
        S.J₁ (Q'.γ d)) ≤ ν p (φ k) (S.γ₁ (Q'.γ d)) (S.A₁ (Q'.γ d)) := by
      intro d
      have := hQ' d
      simp only [bad, not_lt] at this
      rw [← hSN]
      exact this
    have hεk0 : 0 ≤ ε k := (hεpos k).le
    have hpow : 4 * N p (φ k) ^ (ε k + 2 * ε') ≤ N p (φ k) ^ ε'' := by
      rw [← hSN]
      have h1 : N q k ^ (ε k + 2 * ε') ≤ N q k ^ (3 * ε'' / 4) :=
        Real.rpow_le_rpow_of_exponent_le hNq1 (by linarith)
      have h2 : N q k ^ ε'' = N q k ^ (ε'' / 4) * N q k ^ (3 * ε'' / 4) := by
        rw [← Real.rpow_add hNq0]
        ring_nf
      rw [h2]
      have h3 : 0 ≤ N q k ^ (ε k + 2 * ε') := (Real.rpow_pos_of_pos hNq0 _).le
      nlinarith
    have hlift := S.lift_chart Q' hN2 (hpω (φ k)) (hpν (φ k)) hr hLq hbL he2.le
      (by linarith) hgood (δ := ε'' / 4) (ε₃ := ε'') (by show ε k + 2 * ε' + ε'' / 4 ≤ ε''; linarith)
      (by linarith) hεk0 hpow
    refine chart_mono hlift (by linarith) le_rfl ?_ le_rfl
    show h + ε k + (a + ε') ≤ h + a + ε''
    linarith
  exact hφ.tendsto_atTop.frequently hfin

end Submission.Obl.k4_scalar_true_terminal_lifting
