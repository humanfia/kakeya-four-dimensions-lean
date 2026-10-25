import Mathlib
import Submission.Obl.k4_contact_equal_rate_affine_palettes.NativeCoarse
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.SubpowerEnvelope
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# The native coarse affine cover

`native_coarse_cover` proves `NativeCoarseClaim`, the native unit-width stage of the split of o241
proposed by x0881 (`NativeCoarseStatement` on x0881's branch, statement copied verbatim): from the
native hypotheses alone (contact, the frozen `Basic` clauses and the frozen caps), a subpower `H`
and eventually at most `H` affine functions fitting almost every native incidence on all of
`[0,1]` to within `H`.

For each `ε` the velocity scale `N^{-v}` with `v = min(ε, e₀, 1)/1000`, the mesh `N^{-1}` and the
caps at `R = 2 + 1/v` feed `native_palette_at`; its error `C Λ⁸⁰` is at most `N^ε` eventually.
The subpower envelope (x0834's `exists_subpower_envelope`) gives `H`.
-/

namespace Submission.Obl.k4_contact_equal_rate_affine_palettes

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_contact_fine_labels_from_coarse_cover

noncomputable section

/-- The native unit-width stage, verbatim from x0881's split proposal of o241. -/
abbrev NativeCoarseClaim : Prop :=
  ∀ (N K:ℕ → ℝ),(∀ k,2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k,1 ≤ K k) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,K k ≤ N k ^ ε) → ∀ d S e₀:ℝ,0 ≤ d → d < 1 → 0 < S → S ≤ 1 → 0 < e₀ → ∀ (α:Type) [MeasurableSpace α] (ν:ℕ → MeasureTheory.Measure α) (μ ρ:ℕ → MeasureTheory.Measure (α × ℝ)) (π:ℕ → MeasureTheory.Measure ℝ) (b:ℕ → α → Fin 6 → ℝ) (P:ℕ → MvPolynomial (Fin 4) ℝ),(∀ k,∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) → (fun x:ℕ → α → ℝ → Fin 4 → ℝ => (fun z:ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (∀ k,Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k,|b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k,(∀ t ∈ Set.Icc (0:ℝ) 1,|MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k))|)) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ r s v:ℝ,R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a:ℤ,π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a v₀:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∃ H:ℕ → ℝ,(∀ k,1 ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ N k ^ ε) ∧ ∀ᶠ k in Filter.atTop,∃ (M:ℕ) (L:Fin M → Fin 4 → ℝ),(M:ℝ) ≤ H k ∧ ∀ᵐ p ∂μ k,∃ u:Fin M,∀ t ∈ Set.Icc (0:ℝ) 1,|(x k p.1 t) 3 - (L u 0 + L u 1 * t + L u 2 * (x k p.1 t) 1 + L u 3 * (x k p.1 t) 2)| ≤ H k)) (fun k Nk r p e => ⌊(![p.2,(x k p.1 p.2) 1,(x k p.1 p.2) 2]:Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5])


/-- The global loss of the native step, polynomially. -/
theorem nativeΛ_pow_le {K N v : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hv : 0 < v) :
    labelΛ K (N ^ (-v)) (nativeLam K) ^ 80 ≤
      ((4 * 10 ^ 4 * 54 * 7) ^ 80 : ℝ) * K ^ 720 * N ^ (240 * v) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hNv : 0 < N ^ (-v) := Real.rpow_pos_of_pos hN0 _
  have hpow : (N ^ (-v)) ^ 3 = N ^ (-(3 * v)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hΛ : labelΛ K (N ^ (-v)) (nativeLam K) ≤ (4 * 10 ^ 4 * 54 * 7) * K ^ 9 * N ^ (3 * v) := by
    rw [labelΛ, nativeLam, hpow]
    have hinv : N ^ (-(3 * v)) * N ^ (3 * v) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have hpos : 0 < N ^ (3 * v) := Real.rpow_pos_of_pos hN0 _
    rw [div_le_iff₀ (by positivity)]
    have hinv' : N ^ (3 * v) * N ^ (-(3 * v)) = 1 := by rw [mul_comm]; exact hinv
    have e : 4 * 10 ^ 4 * 54 * 7 * K ^ 9 * N ^ (3 * v) *
        (1 / (54 * K * ((2 * K + 5) * K)) * N ^ (-(3 * v))) =
        (4 * 10 ^ 4 * 54 * 7 * K ^ 9) * (1 / (54 * K * ((2 * K + 5) * K))) *
          (N ^ (3 * v) * N ^ (-(3 * v))) := by ring
    rw [e, hinv', mul_one]
    have e2 : (4 * 10 ^ 4 * 54 * 7 * K ^ 9) * (1 / (54 * K * ((2 * K + 5) * K))) =
        (4 * 10 ^ 4 * 7) * K ^ 9 / ((2 * K + 5) * K ^ 2) := by field_simp
    rw [e2, le_div_iff₀ (by positivity)]
    have h7 : 2 * K + 5 ≤ 7 * K := by linarith
    have : 4 * 10 ^ 4 * K ^ 6 * ((2 * K + 5) * K ^ 2) ≤ 4 * 10 ^ 4 * K ^ 6 * (7 * K * K ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 (by positivity)) (by positivity)
    have e3 : 4 * 10 ^ 4 * K ^ 6 * (7 * K * K ^ 2) = 4 * 10 ^ 4 * 7 * K ^ 9 := by ring
    linarith
  have hΛ0 : 0 ≤ labelΛ K (N ^ (-v)) (nativeLam K) := by
    rw [labelΛ]; have := nativeLam_pos hK; positivity
  calc labelΛ K (N ^ (-v)) (nativeLam K) ^ 80
      ≤ ((4 * 10 ^ 4 * 54 * 7) * K ^ 9 * N ^ (3 * v)) ^ 80 := pow_le_pow_left₀ hΛ0 hΛ 80
    _ = ((4 * 10 ^ 4 * 54 * 7) ^ 80 : ℝ) * K ^ 720 * N ^ (240 * v) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_natCast (N ^ (3 * v)),
        ← Real.rpow_mul hN0.le]
      congr 2; push_cast; ring


/-- Native good incidences are almost everything. Adapted from x0834's `Model.Valid.ae_good`
(branch x0834 of o241, file `ModelGood.lean`), with the time `1` excluded. -/
theorem native_good_ae {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (P : MvPolynomial (Fin 4) ℝ) (K Ne : ℝ)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcoeff : ∀ᵐ l ∂ν, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (hnative : ∀ᵐ p ∂μ, (∀ t ∈ Icc (0 : ℝ) 1, |eval (point (b p.1) t) P| ≤ K ∧
      |eval (point (b p.1) t) (pderiv 3 P)| ≤ K ∧
      |eval (point (b p.1) t) (pderiv 3 (pderiv 3 P))| ≤ K) ∧
      K⁻¹ ≤ |eval (point (b p.1) p.2) (pderiv 3 P)|)
    (hcon : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ Ne) :
    ∀ᵐ u ∂μ, NativeGood K Ne b P u := by
  have hbm : Measurable (fun u : α × ℝ => b u.1) := hb.comp measurable_fst
  have hcoord (i : Fin 6) : Measurable (fun u : α × ℝ => b u.1 i) :=
    (measurable_pi_apply i).comp hbm
  have hset : MeasurableSet {u : α × ℝ | |b u.1 0| + |b u.1 1| + |b u.1 3| + |b u.1 4| ≤ K} := by
    apply measurableSet_le _ measurable_const
    exact (((hcoord 0).abs.add (hcoord 1).abs).add (hcoord 3).abs).add (hcoord 4).abs
  have hprod : ∀ᵐ (u : α × ℝ) ∂ν.prod volume,
      |b u.1 0| + |b u.1 1| + |b u.1 3| + |b u.1 4| ≤ K := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards [hcoeff] with l hl
    exact ae_of_all _ (fun _ => hl)
  have hμcoeff := (Measure.ae_smul_measure hprod (ENNReal.ofReal K)).filter_mono (ae_mono hdom)
  have htime : ∀ᵐ u ∂μ, u ∈ (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) := ae_iff.mpr hsupp
  have hone : ∀ᵐ u ∂μ, u.2 ≠ 1 := by
    have hnull : (ν.prod volume) {u : α × ℝ | u.2 = 1} = 0 := by
      have : {u : α × ℝ | u.2 = 1} = univ ×ˢ {(1 : ℝ)} := by ext u; simp
      rw [this, Measure.prod_prod, Real.volume_singleton, mul_zero]
    have h2 : μ {u : α × ℝ | u.2 = 1} = 0 := by
      apply le_antisymm _ bot_le
      calc μ {u : α × ℝ | u.2 = 1} ≤ (ENNReal.ofReal K • (ν.prod volume)) {u | u.2 = 1} :=
            hdom _
        _ = 0 := by rw [Measure.smul_apply, hnull, smul_zero]
    rw [ae_iff]
    simpa only [ne_eq, not_not] using h2
  filter_upwards [htime, hμcoeff, hcon, hnative, hone] with u hu hc hcontact hn h1
  have hu2 := hu.2
  refine ⟨⟨hu2.1, lt_of_le_of_ne hu2.2 h1⟩, hc, hcontact, hn.1, hn.2⟩


set_option maxHeartbeats 8000000 in
/-- **The native coarse affine cover.** -/
theorem native_coarse_cover : NativeCoarseClaim := by
  intro N K hN hNt hK d S e₀ hd0 hd1 hS0 hS1 he₀ α inst ν μ ρ π b P hcontact hBasic hCaps
  beta_reduce at hBasic hCaps ⊢
  obtain ⟨C, hC1, hpal⟩ := native_palette_at
  have hN1 : ∀ k, 1 ≤ N k := fun k => le_trans (by norm_num) (hN k)
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le (by norm_num) (hN k)
  let Pk : ℕ → ℝ → Prop := fun k E => ∃ L : Fin 3 → Fin 4 → ℝ, ∀ᵐ p ∂μ k, ∃ i : Fin 3,
    ∀ t ∈ Icc (0 : ℝ) 1, |point (b k p.1) t 3 - (L i 0 + L i 1 * t + L i 2 * point (b k p.1) t 1 +
      L i 3 * point (b k p.1) t 2)| ≤ E
  have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Pk k (N k ^ ε) := by
    intro ε hε
    set m := min ε (min e₀ 1) with hmdef
    have hm : 0 < m := lt_min hε (lt_min he₀ one_pos)
    have hmε : m ≤ ε := min_le_left _ _
    have hme : m ≤ e₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hm1 : m ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    set v := m / 1000 with hvdef
    have hv : 0 < v := by positivity
    set R := 2 + 1 / v with hRdef
    have hR : 1 < R := by have : 0 < 1 / v := by positivity
                          linarith
    have hRinv : R⁻¹ ≤ v := by
      rw [inv_le_comm₀ (by linarith) hv]
      have : v⁻¹ = 1 / v := by rw [one_div]
      linarith
    have hvR : v ≤ R := by
      have : v ≤ 1 := by rw [hvdef]; linarith
      linarith
    have h1R : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
    set c₁ : ℝ := (4 * 10 ^ 4 * 54 * 7) ^ 80 with hc₁
    have hc₁0 : 0 ≤ c₁ := by positivity
    filter_upwards [hCaps R hR,
      Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hN1 hNt hK.1 hK.2
        6 (show -(S * v) < 0 by nlinarith) (show (0 : ℝ) ≤ 2800 by norm_num),
      Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hN1 hNt hK.1 hK.2
        720 (show 240 * v - e₀ < 0 by rw [hvdef]; linarith)
        (show (0 : ℝ) ≤ 2 * C * c₁ by positivity),
      Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hN1 hNt hK.1 hK.2
        721 (show 240 * v - 1 < 0 by rw [hvdef]; linarith)
        (show (0 : ℝ) ≤ 42 * C * c₁ by positivity),
      Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hN1 hNt hK.1 hK.2
        720 (show 240 * v < ε by rw [hvdef]; linarith)
        (show (0 : ℝ) ≤ C * c₁ by positivity)] with k hcaps hs1 hs2 hs3 hs4
    simp only [Real.rpow_zero] at hs1 hs2 hs3
    obtain ⟨hb, hν, -, hdom, hρμ, hsupp, hρ, hPdeg, hcoeff, hnative⟩ := hBasic k
    have hKk : 1 ≤ K k := hK.1 k
    have hK0 : 0 < K k := by linarith
    have hNk := hNpos k
    obtain ⟨hcπ, hcP, hcJ⟩ := hcaps 1 0 v h1R hR.le le_rfl (by linarith) hRinv hvR
    have hgood := native_good_ae (ν k) (μ k) (b k) hb (P k) (K k) (N k ^ (-e₀)) hdom hsupp
      hcoeff hnative (hcontact k)
    have hmass : ENNReal.ofReal (K k)⁻¹ ≤ μ k univ := hρ.trans (hρμ univ)
    have hNe0 : 0 ≤ N k ^ (-e₀) := (Real.rpow_pos_of_pos hNk _).le
    have hNe1 : N k ^ (-e₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
    have hNr0 : 0 < N k ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hNk _
    have hNr2 : N k ^ (-(1 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (hN k)
    have hNv0 : 0 < N k ^ (-v) := Real.rpow_pos_of_pos hNk _
    have hNv1 : N k ^ (-v) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
    have hπb0 : 0 ≤ K k * N k ^ (-S * v) := by positivity
    -- the caps in native form
    have hr3 : N k ^ (-3 * (1 : ℝ) - d * 0) = (N k ^ (-(1 : ℝ))) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNk.le]; congr 1; push_cast; ring
    have hzero : N k ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    have hcapP : ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {u | baseMesh (N k ^ (-(1 : ℝ)))
        (nbase (b k) u) = q ∧ ⌊eval (point (b k u.1) u.2) (P k) / 1⌋ = a} ≤
        ENNReal.ofReal (K k * (N k ^ (-(1 : ℝ))) ^ 3) := by
      intro q a
      have h := hcP true q a
      rw [hr3] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext u
      simp only [mem_setOf_eq, if_pos, hzero]
      rfl
    have hcapJ : ∀ (q : Fin 3 → ℤ) (a j : ℤ), μ k {u | baseMesh (N k ^ (-(1 : ℝ)))
        (nbase (b k) u) = q ∧ ⌊eval (point (b k u.1) u.2) (P k) / 1⌋ = a ∧
        ⌊b k u.1 3 / N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (K k * (N k ^ (-(1 : ℝ))) ^ 3) * π k {w | ⌊w / N k ^ (-v)⌋ = j} := by
      intro q a j
      have h := hcJ true q a j
      rw [hr3] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext u
      simp only [mem_setOf_eq, if_pos, hzero]
      rfl
    have hπ : ∀ j : ℤ, π k {w | ⌊w / N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (K k * N k ^ (-S * v)) := fun j => hcπ j
    -- the light-cell smallness
    have hsmallL : 400 * K k ^ 3 * ((2 * K k + 5) * K k * (K k * N k ^ (-S * v))) ≤ 1 := by
      have h7 : 2 * K k + 5 ≤ 7 * K k := by linarith
      have hNSv : 0 ≤ N k ^ (-S * v) := (Real.rpow_pos_of_pos hNk _).le
      have : 400 * K k ^ 3 * ((2 * K k + 5) * K k * (K k * N k ^ (-S * v))) ≤
          2800 * K k ^ 6 * N k ^ (-(S * v)) := by
        rw [show -S * v = -(S * v) by ring]
        have e : 2800 * K k ^ 6 * N k ^ (-(S * v)) =
            400 * K k ^ 3 * (7 * K k * K k * (K k * N k ^ (-(S * v)))) := by ring
        rw [e]
        gcongr
      linarith
    -- the budget
    have hΛ := nativeΛ_pow_le hKk (hN1 k) hv
    have hμc : 1 ≤ 1 * labelμ (K k) (N k ^ (-v)) := by
      rw [one_mul, labelμ, le_div_iff₀ hNv0]
      have : 1 ≤ K k ^ 3 := one_le_pow₀ hKk
      nlinarith
    have hbudget : C * labelΛ (K k) (N k ^ (-v)) (nativeLam (K k)) ^ 80 *
        (N k ^ (-e₀) / (1 * labelμ (K k) (N k ^ (-v))) + 7 * K k * (3 * N k ^ (-(1 : ℝ))) / 1 ^ 2)
        ≤ 1 := by
      have hterm1 : N k ^ (-e₀) / (1 * labelμ (K k) (N k ^ (-v))) ≤ N k ^ (-e₀) :=
        div_le_self hNe0 hμc
      have hterm2 : 7 * K k * (3 * N k ^ (-(1 : ℝ))) / 1 ^ 2 = 21 * K k * N k ^ (-(1 : ℝ)) := by
        ring
      have hΛ0 : 0 ≤ labelΛ (K k) (N k ^ (-v)) (nativeLam (K k)) := by
        rw [labelΛ]; have := nativeLam_pos hKk; positivity
      calc C * labelΛ (K k) (N k ^ (-v)) (nativeLam (K k)) ^ 80 *
            (N k ^ (-e₀) / (1 * labelμ (K k) (N k ^ (-v))) + 7 * K k * (3 * N k ^ (-(1 : ℝ))) / 1 ^ 2)
          ≤ C * (c₁ * K k ^ 720 * N k ^ (240 * v)) *
              (N k ^ (-e₀) + 21 * K k * N k ^ (-(1 : ℝ))) := by
            rw [hterm2]
            gcongr
        _ = (C * c₁ * K k ^ 720 * N k ^ (240 * v - e₀)) +
            21 * C * c₁ * K k ^ 721 * N k ^ (240 * v - 1) := by
            rw [sub_eq_add_neg, sub_eq_add_neg, Real.rpow_add hNk, Real.rpow_add hNk]
            ring
        _ ≤ 1 / 2 + 1 / 2 := by
            gcongr
            · nlinarith
            · nlinarith
        _ = 1 := by norm_num
    obtain ⟨L, hL⟩ := hpal (μ k) (π k) (b k) (P k) (K k) (N k ^ (-e₀)) (N k ^ (-(1 : ℝ)))
      (N k ^ (-v)) (K k * N k ^ (-S * v)) hKk hNe0 hNe1 hNr0 hNr2 hNv0 hNv1 hπb0 hPdeg hgood
      hmass hcapP hcapJ hπ hsmallL hbudget
    refine ⟨L, ?_⟩
    have herr : C * labelΛ (K k) (N k ^ (-v)) (nativeLam (K k)) ^ 80 * 1 ≤ N k ^ ε := by
      rw [mul_one]
      calc C * labelΛ (K k) (N k ^ (-v)) (nativeLam (K k)) ^ 80
          ≤ C * (c₁ * K k ^ 720 * N k ^ (240 * v)) := by gcongr
        _ = C * c₁ * K k ^ 720 * N k ^ (240 * v) := by ring
        _ ≤ N k ^ ε := hs4.le
    filter_upwards [hL] with p hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, fun t ht => (hi t ht).trans herr⟩
  obtain ⟨H, hH1, hHsub, hHev⟩ := exists_subpower_envelope N hN1 Pk hev
  refine ⟨fun k => 3 * H k, fun k => by linarith [hH1 k], ?_, ?_⟩
  · intro ε hε
    filter_upwards [hHsub (ε / 2) (by positivity),
      Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (show ε / 2 < ε by linarith) 3] with k hk1 hk2
    calc 3 * H k ≤ 3 * N k ^ (ε / 2) := by linarith
      _ ≤ N k ^ ε := hk2.le
  · filter_upwards [hHev] with k hk
    obtain ⟨L, hL⟩ := hk
    refine ⟨3, L, by push_cast; linarith [hH1 k], ?_⟩
    filter_upwards [hL] with p hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, fun t ht => (hi t ht).trans (by linarith [hH1 k])⟩

end

end Submission.Obl.k4_contact_equal_rate_affine_palettes
