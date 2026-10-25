import Submission.Lib.K4ExactProblemOps.Defs
import Submission.Lib.K4ExactProblemOps.AngularCoarsening

/-!
# Coarsening an exact problem to an intermediate depth

A valid problem of length `L` whose profile has an endpoint cap `d' < 1` at a depth
`0 < b ≤ L` is a valid problem of length `b` with the same data, except that its
joint angular density is the fiber sum of the fine one over the `2 ^ m` fine hidden
bins of each coarse hidden bin (paper Lemma 2.7, and the first paragraph of the proof
of Lemma 4.1).

The frozen initial horizon bound only applies to problems satisfying `prob`, so every
use of it at an intermediate depth (vanishing-depth nodes, coarsened outer problems)
goes through `prob_coarsen`.
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory Filter

/-! ## Dyadic scales -/

/-- The dyadic exponent of the thickness `δ N r`. -/
def dexp (N r : ℝ) : ℤ := ⌊r * Real.log N / Real.log 2⌋

theorem δ_eq_zpow (N r : ℝ) : δ N r = (2 : ℝ) ^ (-dexp N r) := rfl

theorem δ_pos (N r : ℝ) : 0 < δ N r := zpow_pos (by norm_num) _

theorem dexp_mono {N : ℝ} (hN : 1 ≤ N) {b L : ℝ} (hbL : b ≤ L) : dexp N b ≤ dexp N L := by
  unfold dexp
  apply Int.floor_mono
  have h : 0 ≤ Real.log N / Real.log 2 :=
    div_nonneg (Real.log_nonneg hN) (Real.log_nonneg (by norm_num))
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hbL h

/-- The number of hidden-bin halvings from depth `b` to depth `L`. -/
def dsteps (N b L : ℝ) : ℕ := (dexp N L - dexp N b).toNat

theorem δ_coarse {N : ℝ} (hN : 1 ≤ N) {b L : ℝ} (hbL : b ≤ L) :
    δ N b = ((2 ^ dsteps N b L : ℕ) : ℝ) * δ N L := by
  have hle := dexp_mono hN hbL
  have hcast : ((dsteps N b L : ℕ) : ℤ) = dexp N L - dexp N b := by
    unfold dsteps
    exact Int.toNat_of_nonneg (by omega)
  rw [δ_eq_zpow, δ_eq_zpow, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hcast,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

theorem floor_div_δ_coarse {N : ℝ} (hN : 1 ≤ N) {b L : ℝ} (hbL : b ≤ L) (z : ℝ) :
    ⌊z / δ N b⌋ = coarseIdx (dsteps N b L) ⌊z / δ N L⌋ := by
  rw [coarseIdx, ← Int.floor_div_natCast, δ_coarse hN hbL, div_div, mul_comm]

/-- The pure observation at depth `b` is the coarsening of the one at depth `L`. -/
theorem obs_coarse {N : ℝ} (hN : 1 ≤ N) {b L : ℝ} (hbL : b ≤ L) (Bv : ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    obs Bv (δ N b) p = coarsenO (dsteps N b L) (obs Bv (δ N L) p) := by
  simp only [obs, coarsenO]
  rw [floor_div_δ_coarse hN hbL]

theorem measurable_obs (Bv a : ℝ) : Measurable (obs Bv a) := by
  unfold obs x
  refine Measurable.prodMk ?_ ?_
  · refine (WithLp.measurable_toLp 2 _).comp ?_
    refine Measurable.of_eval fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  · refine Measurable.floor ?_
    simp
    fun_prop

theorem measurable_velBins (a : ℝ) :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => fun j : Fin 2 => ⌊(v p.1) j / a⌋) := by
  refine Measurable.of_eval fun j => Measurable.floor ?_
  unfold v
  fin_cases j <;> simp <;> fun_prop

/-! ## Worlds of a valid problem are finite -/

theorem prob_world_finite {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) (k : ℕ) (γ : Fin (W k)) :
    IsFiniteMeasure (((ν k γ).prod volume).restrict (E k γ)) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨M, D, hMD⟩, -⟩ := hp
  obtain ⟨-, -, -, hγ, -⟩ := hMD k
  obtain ⟨hprob, -, -, -, -, -, -, -, hEsub, -⟩ := hγ γ
  refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (measure_mono hEsub))
  rw [Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-! ## The coarsening theorem -/

/-- A valid problem with an endpoint cap `d' < 1` at the depth `b ≤ L` is a valid
problem of length `b`; the joint angular density becomes the fiber sum of the fine
one. -/
theorem prob_coarsen {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) {b d' : ℝ} (hb : 0 < b) (hbL : b ≤ L)
    (hd' : 0 < d') (hd'1 : d' < 1)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ b → f b - f r ≤ d' * (b - r)) :
    prob N K b d' S η W ω ν E P B f g
      (fun k γ u => fiberSumJ (dsteps (N k) b L) (G k γ u)) := by
  have hfin := prob_world_finite hp
  obtain ⟨hN2, hNtend, hK, hL, hd, hd1, hS, hη, hμ, hg, hG, hf, htyp, hcapL, hang⟩ := hp
  have hN1 : ∀ k, (1 : ℝ) ≤ N k := fun k => le_trans (by norm_num) (hN2 k)
  have hNpos : ∀ k, (0 : ℝ) < N k := fun k => lt_of_lt_of_le (by norm_num) (hN2 k)
  have hjoint : ∀ k (γ : Fin (W k)) (u : ℝ),
      (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        (obs (B k γ) (δ (N k) b) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)) =
      fun p => coarsenJ (dsteps (N k) b L)
        (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋) := by
    intro k γ u
    funext p
    simp only [coarsenJ]
    rw [obs_coarse (hN1 k) hbL]
    rfl
  refine ⟨hN2, hNtend, hK, hb, hd', hd'1, hS, hη, hμ, ?_, ?_, ?_, ?_, hcap, ?_⟩
  · intro k γ r hr hrb
    exact hg k γ r hr (hrb.trans hbL)
  · intro k γ u hu hub
    have hu' : u ≤ η * L := hub.trans (mul_le_mul_of_nonneg_left hbL hη.le)
    obtain ⟨hGm, hGd⟩ := hG k γ u hu hu'
    refine ⟨measurable_fiberSumJ _ hGm, ?_⟩
    rw [hjoint k γ u]
    exact map_coarsenJ_joint _ _ _ (measurable_obs _ _) (measurable_velBins _) _ hGm hGd
  · intro r s hr hrs hsb
    exact hf r s hr hrs (hsb.trans hbL)
  · intro r τ hr hrb hτ
    exact htyp r τ hr (hrb.trans hbL) hτ
  · intro u τ hu hub hτ
    have hu' : u ≤ η * L := hub.trans (mul_le_mul_of_nonneg_left hbL hη.le)
    have hτ₁ : 0 < τ / 4 := by positivity
    obtain ⟨c₁, hc₁, hev₁⟩ := hang u (τ / 4) hu hu' hτ₁
    obtain ⟨c₂, hc₂, hev₂⟩ := htyp L (τ / 4) hL.le le_rfl hτ₁
    obtain ⟨c₃, hc₃, hev₃⟩ := htyp b (τ / 4) hb.le hbL hτ₁
    set c := min c₁ (min c₂ c₃) with hcdef
    have hc : 0 < c := lt_min hc₁ (lt_min hc₂ hc₃)
    refine ⟨c / 2, by positivity, ?_⟩
    have hpow : ∀ e : ℝ, 0 < e → ∀ A : ℝ, ∀ᶠ k in atTop, A ≤ N k ^ e := fun e he A =>
      ((tendsto_rpow_atTop he).comp hNtend).eventually_ge_atTop A
    filter_upwards [hev₁, hev₂, hev₃, hpow (τ / 4) hτ₁ 2, hpow (c / 2) (by positivity) 5]
      with k h₁ h₂ h₃ h2 h5
    set m := dsteps (N k) b L with hmdef
    have hNk : 0 < N k := hNpos k
    -- the thresholds
    set a₁ := ENNReal.ofReal (N k ^ (-f L - S * u + τ / 4)) with ha₁
    set a₂ := ENNReal.ofReal (N k ^ (-f L - τ / 4)) with ha₂
    set a₃ := ENNReal.ofReal (N k ^ (-f b + τ / 4)) with ha₃
    set θ := ENNReal.ofReal (N k ^ (-S * u + τ / 2)) with hθdef
    have hθ : a₁ ≤ θ * a₂ := by
      rw [ha₁, ha₂, hθdef, ← ENNReal.ofReal_mul (by positivity),
        ← Real.rpow_add (hNpos k)]
      exact le_of_eq (congrArg _ (congrArg _ (by ring)))
    have hthr : 2 * θ * a₃ ≤ ENNReal.ofReal (N k ^ (-f b - S * u + τ)) := by
      rw [hθdef, ha₃, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← Real.rpow_add (hNpos k)]
      have h2' : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
      rw [h2', ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc 2 * N k ^ (-S * u + τ / 2 + (-f b + τ / 4))
          ≤ N k ^ (τ / 4) * N k ^ (-S * u + τ / 2 + (-f b + τ / 4)) := by
            gcongr
        _ = N k ^ (-f b - S * u + τ) := by
            rw [← Real.rpow_add (hNpos k)]
            congr 1
            ring
    -- one world at a time
    have hworld : ∀ γ : Fin (W k),
        ((ν k γ).prod volume).restrict (E k γ)
          {p | ENNReal.ofReal (N k ^ (-f b - S * u + τ)) <
            fiberSumJ m (G k γ u)
              (obs (B k γ) (δ (N k) b) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)} ≤
        2 * (((ν k γ).prod volume).restrict (E k γ)
              {p | a₁ < G k γ u
                (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)} +
            ((ν k γ).prod volume).restrict (E k γ)
              {p | g k γ L (obs (B k γ) (δ (N k) L) p) <
                  ENNReal.ofReal (N k ^ (-f L - τ / 4)) ∨
                ENNReal.ofReal (N k ^ (-f L + τ / 4)) <
                  g k γ L (obs (B k γ) (δ (N k) L) p)}) +
          ((ν k γ).prod volume).restrict (E k γ)
            {p | g k γ b (obs (B k γ) (δ (N k) b) p) <
                ENNReal.ofReal (N k ^ (-f b - τ / 4)) ∨
              ENNReal.ofReal (N k ^ (-f b + τ / 4)) <
                g k γ b (obs (B k γ) (δ (N k) b) p)} := by
      intro γ
      have := hfin k γ
      obtain ⟨hGm, hGd⟩ := hG k γ u hu hu'
      obtain ⟨hgLm, hgLd⟩ := hg k γ L hL.le le_rfl
      obtain ⟨hgbm, hgbd⟩ := hg k γ b hb.le hbL
      have hob : (fun p => coarsenO m (obs (B k γ) (δ (N k) L) p)) =
          obs (B k γ) (δ (N k) b) := by
        funext p
        rw [obs_coarse (hN1 k) hbL]
      have hgbd' : Measure.map (fun p => coarsenO m (obs (B k γ) (δ (N k) L) p))
          (((ν k γ).prod volume).restrict (E k γ)) =
          (volume.prod Measure.count).withDensity (g k γ b) := by
        rw [hob]
        exact hgbd
      have key := coarse_angular_mass (((ν k γ).prod volume).restrict (E k γ))
        volume Measure.count (measurable_obs (B k γ) (δ (N k) L))
        (measurable_velBins (δ (N k) u)) m hGm hgLm hgbm hGd hgLd hgbd' (a₃ := a₃) hθ
      have hcj := congrFun (hjoint k γ u)
      calc ((ν k γ).prod volume).restrict (E k γ)
            {p | ENNReal.ofReal (N k ^ (-f b - S * u + τ)) <
              fiberSumJ m (G k γ u)
                (obs (B k γ) (δ (N k) b) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)}
          ≤ ((ν k γ).prod volume).restrict (E k γ)
              {p | 2 * θ * a₃ < fiberSumJ m (G k γ u) (coarsenJ m
                (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋))} := by
            refine measure_mono fun p hp => ?_
            simp only [Set.mem_ofPred_eq] at hp ⊢
            rw [← hcj p]
            exact lt_of_le_of_lt hthr hp
        _ ≤ _ := key
        _ ≤ _ := by
            refine add_le_add (mul_le_mul' le_rfl
              (add_le_add le_rfl (measure_mono fun p hp => Or.inl hp)))
              (measure_mono fun p hp => Or.inr ?_)
            have hp' : a₃ < g k γ b (coarsenO m (obs (B k γ) (δ (N k) L) p)) := hp
            rw [show coarsenO m (obs (B k γ) (δ (N k) L) p) = obs (B k γ) (δ (N k) b) p from
              congrFun hob p] at hp'
            exact hp'
    -- sum over the worlds
    have hω : ∀ γ : Fin (W k), ENNReal.ofReal (ω k γ) *
        ((ν k γ).prod volume).restrict (E k γ)
          {p | ENNReal.ofReal (N k ^ (-f b - S * u + τ)) <
            fiberSumJ m (G k γ u)
              (obs (B k γ) (δ (N k) b) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)} ≤
        2 * (ENNReal.ofReal (ω k γ) * ((ν k γ).prod volume).restrict (E k γ)
              {p | a₁ < G k γ u
                (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)}) +
          2 * (ENNReal.ofReal (ω k γ) * ((ν k γ).prod volume).restrict (E k γ)
              {p | g k γ L (obs (B k γ) (δ (N k) L) p) <
                  ENNReal.ofReal (N k ^ (-f L - τ / 4)) ∨
                ENNReal.ofReal (N k ^ (-f L + τ / 4)) <
                  g k γ L (obs (B k γ) (δ (N k) L) p)}) +
          ENNReal.ofReal (ω k γ) * ((ν k γ).prod volume).restrict (E k γ)
            {p | g k γ b (obs (B k γ) (δ (N k) b) p) <
                ENNReal.ofReal (N k ^ (-f b - τ / 4)) ∨
              ENNReal.ofReal (N k ^ (-f b + τ / 4)) <
                g k γ b (obs (B k γ) (δ (N k) b) p)} := by
      intro γ
      calc _ ≤ ENNReal.ofReal (ω k γ) * (2 * (_ + _) + _) := by
            exact mul_le_mul' le_rfl (hworld γ)
        _ = _ := by ring
    have hle : ∀ e : ℝ, c ≤ e → ENNReal.ofReal (N k ^ (-e)) ≤ ENNReal.ofReal (N k ^ (-c)) :=
      fun e he => ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg he))
    calc _ ≤ _ := Finset.sum_le_sum fun γ _ => hω γ
      _ = 2 * _ + 2 * _ + _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ ≤ 2 * ENNReal.ofReal (N k ^ (-c₁)) + 2 * ENNReal.ofReal (N k ^ (-c₂)) +
            ENNReal.ofReal (N k ^ (-c₃)) := by
          exact add_le_add (add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂)) h₃
      _ ≤ 2 * ENNReal.ofReal (N k ^ (-c)) + 2 * ENNReal.ofReal (N k ^ (-c)) +
            ENNReal.ofReal (N k ^ (-c)) := by
          exact add_le_add (add_le_add (mul_le_mul' le_rfl (hle _ (min_le_left _ _)))
            (mul_le_mul' le_rfl (hle _ ((min_le_right _ _).trans (min_le_left _ _)))))
            (hle _ ((min_le_right _ _).trans (min_le_right _ _)))
      _ = ENNReal.ofReal (5 * N k ^ (-c)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
          ring
      _ ≤ ENNReal.ofReal (N k ^ (-(c / 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc 5 * N k ^ (-c) = 5 * (N k ^ (-(c / 2)) * N k ^ (-(c / 2))) := by
                rw [← Real.rpow_add (hNpos k)]
                congr 2
                ring
            _ ≤ N k ^ (c / 2) * (N k ^ (-(c / 2)) * N k ^ (-(c / 2))) := by gcongr
            _ = N k ^ (-(c / 2)) := by
                rw [← mul_assoc, ← Real.rpow_add (hNpos k), add_neg_cancel,
                  Real.rpow_zero, one_mul]

end Submission.Lib.K4ExactProblemOps
