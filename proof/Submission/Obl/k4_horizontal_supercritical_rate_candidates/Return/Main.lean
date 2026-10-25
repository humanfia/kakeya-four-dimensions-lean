import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Model
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CoreStatement

/-!
# The supercritical return from one projected layer

The asymptotic wrapper: from the single-sample `CoreStatement`, the exact projected-layer
datum of o203's split (layer `h = 1`, depth `s + u`) gives the frozen candidate conclusion
in the strict supercritical regime `1 < 2 κ`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates

open Return MeasureTheory

theorem supercritical_return_of_core (hcore : CoreStatement) :
    Scalar → ProjectedPrinciple false true (fun κ => 1 < 2 * κ) := by
  intro hScalar N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hhor
    α inst ν μ ρ π b P T n j A B c F hdata hcaps hlabels hnest
  simp only [Bool.false_eq_true, ↓reduceIte]
  intro hproj
  have hℓκ : ℓ = κ := hhor rfl
  subst hℓκ
  -- chosen horizontal fits
  let Lch : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 4 → ℝ := fun k s i =>
    Classical.epsilon (fun L : Fin 4 → ℝ => F k s i = MvPolynomial.X (3 : Fin 4) -
        (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
          MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
          MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧
        |L 3| ≤ K k * (1 + N k ^ (-s) / ((2 : ℝ) ^ (-(T k s : ℤ))) ^ 2) ∧
        ∀ l ∈ B k s i, ∀ t ∈ Set.Icc (((j k s i : ℕ) : ℝ) / (2 : ℝ) ^ T k s)
          ((((j k s i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k s),
          |L 1 - (b k l 0 + t * b k l 3) * L 3| + |L 2 + t * L 3| ≤
            K k * (1 + N k ^ (-s) / (2 : ℝ) ^ (-(T k s : ℤ))))
  let fam : (k : ℕ) → (s : ℝ) → Fam α := fun k s =>
    ⟨T k s, n k s, j k s, A k s, B k s, c k s, Lch k s⟩
  have hext : ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U →
      ∀ v : ℝ, R⁻¹ ≤ v → v ≤ R →
        (fam k s).Good (ν k) (μ k) (π k) (b k) (N k) (K k) d ℓ s (N k ^ (-v)) := by
    intro R hR
    filter_upwards [hlabels R hR] with k hk s hs1 hs2 v hv1 hv2
    obtain ⟨hT1, hT2, hmeas, hdisj, hlab, hcov, hvd⟩ := hk s hs1 hs2
    have hL : ∀ i, F k s i = MvPolynomial.X (3 : Fin 4) -
        (MvPolynomial.C (Lch k s i 0) + MvPolynomial.C (Lch k s i 1) * MvPolynomial.X (0 : Fin 4) +
          MvPolynomial.C (Lch k s i 2) * MvPolynomial.X (1 : Fin 4) +
          MvPolynomial.C (Lch k s i 3) * MvPolynomial.X (2 : Fin 4)) ∧
        |Lch k s i 3| ≤ K k * (1 + N k ^ (-s) / ((2 : ℝ) ^ (-(T k s : ℤ))) ^ 2) ∧
        ∀ l ∈ B k s i, ∀ t ∈ Set.Icc (((j k s i : ℕ) : ℝ) / (2 : ℝ) ^ T k s)
          ((((j k s i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k s),
          |Lch k s i 1 - (b k l 0 + t * b k l 3) * Lch k s i 3| + |Lch k s i 2 + t * Lch k s i 3| ≤
            K k * (1 + N k ^ (-s) / (2 : ℝ) ^ (-(T k s : ℤ))) := by
      intro i
      obtain ⟨_, _, _, _, _, _, _, _, hh⟩ := hlab i
      obtain ⟨_, _, _, hLi⟩ := hh rfl
      exact Classical.epsilon_spec hLi
    have hq : ((2:ℝ) ^ (-(T k s : ℤ))) = ((2:ℝ) ^ T k s)⁻¹ := by rw [zpow_neg, zpow_natCast]
    refine ⟨hT1, hT2, fun i => (hmeas i).1, fun i => (hmeas i).2.1, fun i => (hmeas i).2.2,
      hdisj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; have := (hlab i).1; simpa [Fam.q, fam, hq] using this
    · intro i; have := (hlab i).2.1; simpa [Fam.q, fam, hq] using this
    · intro i; have := (hlab i).2.2.1; simpa [Fam.q, Fam.I, fam, blk, hq] using this
    · intro i; exact (hlab i).2.2.2.1
    · intro i l hl t ht
      have := (hlab i).2.2.2.2.2.1 l hl t ht
      simpa [Fam.q, Fam.I, fam, blk, hq, x1, x2] using this
    · intro i l hl t ht
      have := ((hlab i).2.2.2.2.2.2.1 l hl t ht).1
      rw [(hL i).1] at this
      simpa [Fam.fitVal, fam, x1, x2, x3] using this
    · intro i; have := (hL i).2.1; simpa [Fam.q, fam, hq] using this
    · intro i l hl t ht
      have := (hL i).2.2 l hl t ht
      simpa [Fam.q, Fam.I, fam, blk, hq, x1] using this
    · exact hcov
    · intro i v₀; have := hvd i v v₀ hv1 hv2; simpa [Fam.q, Fam.I, fam, blk, hq] using this
    · intro i
      obtain ⟨_, _, _, _, _, _, _, _, hh⟩ := hlab i
      obtain ⟨_, _, hcen, _⟩ := hh rfl
      simpa [Fam.q, fam, hq] using hcen
  have hcapx : ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop,
      Caps (μ k) (π k) (b k) (N k) (K k) d S R⁻¹ R R R⁻¹ R := by
    intro R hR
    have hR0 : (0:ℝ) < R := by linarith
    have hRi : R⁻¹ ≤ R := by
      rw [inv_le_iff_one_le_mul₀ hR0]; nlinarith
    filter_upwards [hcaps R hR] with k hk
    refine ⟨?_, ?_, ?_⟩
    · intro v hv1 hv2 a
      exact (hk R⁻¹ 0 v le_rfl hRi le_rfl hR0.le hv1 hv2).1 a
    · intro r σ hr1 hr2 hσ1 hσ2 q a
      exact (hk r σ R⁻¹ hr1 hr2 hσ1 hσ2 le_rfl hRi).2.1 false q a
    · intro r σ v hr1 hr2 hσ1 hσ2 hv1 hv2 q a v₀
      exact (hk r σ v hr1 hr2 hσ1 hσ2 hv1 hv2).2.2 false q a v₀
  obtain ⟨s₀, s, u, v, RL, hs₀, hbU, hbe, hs₀s, hu, hv, hvu, hvd, hsuU, hsu, hw1, hw2, hRL,
    hlay⟩ := hproj 1000 (by norm_num)
  have hlayx : ∀ M : ℝ, 100 * s₀ < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop,
      ∃ (ρs : Measure (α × ℝ)) (Ly : Layer α), ρs ≤ ρ k ∧
        ENNReal.ofReal (N k ^ (-ε)) ≤ ρs Set.univ ∧ (∀ᵐ p ∂ρs, ∃ i, p.1 ∈ Ly.C i) ∧
        Ly.Good (ρ k) (π k) (b k) (N k) (N k ^ (-M)) (N k ^ (-2 * ℓ * s₀)) (N k ^ (-(s + u)))
          d ε RL := by
    intro M hM ε hε
    filter_upwards [hlay M hM ε hε] with k hk
    obtain ⟨ρs, np, Cp, qp, Gp, hρs, hmass, hcov, hmeas, hdisj, hprop, hbud⟩ := hk
    refine ⟨ρs, ⟨np 1, Cp 1, qp 1, Gp 1⟩, hρs, hmass, ?_, ?_⟩
    · filter_upwards [hcov] with p hp
      exact hp 1
    refine ⟨hmeas 1, hdisj 1, fun i => (hprop 1 i).1, fun i => (hprop 1 i).2.1,
      fun i => (hprop 1 i).2.2.1, fun i => (hprop 1 i).2.2.2.1,
      fun i => (hprop 1 i).2.2.2.2.1, fun i => (hprop 1 i).2.2.2.2.2.1,
      fun i => (hprop 1 i).2.2.2.2.2.2, hbud 1⟩
  -- candidate parameters
  have hℓ2 : (0:ℝ) < 2 * ℓ - 1 := by linarith
  set s₁ := s + u with hs₁def
  have hs₁₀ : s₀ < s₁ := by linarith
  have hs₁lt : s₁ < 3 * s₀ / 2 := hsu
  set vc := min u ((2 * ℓ - 1) * (s₁ - s₀) / (4 * ℓ)) / 2 with hvcdef
  have hm0 : 0 < (2 * ℓ - 1) * (s₁ - s₀) / (4 * ℓ) := by
    apply div_pos (mul_pos hℓ2 (by linarith)) (by linarith)
  have hvc_pos : 0 < vc := by
    rw [hvcdef]; exact half_pos (lt_min hu hm0)
  have hvc_le : vc ≤ (2 * ℓ - 1) * (s₁ - s₀) / (4 * ℓ) := by
    rw [hvcdef]; linarith [min_le_right u ((2 * ℓ - 1) * (s₁ - s₀) / (4 * ℓ))]
  have hvc_u : vc ≤ u / 2 := by
    rw [hvcdef]; linarith [min_le_left u ((2 * ℓ - 1) * (s₁ - s₀) / (4 * ℓ))]
  set M := 101 * s₀ with hMdef
  set Rout := max (2 * ℓ * s₁ + 10) (max (2 / vc) (2 / s₀)) with hRoutdef
  have hRout1 : 2 * ℓ * s₁ + 10 ≤ Rout := le_max_left _ _
  have hRout2 : 2 / vc ≤ Rout := (le_max_left _ _).trans (le_max_right _ _)
  have hRout3 : 2 / s₀ ≤ Rout := (le_max_right _ _).trans (le_max_right _ _)
  have h2ls : s₁ ≤ 2 * ℓ * s₁ := by
    have := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 2 * ℓ by linarith) (show 0 ≤ s₁ by linarith)
    linarith
  have hRoutpos : 1 < Rout := by linarith
  have hRout0 : 0 < Rout := by linarith
  refine ⟨Rout, hRoutpos, ?_⟩
  intro ε hε
  obtain ⟨η, hη, N₀, hN₀, Rcap, hRcap, hRcaps, hRcapM, hmain⟩ :=
    hcore hScalar d ℓ S e₀ s₀ s₁ vc M RL Rout ε hd hd1 hreg hκ1 hS hS1 hs₀ hs₁₀ hs₁lt hvc_pos hvc_le
      (by linarith) rfl hRL hRout1 hε
  apply Filter.Eventually.frequently
  have hRcap0 : 0 < Rcap := by linarith
  filter_upwards [hK.2 η hη, hNt.eventually (Filter.eventually_ge_atTop N₀), hcapx Rcap hRcap,
    hext Rcap hRcap, hlabels Rcap hRcap, hnest Rcap hRcap, hlayx M (by linarith) η hη]
    with k hKk hNk hcapk hlabk hlab0 hnestk hlayk
  obtain ⟨ρs, Ly, hρs, hρsm, hρscov, hLy⟩ := hlayk
  obtain ⟨hbm, hνp, hπp, hμd, hρμ, hμs, hρu, hPdeg, hbb, hx3⟩ := hdata k
  have hsc_lo : Rcap⁻¹ ≤ s₁ - vc := by linarith
  have hse_lo : Rcap⁻¹ ≤ 300 * s₀ := by linarith
  have hM_lo : Rcap⁻¹ ≤ M := by rw [hMdef]; linarith
  have hf0 := hlabk s₀ hRcaps (by linarith) M hM_lo hRcapM
  have hfc := hlabk (s₁ - vc) hsc_lo (by linarith) M hM_lo hRcapM
  have hfe := hlabk (300 * s₀) hse_lo (by linarith) M hM_lo hRcapM
  -- a label at depth s₀ exists, giving the horizontal native polynomial
  have hne : Nonempty (Fin (n k s₀)) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hcov := hf0.cover
    have hzero : μ k Set.univ = 0 := by
      have : ∀ᵐ p ∂μ k, False := by
        filter_upwards [hcov] with p hp
        obtain ⟨i, _⟩ := hp
        exact hemp.elim i
      rw [Filter.eventually_false_iff_eq_bot, MeasureTheory.ae_eq_bot] at this
      simp [this]
    have hρ0 : ρ k Set.univ = 0 := le_antisymm ((hρμ Set.univ).trans hzero.le) zero_le
    have hKpos : 0 < (K k)⁻¹ := inv_pos.mpr (by linarith [hK.1 k])
    rw [hρ0] at hρu
    exact absurd (ENNReal.ofReal_eq_zero.mp (le_antisymm hρu zero_le)) (not_le.mpr hKpos)
  obtain ⟨i₀⟩ := hne
  obtain ⟨_, _, _, _, hlabi, _, _⟩ := hlab0 s₀ hRcaps (by linarith)
  obtain ⟨_, _, _, _, _, _, _, _, hhz⟩ := hlabi i₀
  obtain ⟨hPX, hb40, _, _⟩ := hhz rfl
  have hx3' : ∀ᵐ p ∂μ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, |x3 (b k) p.1 t| ≤ K k := by
    filter_upwards [hx3] with p hp t ht
    have := (hp.1 t ht).1
    rw [hPX] at this
    simpa [x3] using this
  have hnest0 : Nests (fam k (s₁ - vc)) (fam k s₀) := by
    intro i
    exact hnestk s₀ (s₁ - vc) hRcaps (by linarith) (by linarith) i
  have hnest1 : Nests (fam k (300 * s₀)) (fam k (s₁ - vc)) := by
    intro i
    exact hnestk (s₁ - vc) (300 * s₀) hsc_lo (by linarith) (by linarith) i
  obtain ⟨i, Q, hQdeg, hQcoef, hmass⟩ := hmain (N k) hNk (K k) η (hK.1 k) hKk hη le_rfl α (ν k)
    (μ k) (ρ k) ρs (π k) (b k) (fam k s₀) (fam k (s₁ - vc)) (fam k (300 * s₀)) Ly hbm hνp hπp
    hμd hρμ hμs hbb hx3' hb40 hcapk hf0 hfc hfe hnest0 hnest1 hρs hρsm hρscov hLy
  refine ⟨s₁ - vc, vc, i, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨Q, hQdeg, ?_, ?_⟩⟩
  · rw [inv_le_comm₀ hRout0 (by linarith)]
    calc (s₁ - vc)⁻¹ ≤ (s₀ / 2)⁻¹ := by
          apply inv_anti₀ (by linarith); linarith
      _ = 2 / s₀ := by field_simp
      _ ≤ Rout := hRout3
  · linarith
  · rw [inv_le_comm₀ hRout0 hvc_pos]
    calc vc⁻¹ = 2 / vc / 2 := by field_simp
      _ ≤ 2 / vc := by linarith [div_pos two_pos hvc_pos]
      _ ≤ Rout := hRout2
  · linarith
  · linarith
  · intro e
    refine (hQcoef e).trans ?_
    have hN1 : 1 ≤ N k := by linarith [hN k]
    have hbase : 1 ≤ (1 + ∑ e ∈ (F k (s₁ - vc) i).support, |(F k (s₁ - vc) i).coeff e|) +
        ∑ e ∈ (P k).support, |(P k).coeff e| := by
      have h1 : 0 ≤ ∑ e ∈ (F k (s₁ - vc) i).support, |(F k (s₁ - vc) i).coeff e| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have h2 : 0 ≤ ∑ e ∈ (P k).support, |(P k).coeff e| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    have := Real.one_le_rpow hbase hRout0.le
    have hNR : 0 ≤ N k ^ Rout := Real.rpow_nonneg (by linarith) _
    exact le_mul_of_one_le_right hNR this
  · have hq : (fam k (s₁ - vc)).q = ((2 : ℝ) ^ T k (s₁ - vc))⁻¹ := rfl
    rw [hq, ← div_eq_mul_inv] at hmass
    exact hmass

/-- o203 from the projected layers (split child 1) and the single-sample core: the
supercritical return replaces the rate-independent wide-return child. -/
theorem candidates_of_projections_and_core (hcore : CoreStatement)
    (hproject : Scalar → ProjectedPrinciple true true (fun κ => 1 < 2 * κ)) :
    Scalar → Row → Matching → CandidatePrinciple true (fun κ => 1 < 2 * κ) := by
  intro hScalar _hRow _hMatching N K hN hNt hK d κ ℓ S U e₀
    hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hhor
    α inst ν μ ρ π b P T n j A B c F hdata hcaps hlabels hnest
  exact (supercritical_return_of_core hcore hScalar N K hN hNt hK d κ ℓ S U e₀
    hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hhor
    α ν μ ρ π b P T n j A B c F hdata hcaps hlabels hnest)
    (hproject hScalar N K hN hNt hK d κ ℓ S U e₀
      hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hhor
      α ν μ ρ π b P T n j A B c F hdata hcaps hlabels hnest)

end Submission.Obl.k4_horizontal_supercritical_rate_candidates
