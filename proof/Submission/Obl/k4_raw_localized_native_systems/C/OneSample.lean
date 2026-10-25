import Submission.Obl.k4_raw_localized_native_systems.C.PositiveWeightPruning

/-
Adapted from this LOT tree, o178, session x0596, `OneSample.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# One localized sample from a narrow later chart system

All strip parameters are explicit functions of the scale `N`, the slack `κ`, the
time exponent `T` and the narrowness `w₂` of the later system:

* the long-axis cutoff `lam = δ_u / (4 κ 2^T)` (shorter charts are charged by
  angular charging, `shortPath_mass_le`);
* the strip width `ρ = 12 κ² N^(-w₂) / δ_u`, the clip `Kc = κ + ρ`, the binning
  constant `KB`, the binning width `g = ρ / KB` and the scale `H = CB KB² + 8 KB / δ_u`
  of paired full-time binning;
* the common width of the full-time charts `gC = 2ρ + 2 g H² κ + 2 g H²`.

Given a certificate step for every family of full-time charts with the delivered
properties (`CFam`), and explicit numeric conditions on these parameters, the sample
is a `NativeSampleCert`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The strip width. -/
def sRho (N κ w₂ δu : ℝ) : ℝ := 12 * κ ^ 2 * N ^ (-w₂) / δu
/-- The binning constant. -/
def sKB (κ ρ : ℝ) : ℝ := 2 * (κ + ρ) + (⌈κ⌉₊ : ℝ) + κ + 2
/-- The scale of paired full-time binning. -/
def sH (CB : ℕ) (KB δu : ℝ) : ℝ := (CB : ℝ) * KB ^ 2 + 8 * KB / δu
/-- The common width of the full-time charts. -/
def sgC (ρ G κ : ℝ) : ℝ := 2 * ρ + 2 * G * κ + 2 * G

/-- The properties of a family of full-time charts delivered to the certificate step;
`a` is the later chart system whose selected incidences contain the charts'. -/
def CFam (p : Data) (k : ℕ) (a : Atlas p k) (M D : ℕ) (loss g : ℝ) {C : ℕ}
    (γC : Fin C → Fin (p.W k)) (n : Fin C → Plane) (int sp : Fin C → ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Point)
    (lst : Fin (p.W k) → Observation → Finset (Fin C)) : Prop :=
  (∀ c, chart (p.N k) M D (p.N k ^ loss) 0 0 0 (p.B k (γC c)) (p.E k (γC c))
      (int c • n c) (sp c • n c) (stripFrame g (n c)) (p.P k (γC c)) (A c) (F c)
      (∀ z ∈ F c, c ∈ lst (γC c) (obs (p.B k (γC c)) (δ (p.N k) 1) z))) ∧
  (∀ c, ‖n c‖ = 1) ∧
  (∀ c c', c ≠ c' → γC c = γC c' → Disjoint (A c) (A c')) ∧
  (∀ γ o, ((lst γ o).card : ℝ) ≤ p.N k ^ loss) ∧
  (∀ γ c, MeasurableSet {o | c ∈ lst γ o}) ∧
  ∀ c, F c ⊆ ⋃ b ∈ Finset.univ.filter (fun b => a.γ b = γC c), a.F b

/-- The certificate step: good sets of small omission and a certificate for every
pruned re-indexing with positive original weights and priors. -/
def DStep (cert : CertPred) (p : Data) (k : ℕ) (a : Atlas p k) (M D : ℕ)
    (loss g a₀ χ d s m : ℝ) : Prop :=
  ∀ (C : ℕ) (γC : Fin C → Fin (p.W k)) (n : Fin C → Plane) (int sp : Fin C → ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Point)
    (lst : Fin (p.W k) → Observation → Finset (Fin C)),
    CFam p k a M D loss g γC n int sp A F lst →
    ∃ G : Fin C → Set Point, (∀ c, MeasurableSet (G c)) ∧ (∀ c, G c ⊆ F c) ∧
      ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c \ G c) ≤
        ENNReal.ofReal (p.N k ^ (-a₀)) ∧
      ∀ (C' : ℕ) (ι : Fin C' → Fin C), Function.Injective ι →
        (∀ c, 0 < p.ν k (γC (ι c)) (A (ι c))) →
        (∀ c, 0 < p.ω k (γC (ι c))) →
        cert (p.N k) χ d s m C' (cR (p.ω k) (p.ν k) (γC ∘ ι) (A ∘ ι))
          (cLaws (p.ν k) (γC ∘ ι) (A ∘ ι) (G ∘ ι)) (cCoeff (p.P k) (γC ∘ ι) (n ∘ ι) (A ∘ ι))

/-- For long charts the minor width is at most the determinant over the cutoff. -/
theorem minorWidth_le_of_long {Q : Matrix (Fin 2) (Fin 2) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (h : lam ≤ ‖longCol Q‖) : minorWidth Q ≤ |Q.det| / lam :=
  div_le_div_of_nonneg_left (abs_nonneg _) hlam h


theorem rhoG_aux {ρ g H KB κ CB : ℝ} (hg : 0 < g) (hρg : ρ = KB * g) (hKB : 2 ≤ KB)
    (hκKB : κ ≤ KB) (hCB : 2 ≤ CB) (hH : CB * KB ^ 2 ≤ H) :
    2 * ρ + g * H * κ ≤ 2 * (g * H ^ 2) := by
  have hKB0 : 0 ≤ KB := by linarith
  have h1 : 2 * KB ^ 2 ≤ H :=
    le_trans (mul_le_mul_of_nonneg_right hCB (sq_nonneg KB)) hH
  have h2 : 2 * KB ≤ 2 * KB ^ 2 := by
    have : KB ≤ KB ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_right hKB0 (by linarith)
    linarith
  have hH2 : 2 * KB ≤ H := h2.trans h1
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 ≤ H := by linarith
  have h3 : H * κ ≤ H * H := mul_le_mul_of_nonneg_left (hκKB.trans (by linarith)) hH0
  have h4 : 2 * KB ≤ H * H := hH2.trans (le_mul_of_one_le_right hH0 hH1)
  have h5 : 2 * KB + H * κ ≤ 2 * H ^ 2 := by rw [sq]; linarith
  have h6 := mul_le_mul_of_nonneg_left h5 hg.le
  rw [hρg]
  calc 2 * (KB * g) + g * H * κ = g * (2 * KB + H * κ) := by ring
    _ ≤ g * (2 * H ^ 2) := h6
    _ = 2 * (g * H ^ 2) := by ring

open Classical in
/-- **One localized sample.** -/
theorem localized_sample {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (cert : CertPred) (hp : Valid p) (hL : p.L = 1) (a : Atlas p k)
      {M₂ D₂ : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M₂ D₂ κ r ex)
      (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
      (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
      (hcard : ∀ γ o, ((a.lst γ o).card : ℝ) ≤ κ)
      (hmeas : ∀ γ b, MeasurableSet {o | b ∈ a.lst γ o})
      (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
        priorMass p k (a.γ b) (a.F b))
      (hcov : ENNReal.ofReal κ⁻¹ ≤
        ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b))
      (hκ1 : 1 ≤ κ) (hKκ : p.K k ≤ κ)
      {u τ w₂ E₀ loss χ a₀ w d s m S U : ℝ} {M D : ℕ}
      (hnarrow : ∀ b, |(a.Q b).det| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w₂))
      (hu : 0 < u) (huη : u ≤ p.η * p.L)
      (hexc : ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
          selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ)) ≤
        ENNReal.ofReal E₀)
      (hE₀ : 0 ≤ E₀)
      (hgH : sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
        sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2 ≤ 1)
      (hEκ : E₀ + p.N k ^ (-p.S * u + 2 * τ) * (9 * ⌈κ⌉₊ : ℕ) ≤ κ⁻¹)
      (hκC : κ + 1 ≤ p.N k ^ loss)
      (hκC2 : 2 * (1 + sgC (sRho (p.N k) κ w₂ (δ (p.N k) u))
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2) κ) ≤
        p.N k ^ loss)
      (hPc : ∀ γ e, |(p.P k γ).coeff e| ≤ p.N k ^ M)
      (hM₁ : 2 * (κ + sRho (p.N k) κ w₂ (δ (p.N k) u)) ≤ p.N k ^ M)
      (hM₂ : 2 * (2 + sgC (sRho (p.N k) κ w₂ (δ (p.N k) u))
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2) κ +
          (sgC (sRho (p.N k) κ w₂ (δ (p.N k) u))
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2) κ)⁻¹) ≤
        p.N k ^ M)
      (hM₃ : 2 * (a.C : ℝ) * p.N k ^ M₂ + 88 ≤ p.N k ^ M) (hM₄ : p.N k ^ M₂ ≤ p.N k ^ M)
      (hD₂ : D₂ ≤ D) (hD4 : 4 ≤ D)
      (hCM : (p.W k : ℝ) * ((CB : ℝ) * sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) /
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2)) ^ CB ≤
        p.N k ^ M)
      (hlstN : (2 * 9 ^ 4 * ⌈κ⌉₊ : ℕ) ≤ p.N k ^ loss)
      (hgw : sgC (sRho (p.N k) κ w₂ (δ (p.N k) u))
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2) κ ≤
        p.N k ^ (-w))
      (hχ : 8 * p.N k ^ loss ≤ p.N k ^ χ)
      (hsig : p.N k ^ loss * δ (p.N k) 1 ≤ p.N k ^ (-1 + χ))
      (hloss : 0 ≤ loss)
      (hX : p.N k ^ (-loss) ≤ ((κ⁻¹ - (E₀ + p.N k ^ (-p.S * u + 2 * τ) * (9 * ⌈κ⌉₊ : ℕ))) ^ 2 / 4 -
          2 * (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * ⌈κ⌉₊ : ℕ) : ENNReal) *
            (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
              ENNReal.ofReal (256 * κ ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)))).toReal -
          p.N k ^ (-a₀)) - p.N k ^ (-χ))
      (hD : DStep cert p k a M D loss (sgC (sRho (p.N k) κ w₂ (δ (p.N k) u))
          (sRho (p.N k) κ w₂ (δ (p.N k) u) / sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u)) *
            sH CB (sKB κ (sRho (p.N k) κ w₂ (δ (p.N k) u))) (δ (p.N k) u) ^ 2) κ) a₀ χ d s m),
      NativeSampleCert cert (p.N k) (p.K k) (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)
        M D a₀ w loss 1 χ d s m S U := by
  have hcs := c_sample (p := p) (k := k) hCB2 hB
  intro cert hp hL a M₂ D₂ κ r ex hc hdisj hknown hcard hmeas hfloor hcov hκ1 hKκ u τ w₂ E₀ loss χ
    a₀ w d s m S U M D hnarrow hu huη hexc hE₀ hgH hEκ hκC hκC2 hPc hM₁ hM₂ hM₃ hM₄ hD₂ hD4 hCM
    hlstN hgw hχ hsig hloss hX hD
  classical
  -- the parameters
  set N := p.N k with hNdef
  set δu := δ N u with hδudef
  set ρ := sRho N κ w₂ δu with hρdef
  set KB := sKB κ ρ with hKBdef
  set g := ρ / KB with hgdef
  set H := sH CB KB δu with hHdef
  set G := g * H ^ 2 with hGdef
  set gC := sgC ρ G κ with hgCdef
  set κL := ⌈κ⌉₊ with hκLdef
  set lam := δu / (4 * κ * (2 : ℝ) ^ a.T) with hlamdef
  set E := E₀ + N ^ (-p.S * u + 2 * τ) * (9 * κL : ℕ) with hEdef
  have hN : 0 < N := hp.scale_pos k
  have hN1 : 1 ≤ N := hp.scale_ge_one k
  have hδpos : 0 < δu := by rw [hδudef]; unfold δ; positivity
  have hκpos : 0 < κ := by linarith
  have h2T : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hρpos : 0 < ρ := by
    rw [hρdef]; unfold sRho; positivity
  have hκLκ : κ ≤ (κL : ℝ) := Nat.le_ceil κ
  have hKBpos : 2 ≤ KB := by
    rw [hKBdef]; unfold sKB
    have : (0 : ℝ) ≤ (κL : ℝ) := Nat.cast_nonneg _
    linarith
  have hgpos : 0 < g := div_pos hρpos (by linarith)
  have hKB1 : 1 ≤ KB := by linarith
  have hHge : (CB : ℝ) * KB ^ 2 ≤ H := by
    rw [hHdef]; unfold sH
    have : 0 ≤ 8 * KB / δu := by positivity
    linarith
  have hCB2' : (2 : ℝ) ≤ CB := by exact_mod_cast hCB2
  have hKB2 : (4 : ℝ) ≤ KB ^ 2 := by
    have := mul_le_mul hKBpos hKBpos (by norm_num) (by linarith)
    rw [sq]; linarith
  have hCKB : (8 : ℝ) ≤ CB * KB ^ 2 := by
    have := mul_le_mul hCB2' hKB2 (by norm_num) (by linarith)
    linarith
  have hH8 : 8 ≤ H := by linarith
  have hCBKB : (1 : ℝ) ≤ CB * KB := by
    have := mul_le_mul hCB2' hKB1 (by norm_num) (by linarith)
    linarith
  have hHKB : KB ≤ H := by
    have h1 : KB ≤ KB * (CB * KB) := le_mul_of_one_le_right (by linarith) hCBKB
    have h2 : KB * (CB * KB) = CB * KB ^ 2 := by ring
    linarith
  have hκKB : κ ≤ KB := by
    rw [hKBdef]; unfold sKB
    have : (0 : ℝ) ≤ (κL : ℝ) := Nat.cast_nonneg _
    linarith
  -- the chart system has at least one chart
  have hC : 0 < a.C := by
    by_contra h0
    push Not at h0
    have hC0 : a.C = 0 := by omega
    have : (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      exact absurd b.2 (by omega)
    rw [this] at hcov
    have hpos : (0 : ENNReal) < ENNReal.ofReal κ⁻¹ := by
      rw [ENNReal.ofReal_pos]; positivity
    exact absurd hcov (not_le.2 hpos)
  -- the long-axis width bound
  have hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ := by
    intro b hlong
    have hlampos : 0 < lam := by rw [hlamdef]; positivity
    have h1 := minorWidth_le_of_long hlampos hlong
    have hss : stripScale a.T ≤ 3 * (2 : ℝ) ^ a.T := by
      unfold stripScale
      have : (1 : ℝ) ≤ (2 : ℝ) ^ a.T := one_le_pow₀ (by norm_num)
      linarith
    have hnar := hnarrow b
    have h4 : (4 : ℝ) ^ a.T = (2 : ℝ) ^ a.T * (2 : ℝ) ^ a.T := by
      rw [← mul_pow]; norm_num
    calc minorWidth (a.Q b) * (κ * stripScale a.T)
        ≤ |(a.Q b).det| / lam * (κ * (3 * (2 : ℝ) ^ a.T)) := by
          apply mul_le_mul h1 _ (mul_nonneg hκpos.le (stripScale_pos a.T).le)
            (div_nonneg (abs_nonneg _) hlampos.le)
          exact mul_le_mul_of_nonneg_left hss hκpos.le
      _ = 12 * κ ^ 2 * (|(a.Q b).det| * (4 : ℝ) ^ a.T) / δu := by
          rw [hlamdef, h4]; field_simp; ring
      _ ≤ 12 * κ ^ 2 * N ^ (-w₂) / δu := by gcongr
      _ = ρ := by rw [hρdef]; rfl
  -- lists of the later system
  have hcardL : ∀ γ o, (a.lst γ o).card ≤ κL := by
    intro γ o
    have h1 : ((a.lst γ o).card : ℝ) ≤ (κL : ℝ) := (hcard γ o).trans hκLκ
    exact_mod_cast h1
  -- the exceptional mass, including the short-axis charts
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hω0 : ∀ γ, 0 ≤ p.ω k γ := (hfmt k).2.1
  have hω1 : ∑ γ, p.ω k γ = 1 := (hfmt k).2.2.1
  have hsel1 : ∀ γ, selected p k γ Set.univ ≤ 1 := by
    intro γ
    have hEs : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
    haveI : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
    unfold selected priorMass
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    calc ((p.ν k γ).prod volume) (p.E k γ) ≤
          ((p.ν k γ).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hEs
      _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp
  have hshort : ∀ γ, selected p k γ (shortPath a γ u τ lam) ≤
      ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) := by
    intro γ
    have h := shortPath_mass_le hp a γ hc hknown κL (hcardL γ) (hmeas γ) (τ := τ) (lam := lam)
      hu huη (by rw [hlamdef]; field_simp; rfl)
    refine h.trans ?_
    calc ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
          selected p k γ Set.univ ≤
        ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) * 1 := by
          gcongr; exact hsel1 γ
      _ = _ := mul_one _
  have hexc' : ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
      selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
        selected p k γ (shortPath a γ u τ lam)) ≤ ENNReal.ofReal E := by
    have hsumω : ∑ γ, ENNReal.ofReal (p.ω k γ) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω0 γ), hω1, ENNReal.ofReal_one]
    calc ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
          selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
            selected p k γ (shortPath a γ u τ lam))
        = ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
            selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ)) +
          ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortPath a γ u τ lam) := by
          rw [← Finset.sum_add_distrib]; simp only [mul_add]
      _ ≤ ENNReal.ofReal E₀ + ∑ γ, ENNReal.ofReal (p.ω k γ) *
            (ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal)) := by
          gcongr with γ
          exact hshort γ
      _ = ENNReal.ofReal E₀ + ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) *
            ((9 * κL : ℕ) : ENNReal) := by
          rw [← Finset.sum_mul, hsumω, one_mul]
      _ = ENNReal.ofReal E := by
          rw [hEdef, ENNReal.ofReal_add hE₀ (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
  -- the remaining numeric conditions of the full-time charts
  have hKcB : 2 * (κ + ρ) ≤ KB := by
    rw [hKBdef]; unfold sKB
    have : (0 : ℝ) ≤ (κL : ℝ) := Nat.cast_nonneg _
    linarith
  have hκLB : ((κL : ℕ) : ℝ) ≤ KB := by
    rw [hKBdef]; unfold sKB; linarith
  have hρB : ρ ≤ KB * g := by
    rw [hgdef, mul_div_cancel₀ _ (by linarith)]
  have hpin : 8 * ρ / (g * H) ≤ δu := by
    have hH0 : 0 < H := by linarith
    have heq : 8 * ρ / (g * H) = 8 * KB / H := by
      rw [hgdef]; field_simp
    rw [heq, div_le_iff₀ hH0]
    have : 8 * KB / δu ≤ H := by
      rw [hHdef]; unfold sH
      have : 0 ≤ (CB : ℝ) * KB ^ 2 := by positivity
      linarith
    rw [div_le_iff₀ hδpos] at this
    linarith
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hρG : 2 * ρ + g * H * κ ≤ 2 * (g * H ^ 2) :=
    rhoG_aux hgpos (by rw [hgdef, mul_div_cancel₀ _ (by linarith)]) hKBpos hκKB hCB2' hHge
  have hgC0 : 0 < gC := by
    rw [hgCdef]; unfold sgC
    have : 0 ≤ G := by rw [hGdef]; positivity
    have : 0 ≤ G * κ := mul_nonneg this hκpos.le
    linarith
  -- apply the full-time charts of one sample
  obtain ⟨C, γC, rep, t₀, lst, hCcount, hcharts, hcdisj, hlcard, hlmeas, hmass⟩ :=
    hcs hp a hc hdisj hknown κL hcardL hmeas hfloor hκpos hC (u := u) (τ := τ) (κ' := κ)
      (lam := lam) (ρ := ρ) (Kc := κ + ρ) (KB := KB) (g := g) (H := H) (E := E) (gC := gC)
      (κC := N ^ loss) M D hu huη hκ1 le_rfl hKκ hρ le_rfl hKcB hκLB hκKB hρB hKBpos hgpos hgH
      hHge hρpos.le hpin hE0 hEκ hcov hexc' (by linarith) hρG le_rfl hgC0 hκC hκC2 hPc hM₁ hM₂ hM₃
      hM₄ hD₂ hD4
  -- the delivered family
  have hfam : CFam p k a M D loss gC γC (fun c => q2normal a (rep c))
      (fun c => q2intercept a (κ + ρ) (rep c)) (fun c => q2speed a (κ + ρ) (rep c))
      (fun c => cA a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (rep c))
      (fun c => cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c)) lst := by
    refine ⟨?_, fun c => norm_minorNormal (hc.det_ne (rep c)), hcdisj, ?_, hlmeas, ?_⟩
    · intro c
      have h := hcharts c
      rw [hL] at h
      exact h
    · intro γ o
      have h1 : ((lst γ o).card : ℝ) ≤ ((2 * 9 ^ 4 * κL : ℕ) : ℝ) := by
        exact_mod_cast hlcard γ o
      exact h1.trans hlstN
    · intro c z hz
      have hz' : z ∈ compatEvent a (γC c) (κ + ρ) (3 * G) (rep c) := hz.1.1
      rw [mem_compatEvent] at hz'
      obtain ⟨b'', hb'', hzF⟩ := hz'
      rw [mem_compatSet] at hb''
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
      exact ⟨b'', hb''.1, hzF⟩
  obtain ⟨Gs, hGm, hGF, homit, hcert⟩ := hD C γC _ _ _ _ _ lst hfam
  -- the good mass
  set Y := ENNReal.ofReal (N ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
    (ENNReal.ofReal (N ^ (-p.f 0 + τ)) *
      ENNReal.ofReal (256 * κ ^ 4 * stripScale a.T ^ 2 * (κ * N ^ p.f r))) with hYdef
  have hYfin : Y ≠ ⊤ := by
    rw [hYdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hFG : ∀ c, ((p.ν k (γC c)).prod volume)
      (cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c)) =
      ((p.ν k (γC c)).prod volume) (Gs c) + ((p.ν k (γC c)).prod volume)
        (cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c) \ Gs c) := by
    intro c
    rw [← measure_union Set.disjoint_sdiff_right
      (((hcharts c).2.2.2.2.2.2.2.1).diff (hGm c)), Set.union_sdiff_cancel (hGF c)]
  set SG := ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (Gs c) with hSG
  have hmassG : ENNReal.ofReal ((κ⁻¹ - E) ^ 2 / 4 - 2 * Y.toReal - N ^ (-a₀)) ≤ SG := by
    have hF : ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume)
        (cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c)) ≤
        SG + ENNReal.ofReal (N ^ (-a₀)) := by
      calc _ = SG + ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume)
              (cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c) \ Gs c) := by
            rw [hSG, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [hFG, mul_add]
        _ ≤ SG + ENNReal.ofReal (N ^ (-a₀)) := by gcongr
    have h1 := hmass.trans (add_le_add hF le_rfl)
    -- cancel the finite error terms
    by_cases hneg : (κ⁻¹ - E) ^ 2 / 4 - 2 * Y.toReal - N ^ (-a₀) ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hneg]; exact bot_le
    · push Not at hneg
      have hy0 : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
      have he0 : 0 ≤ N ^ (-a₀) := by positivity
      have hsplit : ENNReal.ofReal ((κ⁻¹ - E) ^ 2 / 4 - Y.toReal) =
          ENNReal.ofReal ((κ⁻¹ - E) ^ 2 / 4 - 2 * Y.toReal - N ^ (-a₀)) +
            ENNReal.ofReal (N ^ (-a₀) + Y.toReal) := by
        rw [← ENNReal.ofReal_add hneg.le (by positivity)]
        congr 1; ring
      have hc : SG + ENNReal.ofReal (N ^ (-a₀)) + Y = SG + ENNReal.ofReal (N ^ (-a₀) + Y.toReal) := by
        rw [ENNReal.ofReal_add he0 hy0, ENNReal.ofReal_toReal hYfin, add_assoc]
      rw [hsplit, hc] at h1
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  have hM1 : 1 ≤ N ^ M := by linarith
  refine pruned_native_sample_positive_weights cert hp γC (fun c => q2normal a (rep c))
    (fun c => q2intercept a (κ + ρ) (rep c)) (fun c => q2speed a (κ + ρ) (rep c))
    (fun c => cA a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (rep c))
    (fun c => cF a (γC c) (t₀ c) lam (κ + ρ) G gC (N ^ loss) (3 * G) (rep c)) Gs lst
    (by linarith) hloss (hCcount.trans hCM) hM1 hcdisj hfam.2.2.2.1 hlmeas hfam.1 hfam.2.1 hgC0
    hgw hGm hGF hχ hsig hmassG hX homit hcert

end

end Submission.Obl.k4_raw_localized_native_systems.C
