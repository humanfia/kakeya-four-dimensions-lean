import Submission.Obl.k4_raw_localized_native_systems.C.LocalizedSequence
import Submission.Obl.k4_raw_localized_native_systems.SourceSequence
import Submission.Obl.k4_raw_localized_native_systems.SourceWidthBounds

/-!
# Localized samples along a homogeneous nested source sequence

Adapted from this LOT tree, o178, session x0596, `LocalizedSequence.lean`
(`localized_eventually`, commit ec5e1086), whose proof is followed step by step.
Two changes: the source is a homogeneous nested sequence
(`HomogeneousSourceSequence`, adapted from o197/x0690), and the narrowness of
the later level is its ACTUAL homogeneous width `levelWidth n 1 - band` at each
sample, not one fixed lower bound.  Thus the common width `gC` of the full-time
charts follows the actual later width, which is what the comparison with the
earlier level requires.  The later width is at most `2 M` by the chart format,
so the formats `M'`, `D'` are still fixed before the loss.  The certificate step
is a hypothesis at each sample, for every admissible choice of terminal lists of
the later level and every width `g ≤ N^(-(levelWidth n 1 - band) + 3 u + 1)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- The later level of a homogeneous forest is narrow at its actual width. -/
theorem homogeneous_level_one_narrow {p : Data} {k : ℕ} {a : Forest p k}
    {width : Fin a.C → ℝ} {nw : ℕ → ℝ} {band : ℝ}
    (hexact : ∀ b, p.N k ^ (-width b) = |(a.Q b).det| * (4 : ℝ) ^ a.T (a.lev b))
    (hband : ∀ b, |width b - nw (a.lev b)| ≤ band) (hN : 1 ≤ p.N k)
    (c : Fin (levelSet a 1).card) :
    |(a.Q (levelEmb a 1 c)).det| * (4 : ℝ) ^ a.T 1 ≤ p.N k ^ (-(nw 1 - band)) := by
  set b := levelEmb a 1 c with hb
  have hlev : a.lev b = 1 := levelEmb_lev a 1 c
  have hex := hexact b
  rw [hlev] at hex
  rw [← hex]
  have hbd := hband b
  rw [hlev, abs_le] at hbd
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The actual later width is at most twice the chart format. -/
theorem homogeneous_level_one_width_le {p : Data} (hp : Valid p) {k M D : ℕ} {r : ℕ → ℝ}
    {a : Forest p k} (hcore : a.Core M D 2 r)
    {width : Fin a.C → ℝ} {nw : ℕ → ℝ} {band : ℝ}
    (hexact : ∀ b, p.N k ^ (-width b) = |(a.Q b).det| * (4 : ℝ) ^ a.T (a.lev b))
    (hband : ∀ b, |width b - nw (a.lev b)| ≤ band) :
    nw 1 - band ≤ 2 * (M : ℝ) := by
  exact homogeneous_level_width_upper hp hcore hexact hband (by norm_num)

open Classical in
/-- **Localized samples along a homogeneous nested source sequence.** -/
theorem localized_eventually_homogeneous {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (cert : CertPred) (p : Data) (hp : Valid p) (hL : p.L = 1)
      {kr w ε q band : ℝ} {s r : ℕ → ℝ} {M D : ℕ}
      (src : HomogeneousSourceSequence p kr w ε q band 2 M D s r)
      {u τ χ a₀ wt d s' m Sₛ U : ℝ}
      (hu : 0 < u) (huη : u ≤ p.η) (hτ : 0 < τ) (ha₀ : 0 < a₀) (hχ : 0 < χ) (hwt : 0 < wt)
      (hr1 : 0 < r 1) (hr1L : r 1 ≤ 1)
      (hw2 : wt + 3 * u + 1 < w * r 1 - 2 * (q + 2 * band) - band)
      (hgap : 3 * τ + 2 * (kr * s 1 + ε) + r 1 < p.S * u),
      ∃ M' D' : ℕ, ∀ loss : ℝ, 0 < loss → loss < χ → ∀ᶠ n in atTop,
        (∀ Λ : Fin (p.W (src.index n)) → Observation →
            Finset (Fin (levelSet (src.forest n) 1).card),
          (∀ γ c, MeasurableSet {o | c ∈ Λ γ o}) →
          (∀ γ o, ((Λ γ o).card : ℝ) ≤ (src.forest n).κ) →
          (∀ c, ∀ z ∈ (src.forest n).F (levelEmb (src.forest n) 1 c),
            c ∈ Λ ((src.forest n).γ (levelEmb (src.forest n) 1 c))
              (obs (p.B (src.index n) ((src.forest n).γ (levelEmb (src.forest n) 1 c)))
                (δ (p.N (src.index n)) p.L) z)) →
          ∀ g : ℝ, 0 < g → g ≤ 1 →
            g ≤ p.N (src.index n) ^ (-(src.levelWidth n 1 - band) + 3 * u + 1) →
          DStep cert p (src.index n) (levelAtlas (src.forest n) 1 Λ) M' D' loss g a₀ χ d s' m) →
        NativeSampleCert cert (p.N (src.index n)) (p.K (src.index n)) (p.W (src.index n))
          (p.ω (src.index n)) (p.ν (src.index n)) (p.E (src.index n)) (p.P (src.index n))
          (p.B (src.index n)) M' D' a₀ wt loss 1 χ d s' m Sₛ U := by
  intro cert p hp hL kr w ε q band s r M D src u τ χ a₀ wt d s' m Sₛ U hu huη hτ ha₀ hχ hwt
    hr1 hr1L hw2 hgap
  classical
  obtain ⟨Mp, Dp, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  set φ := src.index with hφdef
  set a := src.forest with hadef
  set w₂min := w * r 1 - 2 * (q + 2 * band) - band with hw₂mindef
  have hw₂minpos : 0 < w₂min := by linarith
  -- the actual later width at each sample, and its two bounds
  set w₂ : ℕ → ℝ := fun n => src.levelWidth n 1 - band with hw₂def
  have hw₂lo : ∀ n, w₂min ≤ w₂ n := by
    intro n
    have := (src.width_lower n 1 (by norm_num)).1
    simp only [hw₂def, hw₂mindef]
    push_cast at this
    linarith
  have hw₂hi : ∀ n, w₂ n ≤ 2 * (M : ℝ) := fun n =>
    homogeneous_level_one_width_le hp (src.core n) (src.width_exact n) (src.width_band n)
  set M' : ℕ := Mp + 2 * M + CB * (2 * M + 2) + 3 with hM'def
  refine ⟨M', D + 4, ?_⟩
  intro loss hloss hlossχ
  -- typicality exponents
  have huηL : u ≤ p.η * p.L := by rw [hL, mul_one]; exact huη
  obtain ⟨cA, hcA, hA⟩ := valid_angular hp hu huηL hτ
  obtain ⟨cL, hcL, hTL⟩ := valid_typical hp (r := p.L) hp.length_pos.le le_rfl hτ
  obtain ⟨c0, hc0, hT0⟩ := valid_typical hp (r := 0) le_rfl hp.length_pos.le hτ
  set c₀ := min cA (min cL c0) with hc₀def
  have hc₀ : 0 < c₀ := lt_min hcA (lt_min hcL hc0)
  set gap := p.S * u - (3 * τ + 2 * (kr * s 1 + ε) + r 1) with hgapdef
  have hgap0 : 0 < gap := by rw [hgapdef]; linarith
  have htime_nonneg : 0 ≤ kr * s 1 + ε := by
    have ht := (src.time 0 1 (by norm_num)).2.1
    have hpow : 1 ≤ p.N (src.index 0) ^ (kr * s 1 + ε) :=
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans ht
    have hN : 1 < p.N (src.index 0) := by linarith [hp.scale_ge_two (src.index 0)]
    exact (Real.rpow_le_rpow_left_iff hN).mp (by simpa only [Real.rpow_zero] using hpow)
  set e := min (min (loss / 4) (a₀ / 4)) (min (χ / 4) (min (c₀ / 4) (min (gap / 16) (1 / 16))))
    with hedef
  have he : 0 < e := by
    rw [hedef]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (lt_min
      (by linarith) (lt_min (by linarith) (by norm_num))))
  have he1 : e ≤ loss / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : e ≤ a₀ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : e ≤ χ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have he4 : e ≤ c₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he5 : e ≤ gap / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have he6 : e ≤ 1 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  -- the scales along the sequence
  set Nn : ℕ → ℝ := fun n => p.N (φ n) with hNndef
  have hNn : Tendsto Nn atTop atTop := hp.scale_tendsto.comp src.mono.tendsto_atTop
  have hNn1 : ∀ n, 1 ≤ Nn n := fun n => hp.scale_ge_one (φ n)
  have hκe : ∀ᶠ n in atTop, (a n).κ ≤ Nn n ^ e := src.subpower e he
  -- the eventual power comparisons
  set Cg : ℝ := 24 + 24 * (81 * CB + 72) ^ 2 with hCgdef
  set CG : ℝ := 6 * (81 * CB + 72) ^ 2 with hCGdef
  have hM'w : (M' : ℝ) > 2 * (M : ℝ) := by
    rw [hM'def]; push_cast
    have : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ CB * (2 * (M : ℝ) + 2) := by positivity
    linarith
  have hM'C : (M' : ℝ) > Mp + CB * (2 * e + 2 * (M : ℝ)) := by
    rw [hM'def]; push_cast
    have hCB0 : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
    have : CB * (2 * e + 2 * (M : ℝ)) ≤ CB * (2 * (M : ℝ) + 2) := by
      apply mul_le_mul_of_nonneg_left _ hCB0; linarith
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith
  have hM'1 : (M' : ℝ) > e := by
    have : (3 : ℝ) ≤ M' := by
      exact_mod_cast (show 3 ≤ M' by rw [hM'def]; omega)
    linarith
  have E1 := eventually_const_mul_rpow_le hNn 12 (a := 2 * e - w₂min + u) (b := 0) (by linarith)
  have E2 := eventually_const_mul_rpow_le hNn CG (a := 6 * e - w₂min + 3 * u) (b := 0)
    (by linarith)
  have E3 := eventually_const_mul_rpow_le hNn Cg (a := 7 * e - w₂min + 3 * u) (b := -wt)
    (by linarith)
  have E3' := eventually_const_mul_rpow_le hNn Cg (a := 7 * e) (b := 1) (by linarith)
  have E4 := eventually_const_mul_rpow_le hNn 12 (a := -c₀) (b := -e) (by linarith)
  have E5 := eventually_const_mul_rpow_le hNn 72 (a := e - p.S * u + 2 * τ) (b := -e)
    (by rw [hgapdef] at he5; nlinarith)
  have E6 := eventually_const_mul_rpow_le hNn 2 (a := e) (b := loss) (by linarith)
  have E7 := eventually_const_mul_rpow_le hNn 4 (a := 0) (b := loss) (by linarith)
  have E8 := eventually_const_mul_rpow_le hNn 4 (a := e) (b := M') (by linarith)
  have E9 := eventually_const_mul_rpow_le hNn 7 (a := 2 * (M : ℝ)) (b := M') (by linarith)
  have E10 := eventually_const_mul_rpow_le hNn 90 (a := 2 * M) (b := M') (by linarith)
  have E11 := eventually_const_mul_rpow_le hNn ((14 * CB) ^ CB)
    (a := Mp + CB * (2 * e + 2 * (M : ℝ))) (b := M') (by linarith)
  have E12 := eventually_const_mul_rpow_le hNn 26244 (a := e) (b := loss) (by linarith)
  have E13 := eventually_const_mul_rpow_le hNn 8 (a := loss) (b := χ) (by linarith)
  have E14 := eventually_const_mul_rpow_le hNn 2 (a := loss - 1) (b := -1 + χ) (by linarith)
  have E15 := eventually_const_mul_rpow_le hNn 64 (a := -loss) (b := -2 * e) (by linarith)
  have E16 := eventually_const_mul_rpow_le hNn (128 * 41472) (a := 6 * e - gap) (b := -2 * e)
    (by linarith)
  have E17 := eventually_const_mul_rpow_le hNn 64 (a := -a₀) (b := -2 * e) (by linarith)
  have E18 := eventually_const_mul_rpow_le hNn 64 (a := -χ) (b := -2 * e) (by linarith)
  have EA := src.mono.tendsto_atTop.eventually hA
  have EL := src.mono.tendsto_atTop.eventually hTL
  have E0 := src.mono.tendsto_atTop.eventually hT0
  filter_upwards [hκe, E1, E2, E3, E3', E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15,
    E16, E17, E18, EA, EL, E0] with n hκn e1 e2 e3 e3' e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    e15 e16 e17 e18 eA eL e0
  intro hD
  -- the sample
  have hcore := src.core n
  have hκ1 : 1 ≤ (a n).κ := hcore.1
  have hKκ : p.K (φ n) ≤ (a n).κ := hcore.2.1
  have hN1 : 1 ≤ Nn n := hNn1 n
  have hN0 : 0 < Nn n := lt_of_lt_of_le zero_lt_one hN1
  have hT : (2 : ℝ) ^ (a n).T 1 ≤ Nn n ^ (kr * s 1 + ε) := (src.time n 1 (by norm_num)).2.1
  obtain ⟨Λ, hΛm, hΛc, hΛk⟩ := exists_level_lists hp hcore (i := 1) (by norm_num) hr1.le
    (by rw [hL]; exact hr1L) (src.prepared n)
  -- the later width at this sample
  have hw₂n_lo : w₂min ≤ w₂ n := hw₂lo n
  have hw₂n_hi : w₂ n ≤ 2 * (M : ℝ) := hw₂hi n
  have hw₂n_pos : 0 < w₂ n := lt_of_lt_of_le hw₂minpos hw₂n_lo
  -- parameter bounds at the sample
  have hNe1 : 1 ≤ Nn n ^ e := Real.one_le_rpow hN1 he.le
  have hρle := sRho_le (w₂ := w₂ n) hN1 hu.le hκ1
  have hκ2 : (a n).κ ^ 2 ≤ Nn n ^ (2 * e) := by
    have h2 : Nn n ^ (2 * e) = (Nn n ^ e) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    rw [h2]; exact pow_le_pow_left₀ (le_trans zero_le_one hκ1) hκn 2
  have hmono : ∀ x : ℝ, Nn n ^ (x - w₂ n) ≤ Nn n ^ (x - w₂min) := fun x =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hw₂n_lo, hw₂n_hi])
  have hρ1 : sRho (Nn n) (a n).κ (w₂ n) (δ (Nn n) u) ≤ 1 := by
    have h1 : Nn n ^ (2 * e - w₂ n + u) = Nn n ^ (2 * e) * Nn n ^ (-w₂ n + u) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hpos := Real.rpow_pos_of_pos hN0 (-w₂ n + u)
    have hm := hmono (2 * e + u)
    have hm' : Nn n ^ (2 * e - w₂ n + u) ≤ Nn n ^ (2 * e - w₂min + u) := by
      have h3 : 2 * e + u - w₂ n = 2 * e - w₂ n + u := by ring
      have h4 : 2 * e + u - w₂min = 2 * e - w₂min + u := by ring
      rw [h3, h4] at hm; exact hm
    calc sRho (Nn n) (a n).κ (w₂ n) (δ (Nn n) u) ≤ 12 * (a n).κ ^ 2 * Nn n ^ (-w₂ n + u) := hρle
      _ ≤ 12 * (Nn n ^ (2 * e) * Nn n ^ (-w₂ n + u)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hκ2 hpos.le) (by norm_num : (0 : ℝ) ≤ 12)
      _ = 12 * Nn n ^ (2 * e - w₂ n + u) := by rw [h1]
      _ ≤ 12 * Nn n ^ (2 * e - w₂min + u) := by linarith only [hm']
      _ ≤ Nn n ^ (0 : ℝ) := e1
      _ = 1 := Real.rpow_zero _
  have hGle := binWidth_le hN1 hu.le he.le hκ1 hκn CB hρ1 (w₂ := w₂ n)
  have hgCle := sgC_le_pow hN1 hu.le he.le hκ1 hκn CB hρ1 (w₂ := w₂ n)
  have hratio := count_ratio_le hN1 hu.le hκ1 hκn CB hρ1 (w₂ := w₂ n)
  have hρge := sRho_ge (w₂ := w₂ n) hN1 hu.le hκ1
  set ρ := sRho (Nn n) (a n).κ (w₂ n) (δ (Nn n) u) with hρdef
  set KB := sKB (a n).κ ρ with hKBdef
  set G := ρ / KB * sH CB KB (δ (Nn n) u) ^ 2 with hGdef
  set gC := sgC ρ G (a n).κ with hgCdef
  have hG1 : G ≤ 1 := by
    refine hGle.trans ?_
    have hm := hmono (6 * e + 3 * u)
    have hm' : Nn n ^ (6 * e - w₂ n + 3 * u) ≤ Nn n ^ (6 * e - w₂min + 3 * u) := by
      have h3 : 6 * e + 3 * u - w₂ n = 6 * e - w₂ n + 3 * u := by ring
      have h4 : 6 * e + 3 * u - w₂min = 6 * e - w₂min + 3 * u := by ring
      rw [h3, h4] at hm; exact hm
    have hCG0 : 0 ≤ CG := by positivity
    calc 6 * (81 * CB + 72) ^ 2 * Nn n ^ (6 * e - w₂ n + 3 * u)
        ≤ CG * Nn n ^ (6 * e - w₂min + 3 * u) := by
          rw [hCGdef]; exact mul_le_mul_of_nonneg_left hm' hCG0
      _ ≤ Nn n ^ (0 : ℝ) := e2
      _ = 1 := Real.rpow_zero _
  have hgC_pow : gC ≤ Cg * Nn n ^ (7 * e - w₂ n + 3 * u) := hgCle
  have hCg0 : 0 ≤ Cg := by positivity
  have hgCw : gC ≤ Nn n ^ (-wt) := by
    refine hgC_pow.trans ?_
    have hm := hmono (7 * e + 3 * u)
    have hm' : Nn n ^ (7 * e - w₂ n + 3 * u) ≤ Nn n ^ (7 * e - w₂min + 3 * u) := by
      have h3 : 7 * e + 3 * u - w₂ n = 7 * e - w₂ n + 3 * u := by ring
      have h4 : 7 * e + 3 * u - w₂min = 7 * e - w₂min + 3 * u := by ring
      rw [h3, h4] at hm; exact hm
    exact (mul_le_mul_of_nonneg_left hm' hCg0).trans e3
  have hgC1 : gC ≤ 1 := hgCw.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (neg_nonpos.mpr hwt.le))
  have hρ0 : 0 < ρ := sRho_pos hN1 hκ1
  have hgCρ : 2 * ρ ≤ gC := by
    rw [hgCdef]; unfold sgC
    have hG0 : 0 ≤ G := by
      rw [hGdef]
      have := two_le_sKB (le_trans zero_le_one hκ1) hρ0.le
      have := delta_pos (Nn n) u
      positivity
    have hGK : 0 ≤ G * (a n).κ := mul_nonneg hG0 (le_trans zero_le_one hκ1)
    linarith only [hG0, hGK]
  have hgCpos : 0 < gC := by linarith only [hgCρ, hρ0]
  have hgCrel : gC ≤ Nn n ^ (-(src.levelWidth n 1 - band) + 3 * u + 1) := by
    refine hgC_pow.trans ?_
    have hsplit : Nn n ^ (7 * e - w₂ n + 3 * u) = Nn n ^ (7 * e) * Nn n ^ (-w₂ n + 3 * u) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hsplit' : Nn n ^ (-(src.levelWidth n 1 - band) + 3 * u + 1) =
        Nn n ^ (1 : ℝ) * Nn n ^ (-w₂ n + 3 * u) := by
      rw [← Real.rpow_add hN0]; simp only [hw₂def]; ring_nf
    rw [hsplit, hsplit', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right e3' (Real.rpow_nonneg hN0.le _)
  have hDn := hD Λ hΛm hΛc hΛk gC hgCpos hgC1 hgCrel
  -- the exceptional masses
  set E₀ := Nn n ^ (-cA) + Nn n ^ (-cL) + Nn n ^ (-c0) with hE₀def
  have hE₀ : 0 ≤ E₀ := by positivity
  have hE₀c : E₀ ≤ 3 * Nn n ^ (-c₀) := by
    have h1 : Nn n ^ (-cA) ≤ Nn n ^ (-c₀) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [min_le_left cA (min cL c0)])
    have h2 : Nn n ^ (-cL) ≤ Nn n ^ (-c₀) :=
      Real.rpow_le_rpow_of_exponent_le hN1
        (by linarith only [min_le_left cL c0, min_le_right cA (min cL c0)])
    have h3 : Nn n ^ (-c0) ≤ Nn n ^ (-c₀) :=
      Real.rpow_le_rpow_of_exponent_le hN1
        (by linarith only [min_le_right cL c0, min_le_right cA (min cL c0)])
    rw [hE₀def]; linarith only [h1, h2, h3]
  have hexc : ∑ γ, ENNReal.ofReal (p.ω (φ n) γ) *
      (selected p (φ n) γ (angFail p (φ n) γ u τ) + selected p (φ n) γ (typFail p (φ n) γ p.L τ) +
        selected p (φ n) γ (typFail p (φ n) γ 0 τ)) ≤ ENNReal.ofReal E₀ := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hE₀def, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (add_le_add eA eL) e0
  -- the total exceptional bound
  set E := E₀ + Nn n ^ (-p.S * u + 2 * τ) * ((9 * ⌈(a n).κ⌉₊ : ℕ) : ℝ) with hEdef
  have hceil : ((⌈(a n).κ⌉₊ : ℕ) : ℝ) ≤ 2 * Nn n ^ e := by
    have := (Nat.ceil_lt_add_one (le_trans zero_le_one hκ1)).le
    linarith only [this, hκn, hNe1]
  have hEle : E ≤ Nn n ^ (-e) / 2 := by
    have h1 : Nn n ^ (-p.S * u + 2 * τ) * ((9 * ⌈(a n).κ⌉₊ : ℕ) : ℝ) ≤
        18 * Nn n ^ (e - p.S * u + 2 * τ) := by
      have hsp : Nn n ^ (e - p.S * u + 2 * τ) = Nn n ^ e * Nn n ^ (-p.S * u + 2 * τ) := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [hsp]; push_cast
      have hm := mul_le_mul_of_nonneg_left hceil
        (Real.rpow_nonneg hN0.le (-p.S * u + 2 * τ))
      nlinarith only [hm]
    rw [hEdef]; linarith only [hE₀c, h1, e4, e5]
  have hκinv : Nn n ^ (-e) ≤ (a n).κ⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (lt_of_lt_of_le zero_lt_one hκ1) hκn
  have hEκ : E ≤ (a n).κ⁻¹ := by
    have hpw := Real.rpow_pos_of_pos hN0 (-e)
    linarith only [hEle, hκinv, hpw]
  -- the final mass condition
  have hfr : p.f (r 1) - p.f 0 ≤ r 1 := by
    have := (hp.2.2.2.2.2.2.2.2.2.2.2.1 0 (r 1) le_rfl hr1.le (by rw [hL]; exact hr1L)).2
    linarith only [this]
  have hY := badY_toReal_le (S := p.S) (u := u) (τ := τ) hN1 hκ1 hκn hT hfr
  have hYexp : 6 * e - p.S * u + 3 * τ + r 1 + 2 * (kr * s 1 + ε) = 6 * e - gap := by
    rw [hgapdef]; ring
  rw [hYexp] at hY
  have hX : Nn n ^ (-loss) ≤ (((a n).κ⁻¹ - E) ^ 2 / 4 -
      2 * (ENNReal.ofReal (Nn n ^ (-p.S * u + 2 * τ)) * ((9 * ⌈(a n).κ⌉₊ : ℕ) : ENNReal) *
        (ENNReal.ofReal (Nn n ^ (-p.f 0 + τ)) *
          ENNReal.ofReal (256 * (a n).κ ^ 4 * stripScale ((a n).T 1) ^ 2 *
            ((a n).κ * Nn n ^ p.f (r 1))))).toReal - Nn n ^ (-a₀)) - Nn n ^ (-χ) := by
    have hpe : 0 < Nn n ^ (-e) := Real.rpow_pos_of_pos hN0 _
    have h2e : Nn n ^ (-2 * e) = Nn n ^ (-e) * Nn n ^ (-e) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hsq : Nn n ^ (-2 * e) / 16 ≤ ((a n).κ⁻¹ - E) ^ 2 / 4 := by
      have h1 : Nn n ^ (-e) / 2 ≤ (a n).κ⁻¹ - E := by linarith only [hEle, hκinv]
      have h2 : (Nn n ^ (-e) / 2) ^ 2 ≤ ((a n).κ⁻¹ - E) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      rw [h2e]; nlinarith only [h2]
    linarith only [hsq, hY, e15, e16, e17, e18]
  -- apply the localized sample
  have hNM : ∀ (x : ℕ), Nn n ^ (x : ℝ) = Nn n ^ x := fun x => Real.rpow_natCast _ _
  refine localized_sample hCB2 hB cert hp hL (levelAtlas (a n) 1 Λ) (M₂ := M) (D₂ := D)
    (κ := (a n).κ) (r := r 1) (levelAtlas_charts hcore (by norm_num) Λ)
    (levelAtlas_disjoint hcore (by norm_num) Λ) hΛk hΛc hΛm
    (levelAtlas_floor hcore (by norm_num) Λ) (levelAtlas_coverage hcore (by norm_num) Λ)
    hκ1 hKκ (u := u) (τ := τ) (w₂ := w₂ n) (E₀ := E₀) (loss := loss) (χ := χ) (a₀ := a₀)
    (w := wt) (d := d) (s := s') (m := m) (S := Sₛ) (U := U) (M := M') (D := D + 4)
    (fun c => homogeneous_level_one_narrow (src.width_exact n) (src.width_band n) hN1 c)
    hu huηL hexc hE₀ hG1 hEκ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) ?_ ?_ hgCw ?_ ?_
    hloss.le hX hDn
  · -- κ + 1 ≤ N^loss
    linarith only [hκn, hNe1, e6]
  · -- 2 (1 + gC) ≤ N^loss
    have : (4 : ℝ) ≤ Nn n ^ loss := by simpa using e7
    linarith only [this, hgC1]
  · -- coefficients
    intro γ e'
    have h := ((hfmt (φ n)).2.2.2.1 γ).2.2.2.2.2.1 e'
    exact h.trans (pow_le_pow_right₀ hN1 (by omega))
  · -- 2 (κ + ρ) ≤ N^M'
    rw [← hNM]
    linarith only [hρ1, hκn, hNe1, e8]
  · -- 2 (2 + gC + gC⁻¹) ≤ N^M'
    rw [← hNM]
    have hinv : gC⁻¹ ≤ Nn n ^ (w₂ n) / 12 := by
      have h12 : 12 * Nn n ^ (-w₂ n) ≤ gC := by linarith only [hρge, hgCρ]
      have hpw : 0 < Nn n ^ (-w₂ n) := Real.rpow_pos_of_pos hN0 _
      rw [inv_le_iff_one_le_mul₀ hgCpos]
      have hmul : Nn n ^ (w₂ n) * Nn n ^ (-w₂ n) = 1 := by
        rw [← Real.rpow_add hN0]; simp
      have hm := mul_le_mul_of_nonneg_left h12
        (show 0 ≤ Nn n ^ (w₂ n) / 12 from by positivity)
      nlinarith only [hm, hmul]
    have hNw : Nn n ^ (w₂ n) ≤ Nn n ^ (2 * (M : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hw₂n_hi
    have hNw1 : 1 ≤ Nn n ^ (w₂ n) := Real.one_le_rpow hN1 hw₂n_pos.le
    linarith only [hinv, hgC1, hNw, hNw1, e9]
  · -- 2 C N^M + 88 ≤ N^M'
    conv_rhs => rw [← hNM]
    have hC : ((levelSet (a n) 1).card : ℝ) ≤ Nn n ^ M := by
      have h1 : (levelSet (a n) 1).card ≤ (a n).C := by
        have := Finset.card_le_univ (levelSet (a n) 1)
        simpa using this
      exact (Nat.cast_le.2 h1).trans hcore.2.2.1
    have hNM1 : 1 ≤ Nn n ^ M := one_le_pow₀ hN1
    have h2M : Nn n ^ (2 * (M : ℝ)) = (Nn n ^ M) ^ 2 := by
      rw [show (2 * (M : ℝ)) = ((2 * M : ℕ) : ℝ) by push_cast; ring, hNM, pow_mul']
    have e10' : 90 * (Nn n ^ M) ^ 2 ≤ Nn n ^ (M' : ℝ) := by rw [← h2M]; exact e10
    change 2 * ((levelSet (a n) 1).card : ℝ) * Nn n ^ M + 88 ≤ _
    have hCX := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ Nn n ^ M from by positivity)
    nlinarith only [hCX, hNM1, e10']
  · -- N^M ≤ N^M'
    exact pow_le_pow_right₀ hN1 (by omega)
  · -- the count of the full-time charts
    rw [← hNM]
    have hW : (p.W (φ n) : ℝ) ≤ Nn n ^ Mp := ((hfmt (φ n)).1)
    have hCB0 : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
    have hratio' : KB / G ≤ 14 * Nn n ^ (2 * e + 2 * (M : ℝ)) :=
      hratio.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hw₂n_lo, hw₂n_hi])) (by norm_num))
    have hx : (CB : ℝ) * KB / G ≤ 14 * CB * Nn n ^ (2 * e + 2 * (M : ℝ)) := by
      have : (CB : ℝ) * KB / G = CB * (KB / G) := by ring
      rw [this]
      calc (CB : ℝ) * (KB / G) ≤ CB * (14 * Nn n ^ (2 * e + 2 * (M : ℝ))) :=
            mul_le_mul_of_nonneg_left hratio' hCB0
        _ = 14 * CB * Nn n ^ (2 * e + 2 * (M : ℝ)) := by ring
    have hx0 : 0 ≤ (CB : ℝ) * KB / G := by
      have hKB0 : 0 ≤ KB := by
        have := two_le_sKB (le_trans zero_le_one hκ1) hρ0.le; linarith only [this]
      have hG0 : 0 ≤ G := by
        rw [hGdef]; have := delta_pos (Nn n) u; positivity
      positivity
    have hpowx : ((CB : ℝ) * KB / G) ^ CB ≤
        (14 * CB) ^ CB * Nn n ^ (CB * (2 * e + 2 * (M : ℝ))) := by
      calc ((CB : ℝ) * KB / G) ^ CB ≤ (14 * CB * Nn n ^ (2 * e + 2 * (M : ℝ))) ^ CB :=
            pow_le_pow_left₀ hx0 hx CB
        _ = (14 * CB) ^ CB * (Nn n ^ (2 * e + 2 * (M : ℝ))) ^ CB := by rw [mul_pow]
        _ = (14 * CB) ^ CB * Nn n ^ (CB * (2 * e + 2 * (M : ℝ))) := by
            rw [← Real.rpow_natCast (Nn n ^ (2 * e + 2 * (M : ℝ))) CB, ← Real.rpow_mul hN0.le]
            ring_nf
    have hsplit : Nn n ^ (Mp + CB * (2 * e + 2 * (M : ℝ))) =
        Nn n ^ (Mp : ℝ) * Nn n ^ (CB * (2 * e + 2 * (M : ℝ))) :=
      Real.rpow_add hN0 _ _
    have hWr : (p.W (φ n) : ℝ) ≤ Nn n ^ (Mp : ℝ) := by rw [hNM]; exact hW
    have hpos1 : 0 ≤ ((CB : ℝ) * KB / G) ^ CB := pow_nonneg hx0 _
    calc (p.W (φ n) : ℝ) * ((CB : ℝ) * KB / G) ^ CB
        ≤ Nn n ^ (Mp : ℝ) * ((14 * CB) ^ CB * Nn n ^ (CB * (2 * e + 2 * (M : ℝ)))) :=
          mul_le_mul hWr hpowx hpos1 (Real.rpow_nonneg hN0.le _)
      _ = (14 * CB) ^ CB * Nn n ^ (Mp + CB * (2 * e + 2 * (M : ℝ))) := by rw [hsplit]; ring
      _ ≤ Nn n ^ (M' : ℝ) := e11
  · -- list length
    have h1 : ((2 * 9 ^ 4 * ⌈(a n).κ⌉₊ : ℕ) : ℝ) ≤ 26244 * Nn n ^ e := by
      push_cast; nlinarith only [hceil]
    exact h1.trans e12
  · -- 8 N^loss ≤ N^χ
    exact e13
  · -- the observation scale
    have hδ := delta_le_two_rpow_neg (u := 1) hN1
    have hsplit : Nn n ^ (loss - 1) = Nn n ^ loss * Nn n ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hl0 : 0 ≤ Nn n ^ loss := Real.rpow_nonneg hN0.le _
    calc Nn n ^ loss * δ (Nn n) 1 ≤ Nn n ^ loss * (2 * Nn n ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hδ hl0
      _ = 2 * Nn n ^ (loss - 1) := by rw [hsplit]; ring
      _ ≤ Nn n ^ (-1 + χ) := e14

end

end Submission.Obl.k4_raw_localized_native_systems.C
