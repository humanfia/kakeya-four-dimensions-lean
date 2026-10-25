import Submission.Obl.k4_horizontal_wide_interval_return.Core.LayerCaps

/-!
# Long-domain comparison of the layers of the datum

For one index of the datum, the pairs of pieces (layer `0`, layer `h`) whose normalized sheets
differ by `Mst` in some coefficient carry `ρ⋆`-mass at most `A · Nm^-η · Σ T`, where the
reference weights `T = χ D a_h^d π(bin)` are summable by the datum.  This is `key_compare`
(x0788's `gml2D`) applied key by key, with interval ceilings and jet counts from the frozen
joint caps and the layer floors.  The numerical side conditions are explicit hypotheses
(`CompareNumerics`).
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_horizontal_wide_interval_return.MatchCor
open Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D
open Submission.Obl.k4_horizontal_wide_interval_return.CompareSheets
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The numerical side conditions of the comparison of layer `0` (width `a`) with a layer of
width `ah`, at resolution `N`, loss `K`, datum loss `N^ε`, chart width `χ`, strip width `D`,
horizontal defect `ζ₀`, base cells `N^-r` and gain `Nm`. -/
structure CompareNumerics (N K d ε χ D ζ₀ r a ah Nm R₀ η : ℝ) : Prop where
  N_gt : 1 < N
  eps_pos : 0 < ε
  d_nonneg : 0 ≤ d
  d_lt : d < 1
  K_one : 1 ≤ K
  χ_pos : 0 < χ
  D_pos : 0 < D
  D_le : D ≤ 1
  ζ₀_nonneg : 0 ≤ ζ₀
  a_pos : 0 < a
  a_le : a ≤ 1
  ah_pos : 0 < ah
  ah_le : ah ≤ a
  drift : χ / 2 + ζ₀ ≤ D * a / 960
  close : 80 * (ζ₀ + χ) / D ≤ a
  cell_chart : (N ^ ε + χ + 1) * N ^ (-r) ≤ χ / 2
  cell_half : N ^ (-r) ≤ 1 / 2
  cell_strip : (1 + N ^ ε) * N ^ (-r) ≤ D
  cell_fit : 1120 * (N ^ (-r) + (1 + N ^ ε) * N ^ (-r) / (4 * D)) ≤ ah
  cell_jet : 1120 * (N ^ (-r) + (1 + N ^ ε) * N ^ (-r) / (4 * D)) ≤ 27 * a
  gain_one : 1 ≤ Nm
  gain_R₀ : R₀ ≤ Nm
  gain_A : 1000000 * K * (K + 1) * N ^ (2 * ε) ≤ Nm ^ η
  gain_count : (a / ah) ^ d ≤ Nm ^ ((1 - d) / 2)
  thick_count : a ^ ((1 + d) / 2) ≤ ah ^ d

/-- Cancel a positive finite palette weight from a floor/cap comparison. -/
theorem card_le_of_floor {c : ℕ} {x y : ℝ} {p : ENNReal} (hx : 0 < x) (hy : 0 ≤ y)
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (h : (c : ENNReal) * (ENNReal.ofReal x * p) ≤ ENNReal.ofReal y * p) : (c : ℝ) * x ≤ y := by
  have h' : (c : ENNReal) * ENNReal.ofReal x ≤ ENNReal.ofReal y := by
    rw [← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hp0 hpt).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg c)] at h'
  exact (ENNReal.ofReal_le_ofReal_iff hy).mp h'

/-- Offset variation in the fine jet regime. -/
theorem jet_theta_le {a M Nε X Xκ : ℝ} (ha : 0 < a) (hM : 0 < M) (hNε : 0 ≤ Nε)
    (hX : 1120 * X ≤ 27 * a) (hXκ : Xκ ≤ X) (hXκ0 : 0 ≤ Xκ) (ha1 : a ≤ 1) (hMN : 3 * Nε ≤ M) :
    a * (160 * Nε / a + M) * 7 * Xκ ≤ 18 * a * M := by
  have he : a * (160 * Nε / a + M) = 160 * Nε + a * M := by field_simp
  rw [he]
  have hX0 : 0 ≤ X := hXκ0.trans hXκ
  have h7 : 7 * X ≤ 1 := by nlinarith
  have h1 : 160 * Nε * 7 * Xκ ≤ 9 * a * M := by
    have : 160 * Nε * 7 * Xκ ≤ 160 * Nε * 7 * X := by
      apply mul_le_mul_of_nonneg_left hXκ; positivity
    nlinarith
  have h2 : a * M * 7 * Xκ ≤ a * M := by
    have : a * M * 7 * Xκ ≤ a * M * 7 * X := by
      apply mul_le_mul_of_nonneg_left hXκ; positivity
    have hp : 0 < a * M := mul_pos ha hM
    nlinarith
  nlinarith

/-- The fine regime count against the matching budget. -/
theorem fine_count_le {c K Nε Nm M a ah d χ D ζ₀ : ℝ} (hc : 0 ≤ c) (hK : 1 ≤ K) (hNε : 1 ≤ Nε)
    (hNm : 1 ≤ Nm) (hMNm : Nm ≤ M) (ha : 0 < a) (hah : 0 < ah) (hχ : 0 < χ) (hD : 0 < D)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hDsum : D / 2 + χ / 2 + ζ₀ ≤ D)
    (hgc : (a / ah) ^ d ≤ Nm ^ ((1 - d) / 2))
    (hcard : c * (χ * D * ah ^ d / Nε) ≤ 3000 * K * χ * (D / 2 + χ / 2 + ζ₀) * (18 * a * M) ^ d) :
    c ≤ 1000000 * K * (K + 1) * (Nε * Nε) * (M / (3 * Nε)) ^ ((1 + d) / 2) := by
  have hM : 0 < M := by linarith
  have hah' : 0 < ah ^ d := Real.rpow_pos_of_pos hah _
  have hsplit : (18 * a * M) ^ d = 18 ^ d * (a / ah) ^ d * ah ^ d * M ^ d := by
    have h1 : (18 * a * M) ^ d = 18 ^ d * a ^ d * M ^ d := by
      rw [Real.mul_rpow (by positivity) hM.le, Real.mul_rpow (by norm_num) ha.le]
    have h2 : (a / ah) ^ d * ah ^ d = a ^ d := by
      rw [Real.div_rpow ha.le hah.le]; field_simp
    rw [h1, mul_assoc (18 ^ d) ((a / ah) ^ d), h2]
  have h18 : (18 : ℝ) ^ d ≤ 18 := by
    calc (18 : ℝ) ^ d ≤ 18 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
      _ = 18 := Real.rpow_one 18
  have hMd : 0 ≤ M ^ d := by positivity
  have hfac : 0 ≤ (a / ah) ^ d := by positivity
  -- step 1: `c ≤ 54000 K Nε Nm^((1-d)/2) M^d`
  have hstep1 : c ≤ 54000 * K * Nε * Nm ^ ((1 - d) / 2) * M ^ d := by
    have hden : 0 < χ * D * ah ^ d / Nε := by positivity
    have hrhs : 3000 * K * χ * (D / 2 + χ / 2 + ζ₀) * (18 * a * M) ^ d ≤
        (54000 * K * Nε * Nm ^ ((1 - d) / 2) * M ^ d) * (χ * D * ah ^ d / Nε) := by
      rw [hsplit]
      have e : (54000 * K * Nε * Nm ^ ((1 - d) / 2) * M ^ d) * (χ * D * ah ^ d / Nε) =
          3000 * K * χ * D * (18 * Nm ^ ((1 - d) / 2)) * ah ^ d * M ^ d := by
        field_simp; ring
      rw [e]
      have h1 : 3000 * K * χ * (D / 2 + χ / 2 + ζ₀) ≤ 3000 * K * χ * D := by
        apply mul_le_mul_of_nonneg_left hDsum; positivity
      have h2 : 18 ^ d * (a / ah) ^ d ≤ 18 * Nm ^ ((1 - d) / 2) := by
        calc 18 ^ d * (a / ah) ^ d ≤ 18 * (a / ah) ^ d := by gcongr
          _ ≤ 18 * Nm ^ ((1 - d) / 2) := by gcongr
      have hpos : 0 ≤ ah ^ d * M ^ d := by positivity
      calc 3000 * K * χ * (D / 2 + χ / 2 + ζ₀) * (18 ^ d * (a / ah) ^ d * ah ^ d * M ^ d)
          = (3000 * K * χ * (D / 2 + χ / 2 + ζ₀)) * (18 ^ d * (a / ah) ^ d) * (ah ^ d * M ^ d) := by
            ring
        _ ≤ (3000 * K * χ * D) * (18 * Nm ^ ((1 - d) / 2)) * (ah ^ d * M ^ d) := by
            gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right (hcard.trans hrhs) hden
  -- step 2: the matching budget dominates
  have hMdg : M ^ ((1 + d) / 2) = M ^ d * M ^ ((1 - d) / 2) := by
    rw [← Real.rpow_add hM]; ring_nf
  have hMd2 : Nm ^ ((1 - d) / 2) ≤ M ^ ((1 - d) / 2) :=
    Real.rpow_le_rpow (by linarith) hMNm (by linarith)
  have hδdg : (3 * Nε) ^ ((1 + d) / 2) ≤ 3 * Nε := by
    calc (3 * Nε) ^ ((1 + d) / 2) ≤ (3 * Nε) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 3 * Nε := Real.rpow_one _
  have hδpos : 0 < (3 * Nε) ^ ((1 + d) / 2) := by positivity
  rw [Real.div_rpow hM.le (by positivity), hMdg, mul_div_assoc', le_div_iff₀ hδpos]
  have hNm0 : 0 ≤ Nm ^ ((1 - d) / 2) := by positivity
  calc c * (3 * Nε) ^ ((1 + d) / 2)
      ≤ (54000 * K * Nε * Nm ^ ((1 - d) / 2) * M ^ d) * (3 * Nε) := by
        gcongr
  _ ≤ 1000000 * K * (K + 1) * (Nε * Nε) * (M ^ d * M ^ ((1 - d) / 2)) := by
        have hK0 : 0 ≤ K := by linarith
        have e : (54000 * K * Nε * Nm ^ ((1 - d) / 2) * M ^ d) * (3 * Nε) =
            (162000 * K) * (Nε * Nε) * (Nm ^ ((1 - d) / 2) * M ^ d) := by ring
        rw [e]
        have h1 : 162000 * K ≤ 1000000 * K * (K + 1) := by nlinarith
        have h2 : Nm ^ ((1 - d) / 2) * M ^ d ≤ M ^ d * M ^ ((1 - d) / 2) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hMd2 hMd
        have hNN : 0 ≤ Nε * Nε := by positivity
        calc (162000 * K) * (Nε * Nε) * (Nm ^ ((1 - d) / 2) * M ^ d)
            ≤ (1000000 * K * (K + 1)) * (Nε * Nε) * (M ^ d * M ^ ((1 - d) / 2)) := by
              gcongr
          _ = _ := by ring

/-- The coarse regime count against the matching budget. -/
theorem coarse_count_le {c K Nε M a ah d : ℝ} (hK : 1 ≤ K) (hNε : 1 ≤ Nε) (ha : 0 < a)
    (hah : 0 < ah) (hd0 : 0 ≤ d) (hd1 : d < 1) (hreg : 1 < 18 * a * M)
    (htc : a ^ ((1 + d) / 2) ≤ ah ^ d) (hc : c ≤ 6000 * K * (K + 1) * Nε / ah ^ d) :
    c ≤ 1000000 * K * (K + 1) * (Nε * Nε) * (M / (3 * Nε)) ^ ((1 + d) / 2) := by
  have hM : 0 < M := by
    by_contra h; push_neg at h; nlinarith
  have hdg0 : 0 ≤ (1 + d) / 2 := by linarith
  have hdg1 : (1 + d) / 2 ≤ 1 := by linarith
  have hah' : 0 < ah ^ d := Real.rpow_pos_of_pos hah _
  have hadg : 0 < a ^ ((1 + d) / 2) := Real.rpow_pos_of_pos ha _
  have hM' : 1 / (54 * a * Nε) ≤ M / (3 * Nε) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlow : (a ^ ((1 + d) / 2))⁻¹ / (54 * Nε) ≤ (M / (3 * Nε)) ^ ((1 + d) / 2) := by
    calc (a ^ ((1 + d) / 2))⁻¹ / (54 * Nε)
        ≤ (a ^ ((1 + d) / 2))⁻¹ / (54 * Nε) ^ ((1 + d) / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          calc (54 * Nε) ^ ((1 + d) / 2) ≤ (54 * Nε) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hdg1
            _ = 54 * Nε := Real.rpow_one _
      _ = (1 / (54 * a * Nε)) ^ ((1 + d) / 2) := by
          rw [one_div, Real.inv_rpow (by positivity), mul_comm 54 a, mul_assoc,
            Real.mul_rpow ha.le (by positivity)]
          field_simp
      _ ≤ (M / (3 * Nε)) ^ ((1 + d) / 2) := Real.rpow_le_rpow (by positivity) hM' hdg0
  have hstep : 6000 * K * (K + 1) * Nε / ah ^ d ≤
      1000000 * K * (K + 1) * (Nε * Nε) * ((a ^ ((1 + d) / 2))⁻¹ / (54 * Nε)) := by
    have e : 1000000 * K * (K + 1) * (Nε * Nε) * ((a ^ ((1 + d) / 2))⁻¹ / (54 * Nε)) =
        (1000000 / 54) * K * (K + 1) * Nε / a ^ ((1 + d) / 2) := by field_simp
    rw [e, div_le_div_iff₀ hah' hadg]
    have hKK : 0 ≤ K * (K + 1) * Nε := by positivity
    calc 6000 * K * (K + 1) * Nε * a ^ ((1 + d) / 2)
        ≤ 6000 * K * (K + 1) * Nε * ah ^ d := by gcongr
      _ ≤ 1000000 / 54 * K * (K + 1) * Nε * ah ^ d := by
          have : (6000 : ℝ) ≤ 1000000 / 54 := by norm_num
          gcongr
  calc c ≤ 6000 * K * (K + 1) * Nε / ah ^ d := hc
    _ ≤ 1000000 * K * (K + 1) * (Nε * Nε) * ((a ^ ((1 + d) / 2))⁻¹ / (54 * Nε)) := hstep
    _ ≤ 1000000 * K * (K + 1) * (Nε * Nε) * (M / (3 * Nε)) ^ ((1 + d) / 2) := by
        gcongr

/-- **Jet counts of one family**, both regimes. -/
theorem LayerDatum.jet_count {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ r M' Nm R₀ η : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ (cfg.K k))ᶜ = 0)
    (hχv : χ = cfg.N k ^ (-M')) (h : Fin 3) (κ : Fin 3 → ℤ)
    (hcaps : ∀ s' : ℝ, 0 ≤ s' → s' ≤ depth 0 →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' M')
    (hnum : CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
      (cfg.N k ^ (-depth h)) Nm R₀ η)
    (hd0 : 0 ≤ cfg.d) (hd1 : cfg.d < 1)
    (hπ0 : cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ)) ≠ 0)
    (hπt : cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ)) ≠ ⊤)
    (hκ : ∃ i, L.qp h i = κ)
    (ref : Fin 6 → ℝ) {M : ℝ} (hM : 3 * cfg.N k ^ ε * Nm ≤ M) :
    ((Finset.univ.filter (fun i => L.qp h i = κ ∧
        ∀ k', |keySheet (L.G h i) κ χ D (cfg.N k ^ (-depth 0)) k' - ref k'| ≤ M)).card : ℝ) ≤
      1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) *
        (M / (3 * cfg.N k ^ ε)) ^ ((1 + cfg.d) / 2) := by
  classical
  have hN1 : 1 < cfg.N k := hnum.N_gt
  have hN0 : 0 < cfg.N k := by linarith
  have hε := hnum.eps_pos
  have hK1 := hnum.K_one
  have ha0 := hnum.a_pos
  have ha1 := hnum.a_le
  have hah0 := hnum.ah_pos
  have haha := hnum.ah_le
  have hχ := hnum.χ_pos
  have hD := hnum.D_pos
  have hD1 := hnum.D_le
  have hζ₀ := hnum.ζ₀_nonneg
  have hNm := hnum.gain_one
  have hNε : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow hN1.le hε.le
  have hN2ε : cfg.N k ^ (2 * ε) = cfg.N k ^ ε * cfg.N k ^ ε := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [hN2ε]
  have hMpos : 0 < M := by nlinarith
  have hMNm : Nm ≤ M := by nlinarith
  obtain ⟨i₀, hi₀⟩ := hκ
  have hkey := L.key_bound h i₀
  rw [hi₀] at hkey
  have hκ1 : |(κ 1 : ℝ) * χ| ≤ cfg.N k ^ ε := by
    linarith [abs_nonneg ((κ 2 : ℝ) * D), abs_nonneg ((κ 0 : ℝ) * χ)]
  have hr : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hδχ : (|(κ 0 : ℝ) * χ| + |(κ 1 : ℝ) * χ| + χ + 1) * cfg.N k ^ (-r) ≤ χ / 2 := by
    have h1 := hnum.cell_chart
    have : |(κ 0 : ℝ) * χ| + |(κ 1 : ℝ) * χ| + χ + 1 ≤ cfg.N k ^ ε + χ + 1 := by
      linarith [abs_nonneg ((κ 2 : ℝ) * D)]
    calc _ ≤ (cfg.N k ^ ε + χ + 1) * cfg.N k ^ (-r) := mul_le_mul_of_nonneg_right this hr.le
      _ ≤ χ / 2 := h1
  have hdrift : ζ₀ + χ ≤ D / 4 := by
    have h1 := hnum.drift
    have h2 : D * cfg.N k ^ (-depth 0) / 960 ≤ D / 960 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc D * cfg.N k ^ (-depth 0) ≤ D * 1 := mul_le_mul_of_nonneg_left ha1 hD.le
        _ = D := mul_one D
    linarith
  have hsmall : (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) ≤ D := by
    calc (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) ≤ (1 + cfg.N k ^ ε) * cfg.N k ^ (-r) :=
          mul_le_mul_of_nonneg_right (by linarith) hr.le
      _ ≤ D := hnum.cell_strip
  have hDsum : D / 2 + χ / 2 + ζ₀ ≤ D := by
    have h1 := hnum.drift
    have h2 : D * cfg.N k ^ (-depth 0) / 960 ≤ D / 2 := by
      have : D * cfg.N k ^ (-depth 0) ≤ D := by nlinarith
      linarith
    linarith
  by_cases hreg : 18 * cfg.N k ^ (-depth 0) * M ≤ 1
  · -- fine regime: bins of width `18 a M`
    set s' : ℝ := -Real.logb (cfg.N k) (18 * cfg.N k ^ (-depth 0) * M) with hs'
    have hβ : 18 * cfg.N k ^ (-depth 0) * M = cfg.N k ^ (-s') := by
      rw [hs', neg_neg, Real.rpow_logb hN0 hN1.ne' (by positivity)]
    have hs'0 : 0 ≤ s' := by
      rw [hs', neg_nonneg]; exact Real.logb_nonpos hN1 (by positivity) hreg
    have hs'd : s' ≤ depth 0 := by
      have h18 : cfg.N k ^ (-depth 0) ≤ 18 * cfg.N k ^ (-depth 0) * M := by nlinarith
      have := Real.logb_le_logb_of_le hN1 ha0 h18
      have hla : Real.logb (cfg.N k) (cfg.N k ^ (-depth 0)) = -depth 0 := by
        rw [Real.logb_rpow hN0 hN1.ne']
      rw [hs']; linarith
    have hB : ∀ i, L.qp h i = κ → ∀ k',
        |keySheet (L.G h i) κ χ D (cfg.N k ^ (-depth 0)) k'| ≤
          160 * cfg.N k ^ ε / cfg.N k ^ (-depth 0) := by
      intro i hi k'
      have hstrip := L.strip h i
      rw [hi] at hstrip
      have := sheetCoeff_bound (L.degree h i) hstrip k'
      simp only [keySheet, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos ha0]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr ha0.le)
    have hθ := jet_theta_le (Nε := cfg.N k ^ ε) ha0 hMpos (by positivity) hnum.cell_jet
      (Xκ := cfg.N k ^ (-r) + (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D))
      (by gcongr) (by positivity) ha1 (by nlinarith)
    have hfitw : cfg.N k ^ ε * cfg.N k ^ (-depth h) ≤ 3 * cfg.N k ^ (-depth 0) * M := by
      have : cfg.N k ^ ε ≤ M := by nlinarith
      nlinarith
    have hmain := L.jet_count_fine hb hρμ hgood hζ₀ (hcaps s' hs'0 hs'd) hN0
      (by linarith) hχv hD h κ ha0 ref hB hβ hfitw hδχ hnum.cell_half hθ hdrift hsmall
    have hcard := card_le_of_floor (by positivity) (by positivity) hπ0 hπt hmain
    push_cast at hcard
    rw [mul_one] at hcard
    exact fine_count_le (Nat.cast_nonneg _) hK1 hNε hNm hMNm ha0 hah0 hχ hD hd0 hd1 hDsum
      hnum.gain_count hcard
  · -- coarse regime: count all pieces of the key
    push_neg at hreg
    have hcap0 := hcaps 0 le_rfl (by
      by_contra hcon; push_neg at hcon
      have : 1 < cfg.N k ^ (-depth 0) := Real.one_lt_rpow hN1 (by linarith)
      linarith)
    have hmain := L.key_count hb hρμ hgood hζ₀ (by linarith) hcap0 hN0 (by linarith) hχv hD
      h κ hδχ hnum.cell_half
    have hN0' : cfg.N k ^ (-(0 : ℝ)) = 1 := by simp
    rw [hN0', Real.one_rpow, mul_one] at hmain
    have hcard := card_le_of_floor (by positivity) (by positivity) hπ0 hπt hmain
    have hceil : ((⌈2 * cfg.K k⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * cfg.K k + 2 := by
      push_cast; linarith [Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ 2 * cfg.K k)]
    have hcnt : ((Finset.univ.filter (fun i => L.qp h i = κ)).card : ℝ) ≤
        6000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ ε / (cfg.N k ^ (-depth h)) ^ cfg.d := by
      have hah' : 0 < (cfg.N k ^ (-depth h)) ^ cfg.d := Real.rpow_pos_of_pos hah0 _
      have hden : 0 < χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε := by positivity
      have hrhs : 3000 * cfg.K k * ((⌈2 * cfg.K k⌉₊ + 1 : ℕ) : ℝ) * χ * (D / 2 + χ / 2 + ζ₀) ≤
          (6000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ ε / (cfg.N k ^ (-depth h)) ^ cfg.d) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) := by
        have e : (6000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ ε / (cfg.N k ^ (-depth h)) ^ cfg.d) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) =
            3000 * cfg.K k * (2 * cfg.K k + 2) * χ * D := by field_simp; ring
        rw [e]
        have hK0 : 0 ≤ 3000 * cfg.K k := by linarith
        calc 3000 * cfg.K k * ((⌈2 * cfg.K k⌉₊ + 1 : ℕ) : ℝ) * χ * (D / 2 + χ / 2 + ζ₀)
            ≤ 3000 * cfg.K k * (2 * cfg.K k + 2) * χ * D := by gcongr
          _ = _ := rfl
      exact le_of_mul_le_mul_right (hcard.trans hrhs) hden
    have hJsub : ((Finset.univ.filter (fun i => L.qp h i = κ ∧
        ∀ k', |keySheet (L.G h i) κ χ D (cfg.N k ^ (-depth 0)) k' - ref k'| ≤ M)).card : ℝ) ≤
        ((Finset.univ.filter (fun i => L.qp h i = κ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1)
    exact coarse_count_le hK1 hNε ha0 hah0 hd0 hd1 hreg hnum.thick_count (hJsub.trans hcnt)

/-- The reference weight of a piece. -/
def refWeight {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (i : Fin (L.np h)) : ℝ :=
  χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d *
    (cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal

/-- The normalized sheet of a piece in its own key. -/
def LayerDatum.sheet {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (i : Fin (L.np h)) : Fin 6 → ℝ :=
  keySheet (L.G h i) (L.qp h i) χ D (cfg.N k ^ (-depth 0))

/-- The interval ceiling in the form of `key_compare`. -/
theorem LayerDatum.interval_ceiling' {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k) [IsFiniteMeasure (cfg.π k)]
    {ζ₀ r M' Nm R₀ η : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ (cfg.K k))ᶜ = 0)
    (hχv : χ = cfg.N k ^ (-M')) (h : Fin 3)
    (hcap : JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r
      (depth h - ε) M')
    (hnum : CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
      (cfg.N k ^ (-depth h)) Nm R₀ η)
    (i : Fin (L.np h)) (κ : Fin 3 → ℤ) (hi : L.qp h i = κ) (x : ℝ) :
    L.ρs ((L.C h i ∩ {l | etaOf ((κ 2 : ℝ) * D) D (cfg.b k l 1) ∈
        Icc (x - cfg.N k ^ (-depth 0) / 960) x}) ×ˢ univ) ≤
      ENNReal.ofReal (1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) * refWeight L h i *
        (cfg.N k ^ (-depth 0) / 960)) := by
  have hN1 : 1 < cfg.N k := hnum.N_gt
  have hN0 : 0 < cfg.N k := by linarith
  have hε := hnum.eps_pos
  have hK1 := hnum.K_one
  have ha0 := hnum.a_pos
  have ha1 := hnum.a_le
  have hah0 := hnum.ah_pos
  have haha := hnum.ah_le
  have hχ := hnum.χ_pos
  have hD := hnum.D_pos
  have hζ₀ := hnum.ζ₀_nonneg
  have hNε : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow hN1.le hε.le
  have hr : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hkey := L.key_bound h i
  have hκ1 : |(L.qp h i 1 : ℝ) * χ| ≤ cfg.N k ^ ε := by
    linarith [abs_nonneg ((L.qp h i 2 : ℝ) * D), abs_nonneg ((L.qp h i 0 : ℝ) * χ)]
  have hδχ : (|(L.qp h i 0 : ℝ) * χ| + |(L.qp h i 1 : ℝ) * χ| + χ + 1) * cfg.N k ^ (-r) ≤
      χ / 2 := by
    have : |(L.qp h i 0 : ℝ) * χ| + |(L.qp h i 1 : ℝ) * χ| + χ + 1 ≤ cfg.N k ^ ε + χ + 1 := by
      linarith [abs_nonneg ((L.qp h i 2 : ℝ) * D)]
    exact (mul_le_mul_of_nonneg_right this hr.le).trans hnum.cell_chart
  have hfitw : cfg.N k ^ ε * cfg.N k ^ (-depth h) ≤ cfg.N k ^ (-(depth h - ε)) := by
    rw [show -(depth h - ε) = ε + -depth h by ring, Real.rpow_add hN0]
  have hX : cfg.N k ^ (-r) + (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) ≤
      cfg.N k ^ (-r) + (1 + cfg.N k ^ ε) * cfg.N k ^ (-r) / (4 * D) := by gcongr
  have hθ : 1120 * cfg.N k ^ ε * (cfg.N k ^ (-r) +
      (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D)) ≤ cfg.N k ^ (-(depth h - ε)) := by
    rw [show -(depth h - ε) = ε + -depth h by ring, Real.rpow_add hN0]
    have := hnum.cell_fit
    have hpos : 0 < cfg.N k ^ ε := by positivity
    calc 1120 * cfg.N k ^ ε * (cfg.N k ^ (-r) +
          (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D))
        ≤ cfg.N k ^ ε * (1120 * (cfg.N k ^ (-r) + (1 + cfg.N k ^ ε) * cfg.N k ^ (-r) / (4 * D))) := by
          nlinarith
      _ ≤ cfg.N k ^ ε * cfg.N k ^ (-depth h) := mul_le_mul_of_nonneg_left this hpos.le
  have hdrift : ζ₀ + χ ≤ D / 4 := by
    have h1 := hnum.drift
    have : D * cfg.N k ^ (-depth 0) / 960 ≤ D / 960 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    linarith
  have hsmall : (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) ≤ D :=
    (mul_le_mul_of_nonneg_right (by linarith) hr.le).trans hnum.cell_strip
  have hw : 0 < cfg.N k ^ (-depth 0) / 960 := by positivity
  have hmain := L.interval_ceiling hb hρμ hgood hζ₀ hcap hN0 (by linarith) hχv hD h i hw
    (x := x) hfitw hδχ hnum.cell_half hθ hdrift hsmall
  rw [hi] at hmain
  refine hmain.trans ?_
  set π₀ := cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ))
  have hπt : π₀ ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hπt, ← ENNReal.ofReal_mul (by
    have : 0 ≤ (cfg.N k ^ (-(depth h - ε))) ^ cfg.d := by positivity
    positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hπ0 : 0 ≤ π₀.toReal := ENNReal.toReal_nonneg
  have hpow : (cfg.N k ^ (-(depth h - ε))) ^ cfg.d =
      (cfg.N k ^ ε) ^ cfg.d * (cfg.N k ^ (-depth h)) ^ cfg.d := by
    rw [show -(depth h - ε) = ε + -depth h by ring, Real.rpow_add hN0,
      Real.mul_rpow (by positivity) (by positivity)]
  have hNεd : (cfg.N k ^ ε) ^ cfg.d ≤ cfg.N k ^ (2 * ε) := by
    rw [← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    nlinarith [hnum.eps_pos, hnum.d_lt, hnum.d_nonneg]
  have hwidth : 2 * D * (cfg.N k ^ (-depth 0) / 960) + χ / 2 + ζ₀ ≤
      3 * D * (cfg.N k ^ (-depth 0) / 960) := by
    have := hnum.drift; linarith
  rw [hpow]
  unfold refWeight
  rw [hi]
  have hahd : 0 ≤ (cfg.N k ^ (-depth h)) ^ cfg.d := by positivity
  have hK0 : 0 ≤ cfg.K k := by linarith
  calc 3000 * cfg.K k * ((2 : ℕ) : ℝ) * χ * (2 * D * (cfg.N k ^ (-depth 0) / 960) + χ / 2 + ζ₀) *
        ((cfg.N k ^ ε) ^ cfg.d * (cfg.N k ^ (-depth h)) ^ cfg.d) * π₀.toReal
      ≤ 3000 * cfg.K k * 2 * χ * (3 * D * (cfg.N k ^ (-depth 0) / 960)) *
        (cfg.N k ^ (2 * ε) * (cfg.N k ^ (-depth h)) ^ cfg.d) * π₀.toReal := by
        push_cast
        gcongr
    _ = 18000 * cfg.K k * cfg.N k ^ (2 * ε) * (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) *
        (cfg.N k ^ (-depth 0) / 960) := by ring
    _ ≤ 1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) *
        (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) * (cfg.N k ^ (-depth 0) / 960) := by
        have hT0 : 0 ≤ cfg.N k ^ (2 * ε) * (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) *
            (cfg.N k ^ (-depth 0) / 960) := by positivity
        have h18 : 18000 * cfg.K k ≤ 1000000 * cfg.K k * (cfg.K k + 1) := by nlinarith
        have e1 : 18000 * cfg.K k * cfg.N k ^ (2 * ε) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) * (cfg.N k ^ (-depth 0) / 960) =
            (18000 * cfg.K k) * (cfg.N k ^ (2 * ε) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) * (cfg.N k ^ (-depth 0) / 960)) := by
          ring
        have e2 : 1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) * (cfg.N k ^ (-depth 0) / 960) =
            (1000000 * cfg.K k * (cfg.K k + 1)) * (cfg.N k ^ (2 * ε) *
            (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d * π₀.toReal) * (cfg.N k ^ (-depth 0) / 960)) := by
          ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right h18 hT0

/-- A velocity bin of zero palette weight carries no incidences. -/
theorem velocityBin_null {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d r s' v' : ℝ} (hcap : JointCapAt μ π b N K d r s' v') (v₀ : ℤ)
    (hπ : π {w | ⌊w / N ^ (-v')⌋ = v₀} = 0) :
    μ {p | ⌊b p.1 3 / N ^ (-v')⌋ = v₀} = 0 := by
  have hsub : {p : α × ℝ | ⌊b p.1 3 / N ^ (-v')⌋ = v₀} ⊆
      ⋃ q : Fin 3 → ℤ, ⋃ a : ℤ, {p | baseMesh (N ^ (-r)) (basePt b p) = q ∧
        ⌊hidden b p / N ^ (-s')⌋ = a ∧ ⌊b p.1 3 / N ^ (-v')⌋ = v₀} := by
    intro p hp
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨_, rfl, rfl, hp⟩⟩
  refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun a => ?_)
  refine le_antisymm ((hcap q a v₀).trans (le_of_eq ?_)) bot_le
  rw [hπ, mul_zero]

theorem measurable_etaOf (y₀ D : ℝ) : Measurable (etaOf y₀ D) := by
  unfold etaOf; fun_prop

/-- **Bad pairs of one key.** -/
theorem key_bad_le (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (cfg : Data α) (k : ℕ) (ε R χ D : ℝ) (depth : Fin 3 → ℝ)
      (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (ζ₀ r M' Nm : ℝ) (κ : Fin 3 → ℤ),
      cfg.d = d → Measurable (cfg.b k) → cfg.ρ k ≤ cfg.μ k →
      IsFiniteMeasure (cfg.μ k) → IsFiniteMeasure (cfg.π k) →
      cfg.μ k (goodSet (cfg.b k) ζ₀ (cfg.K k))ᶜ = 0 →
      (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀) →
      χ = cfg.N k ^ (-M') →
      (∀ s' : ℝ, 0 ≤ s' → s' ≤ depth 0 →
        JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' M') →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r (depth 0 - ε) M' →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r (depth h - ε) M' →
      CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
        (cfg.N k ^ (-depth 0)) Nm R₀ η →
      CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
        (cfg.N k ^ (-depth h)) Nm R₀ η →
      (∃ i, L.qp 0 i = κ) →
      (∑ i ∈ Finset.univ.filter (fun i => L.qp 0 i = κ),
        ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = κ ∧
          ∃ k', 3 * cfg.N k ^ ε * Nm ≤ |L.sheet 0 i k' - L.sheet h j k'|),
          L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) ≤
        ENNReal.ofReal (1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) * Nm ^ (-η) *
          (∑ i ∈ Finset.univ.filter (fun i => L.qp 0 i = κ), refWeight L 0 i +
            ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = κ), refWeight L h j)) := by
  obtain ⟨η, hη, R₀, hR₀, KC⟩ := key_compare (α := α) hM (dg := (1 + d) / 2) (by linarith) (by linarith)
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro cfg k ε R χ D depth L h ζ₀ r M' Nm κ hdd hb hρμ hμfin hπfin hgood hhor hχv hcaps hcap0
    hcaph hnum0 hnumh hκ
  classical
  have hN1 : 1 < cfg.N k := hnum0.N_gt
  have hN0 : 0 < cfg.N k := by linarith
  have hε := hnum0.eps_pos
  have hK1 := hnum0.K_one
  have ha0 := hnum0.a_pos
  have ha1 := hnum0.a_le
  have hχ := hnum0.χ_pos
  have hD := hnum0.D_pos
  have hNε : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow hN1.le hε.le
  haveI : IsFiniteMeasure L.ρs := isFiniteMeasure_of_le _ (L.le_rho.trans hρμ)
  set π₀ := cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ)) with hπ₀
  have hπt : π₀ ≠ ⊤ := measure_ne_top _ _
  by_cases hπ0 : π₀ = 0
  · -- a null velocity bin: no mass
    have hnull : cfg.μ k {p | ⌊cfg.b k p.1 3 / cfg.N k ^ (-M')⌋ = κ 0} = 0 := by
      apply velocityBin_null (hcaps 0 le_rfl (by
        by_contra hcon; push_neg at hcon
        have : 1 < cfg.N k ^ (-depth 0) := Real.one_lt_rpow hN1 (by linarith)
        linarith))
      rw [← hχv, floorBin_eq_Ico hχ]; exact hπ0
    refine le_trans (le_of_eq ?_) bot_le
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    have hi' := (Finset.mem_filter.mp hi).2
    apply le_antisymm _ bot_le
    calc L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)
        ≤ cfg.μ k {p | ⌊cfg.b k p.1 3 / cfg.N k ^ (-M')⌋ = κ 0} := by
          refine ((L.le_rho.trans hρμ) _).trans (measure_mono ?_)
          rintro p ⟨⟨hp1, -⟩, -⟩
          have := (L.mem_bins hp1).1
          rw [hi', hχv] at this
          exact this
      _ = 0 := hnull
  -- the main case: apply the matching lemma on the key
  have hδ : (0 : ℝ) < 3 * cfg.N k ^ ε := by positivity
  set A : ℝ := 1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ cfg.N k ^ (2 * ε) := Real.one_le_rpow hN1.le (by linarith)
    have hKK : 1 ≤ cfg.K k * (cfg.K k + 1) := by nlinarith
    calc (1 : ℝ) ≤ 1000000 * 1 * 1 := by norm_num
      _ ≤ 1000000 * (cfg.K k * (cfg.K k + 1)) * cfg.N k ^ (2 * ε) := by gcongr
      _ = A := by rw [hAdef]; ring
  have hMstδ : 3 * cfg.N k ^ ε * Nm / (3 * cfg.N k ^ ε) = Nm := by field_simp
  have hsheet0 : ∀ i, L.qp 0 i = κ → L.sheet 0 i = keySheet (L.G 0 i) κ χ D (cfg.N k ^ (-depth 0)) :=
    fun i hi => by rw [LayerDatum.sheet, hi]
  have hsheeth : ∀ j, L.qp h j = κ → L.sheet h j = keySheet (L.G h j) κ χ D (cfg.N k ^ (-depth 0)) :=
    fun j hj => by rw [LayerDatum.sheet, hj]
  have hBnd : ∀ (h' : Fin 3) (i : Fin (L.np h')) (k' : Fin 6),
      |L.sheet h' i k'| ≤ 160 * cfg.N k ^ ε / cfg.N k ^ (-depth 0) := by
    intro h' i k'
    have := sheetCoeff_bound (L.degree h' i) (L.strip h' i) k'
    simp only [LayerDatum.sheet, keySheet, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv,
      abs_of_pos ha0]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr ha0.le)
  have hcount : ∀ (h' : Fin 3) (hnum : CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r
      (cfg.N k ^ (-depth 0)) (cfg.N k ^ (-depth h')) Nm R₀ η) (rr : Fin 6 → ℝ) (M : ℝ),
      3 * cfg.N k ^ ε * Nm ≤ M →
      ((Finset.univ.filter (fun i => L.qp h' i = κ ∧ ∀ k', |L.sheet h' i k' - rr k'| ≤ M)).card : ℝ) ≤
        A * (M / (3 * cfg.N k ^ ε)) ^ ((1 + d) / 2) := by
    intro h' hnum rr M hMM
    by_cases hκ' : ∃ i, L.qp h' i = κ
    · have hfilt : Finset.univ.filter (fun i => L.qp h' i = κ ∧ ∀ k', |L.sheet h' i k' - rr k'| ≤ M) =
          Finset.univ.filter (fun i => L.qp h' i = κ ∧
            ∀ k', |keySheet (L.G h' i) κ χ D (cfg.N k ^ (-depth 0)) k' - rr k'| ≤ M) := by
        apply Finset.filter_congr
        intro i _
        constructor
        · rintro ⟨hi, hm⟩; exact ⟨hi, by rw [LayerDatum.sheet, hi] at hm; exact hm⟩
        · rintro ⟨hi, hm⟩; exact ⟨hi, by rw [LayerDatum.sheet, hi]; exact hm⟩
      rw [hfilt, hAdef, ← hdd]
      exact L.jet_count hb hρμ hgood hχv h' κ hcaps hnum hnum.d_nonneg hnum.d_lt hπ0 hπt hκ' rr hMM
    · have : Finset.univ.filter (fun i => L.qp h' i = κ ∧ ∀ k', |L.sheet h' i k' - rr k'| ≤ M) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi; exact hκ' ⟨i, hi.1⟩
      rw [this, Finset.card_empty, Nat.cast_zero]
      have hMpos : 0 < M := by nlinarith [hnum.gain_one]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (div_nonneg hMpos.le (by positivity)) _)
  have hmain := KC L.ρs (cfg.b k) hb (L.C 0) (L.C h) (L.qp 0) (L.qp h) κ (L.sheet 0) (L.sheet h)
    (refWeight L 0) (refWeight L h) (etaOf ((κ 2 : ℝ) * D) D) (3 * cfg.N k ^ ε)
    (3 * cfg.N k ^ ε * Nm) A (160 * cfg.N k ^ ε / cfg.N k ^ (-depth 0)) (cfg.N k ^ (-depth 0) / 960)
    (measurable_etaOf _ _) (L.meas 0) (L.meas h) (L.disj h) (L.disj 0) hδ
    (by rw [mul_comm (3 * cfg.N k ^ ε) Nm]; exact mul_le_mul_of_nonneg_right hnum0.gain_R₀ hδ.le)
    hA1 (by rw [hMstδ, hAdef]; exact hnum0.gain_A) (by positivity) (by linarith)
    (le_of_eq (by field_simp; ring)) (fun i => by unfold refWeight; positivity)
    (fun j => by unfold refWeight; positivity) (fun i k' => hBnd 0 i k') (fun j k' => hBnd h j k')
    (fun i hi x => by
      have := L.interval_ceiling' hb hρμ hgood hχv 0 hcap0 hnum0 i κ hi x
      rw [hAdef]; exact this)
    (fun j hj x => by
      have := L.interval_ceiling' hb hρμ hgood hχv h hcaph hnumh j κ hj x
      rw [hAdef]; exact this)
    (fun rr M hMM => hcount 0 hnum0 rr M hMM) (fun rr M hMM => hcount h hnumh rr M hMM)
    (fun i j hi hj => by
      have hDa : D * cfg.N k ^ (-depth 0) ≤ D := by nlinarith
      have hcl := L.close hρμ hhor hχ hD (by linarith [hnum0.drift, hnum0.ζ₀_nonneg]) i j κ hi hj ha0
        (δ := 3 * cfg.N k ^ ε) (by
          rw [div_le_iff₀ ha0]
          have h1 := hnumh.ah_le
          have h2 := hnum0.close
          have h3 : 80 * cfg.N k ^ ε * (ζ₀ + χ) / D ≤ cfg.N k ^ ε * cfg.N k ^ (-depth 0) := by
            have e : 80 * cfg.N k ^ ε * (ζ₀ + χ) / D = cfg.N k ^ ε * (80 * (ζ₀ + χ) / D) := by ring
            rw [e]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ cfg.N k ^ ε)])
      rw [hsheet0 i hi, hsheeth j hj]
      exact hcl)
  rw [hMstδ] at hmain
  exact hmain

/-- Pieces of two layers with different keys are disjoint. -/
theorem LayerDatum.inter_empty_of_key_ne {cfg : Data α} {k : ℕ} {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) {h₁ h₂ : Fin 3}
    {i : Fin (L.np h₁)} {j : Fin (L.np h₂)} (hne : L.qp h₂ j ≠ L.qp h₁ i) :
    L.C h₁ i ∩ L.C h₂ j = ∅ := by
  ext l
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  apply hne
  obtain ⟨a1, b1, c1, -⟩ := L.mem_bins h1
  obtain ⟨a2, b2, c2, -⟩ := L.mem_bins h2
  funext e
  fin_cases e
  · exact a2.symm.trans a1
  · exact b2.symm.trans b1
  · exact c2.symm.trans c1

/-- **Long-domain comparison of two layers at one index.** -/
theorem layer_bad_le (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (cfg : Data α) (k : ℕ) (ε R χ D : ℝ) (depth : Fin 3 → ℝ)
      (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (ζ₀ r M' Nm : ℝ),
      cfg.d = d → Measurable (cfg.b k) → cfg.ρ k ≤ cfg.μ k →
      IsFiniteMeasure (cfg.μ k) → IsFiniteMeasure (cfg.π k) →
      cfg.μ k (goodSet (cfg.b k) ζ₀ (cfg.K k))ᶜ = 0 →
      (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀) →
      χ = cfg.N k ^ (-M') →
      (∀ s' : ℝ, 0 ≤ s' → s' ≤ depth 0 →
        JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' M') →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r (depth 0 - ε) M' →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r (depth h - ε) M' →
      CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
        (cfg.N k ^ (-depth 0)) Nm R₀ η →
      CompareNumerics (cfg.N k) (cfg.K k) cfg.d ε χ D ζ₀ r (cfg.N k ^ (-depth 0))
        (cfg.N k ^ (-depth h)) Nm R₀ η →
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j =>
          ∃ k', 3 * cfg.N k ^ ε * Nm ≤ |L.sheet 0 i k' - L.sheet h j k'|),
          L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) ≤
        ENNReal.ofReal (1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) * Nm ^ (-η) *
          (∑ i, refWeight L 0 i + ∑ j, refWeight L h j)) := by
  obtain ⟨η, hη, R₀, hR₀, KB⟩ := key_bad_le (α := α) hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro cfg k ε R χ D depth L h ζ₀ r M' Nm hdd hb hρμ hμfin hπfin hgood hhor hχv hcaps hcap0
    hcaph hnum0 hnumh
  classical
  set A : ℝ := 1000000 * cfg.K k * (cfg.K k + 1) * cfg.N k ^ (2 * ε) * Nm ^ (-η) with hAdef
  have hA0 : 0 ≤ A := by
    have := hnum0.K_one
    have : 0 < cfg.N k := by linarith [hnum0.N_gt]
    have : 0 ≤ Nm := by linarith [hnum0.gain_one]
    positivity
  set keys := Finset.univ.image (L.qp 0) with hkeys
  set bad : Fin (L.np 0) → Fin (L.np h) → Prop := fun i j =>
    ∃ k', 3 * cfg.N k ^ ε * Nm ≤ |L.sheet 0 i k' - L.sheet h j k'|
  -- restrict each inner sum to the key of `i`
  have hinner : ∀ i, (∑ j ∈ Finset.univ.filter (fun j => bad i j),
      L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) =
      ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = L.qp 0 i ∧ bad i j),
        L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ) := by
    intro i
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.2
    · intro j hj hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hj hj'
      have hne : L.qp h j ≠ L.qp 0 i := fun he => hj' he hj
      rw [L.inter_empty_of_key_ne hne, empty_prod, measure_empty]
  have hlhs : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => bad i j),
      L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) =
      ∑ κ ∈ keys, ∑ i ∈ Finset.univ.filter (fun i => L.qp 0 i = κ),
        ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = κ ∧ bad i j),
          L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := keys) (g := L.qp 0)
      (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    apply Finset.sum_congr rfl
    intro κ _
    apply Finset.sum_congr rfl
    intro i hi
    rw [hinner i, (Finset.mem_filter.mp hi).2]
  change (∑ i, ∑ j ∈ Finset.univ.filter (fun j => bad i j),
      L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) ≤ _
  rw [hlhs]
  have hkey : ∀ κ ∈ keys, (∑ i ∈ Finset.univ.filter (fun i => L.qp 0 i = κ),
        ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = κ ∧ bad i j),
          L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ)) ≤
      ENNReal.ofReal (A * (∑ i ∈ Finset.univ.filter (fun i => L.qp 0 i = κ), refWeight L 0 i +
        ∑ j ∈ Finset.univ.filter (fun j => L.qp h j = κ), refWeight L h j)) := by
    intro κ hκ
    obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hκ
    have := KB cfg k ε R χ D depth L h ζ₀ r M' Nm κ hdd hb hρμ hμfin hπfin hgood hhor hχv hcaps
      hcap0 hcaph hnum0 hnumh ⟨i₀, hi₀⟩
    rw [hAdef]
    exact this
  refine (Finset.sum_le_sum hkey).trans ?_
  have hw0 : ∀ (h' : Fin 3) (i : Fin (L.np h')), 0 ≤ refWeight L h' i := by
    intro h' i
    have : 0 < cfg.N k := by linarith [hnum0.N_gt]
    unfold refWeight
    have := hnum0.χ_pos; have := hnum0.D_pos
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg (fun κ _ => mul_nonneg hA0 (add_nonneg
    (Finset.sum_nonneg fun i _ => hw0 0 i) (Finset.sum_nonneg fun j _ => hw0 h j)))]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hA0
  apply add_le_add
  · rw [Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := keys) (g := L.qp 0)
      (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  · rw [Finset.sum_fiberwise_eq_sum_filter (s := Finset.univ) (t := keys) (g := L.qp h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => hw0 h j)

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
