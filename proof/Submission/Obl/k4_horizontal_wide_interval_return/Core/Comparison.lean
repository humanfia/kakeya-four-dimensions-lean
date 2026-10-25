import Submission.Obl.k4_horizontal_wide_interval_return.Core.Agree
import Submission.Obl.k4_horizontal_wide_interval_return.Core.CompareEventually
import Submission.Obl.k4_horizontal_wide_interval_return.Core.IndexFacts

/-!
# The full-strip comparison of the projected layers (paper Prop. 8.4, long domains)

From Matching, a valid prepared parent and the three-layer datum: for every buffer, with the
same exponents, for every loss `ε` and all large indices, the datum (with loss `ε`) holds for a
restriction of `ρ⋆` on which, almost everywhere, the layer-`h` predictor of the piece of the
trajectory agrees with its layer-`0` predictor on the whole shared moving strip up to
`N^(ε + C_d u) N^-s`, `C_d = 10/(1-d)`.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_horizontal_wide_interval_return.MatchCor

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The strengthened datum at one index. -/
def AgreeAt (cfg : Data α) (k : ℕ) (ε R χ D s u : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∃ L : LayerDatum cfg k ε R χ D depth, ∀ᵐ p ∂L.ρs, ∀ h : Fin 3, h ≠ 0 →
    ∀ (i₀ : Fin (L.np 0)) (ih : Fin (L.np h)), p.1 ∈ L.C 0 i₀ → p.1 ∈ L.C h ih →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval (![t, (L.qp 0 i₀ 2 : ℝ) * D - t * ((L.qp 0 i₀ 1 : ℝ) * χ) + D * w] :
          Fin 2 → ℝ) (L.G h ih - L.G 0 i₀)| ≤
          cfg.N k ^ (ε + (10 / (1 - cfg.d)) * u) * cfg.N k ^ (-s)

/-- The reference weights of a layer are summable by the datum. -/
theorem LayerDatum.sum_refWeight_le {cfg : Data α} {k : ℕ} {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) [IsFiniteMeasure (cfg.π k)]
    (hN : 0 < cfg.N k) (hχ : 0 ≤ χ) (hD : 0 ≤ D) (h : Fin 3) :
    ∑ i, refWeight L h i ≤ cfg.N k ^ ε := by
  have hc : 0 ≤ χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d := by positivity
  have hfin : ∀ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
      cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hsum := L.sum h
  have : ∑ i, refWeight L h i = (∑ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
      cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    rfl
  rw [this]
  calc _ ≤ (ENNReal.ofReal (cfg.N k ^ ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = cfg.N k ^ ε := ENNReal.toReal_ofReal (by positivity)

theorem mass_alg {P Y Z B : ℝ} (hP : 0 < P) (hY : 16000000 ≤ Y) (hZ : 18 ≤ Z)
    (hB : B ≤ 4000000 * (P / Y)) : 2 * B + P / Z ≤ P := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have h1 : 4000000 * (P / Y) ≤ P / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hY0 (by norm_num)]; nlinarith
  have h2 : P / Z ≤ P / 18 := div_le_div_of_nonneg_left hP.le (by norm_num) hZ
  linarith

/-- Cancel a finite term in an `ENNReal` mass bound. -/
theorem ofReal_le_of_add {x b : ℝ} {m t : ENNReal} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h : ENNReal.ofReal (x + b) ≤ t) (ht : t ≤ m + ENNReal.ofReal b) : ENNReal.ofReal x ≤ m := by
  rw [ENNReal.ofReal_add hx hb] at h
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (h.trans ht)

/-- **The full-strip comparison.** -/
theorem projected_agree (hM : MatchHyp) (cfg : Data α) (hv : cfg.Valid) (hp : cfg.Projected)
    {buffer : ℝ} (hbuf : 100 < buffer) :
    ∃ s₀ s u v R M : ℝ, Depths cfg buffer s₀ s u v R M ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      AgreeAt cfg k ε R (cfg.N k ^ (-M)) (cfg.N k ^ (-2 * cfg.κ * s₀)) s u
        ![s, s + u, s + v] := by
  obtain ⟨s₀, s, u, v, R, M, hdep, hL⟩ := projected_unpack hp hbuf
  obtain ⟨η, hη, R₀, hR₀, LB⟩ :=
    layer_bad_le (α := α) hM hv.dimension_nonneg hv.dimension_lt_one
  refine ⟨s₀, s, u, v, R, M, hdep, fun ε hε => ?_⟩
  have hd1 := hv.dimension_lt_one
  have hNt := hv.resolution_tendsto
  have hCd : 0 < 10 / (1 - cfg.d) := div_pos (by norm_num) (by linarith)
  have hu := hdep.u_pos
  have hs₀ := hdep.s₀_pos
  have hs : 0 < s := by linarith [hdep.s₀_lt]
  have hbs : 0 < buffer * s₀ := by positivity
  have hM0 : 0 < M := by linarith [hdep.M_gt]
  have hCuη : 0 < (10 / (1 - cfg.d)) * u * η := by positivity
  set τ : ℝ := min (min (ε / 2) ((10 / (1 - cfg.d)) * u * η / 20)) (min (1 / 2) (s / 2)) with hτdef
  have hτ : 0 < τ := by
    simp only [hτdef, lt_min_iff]; refine ⟨⟨by linarith, by linarith⟩, by norm_num, by linarith⟩
  have hτε : τ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hτη : 20 * τ ≤ (10 / (1 - cfg.d)) * u * η := by
    have h1 : τ ≤ min (ε / 2) ((10 / (1 - cfg.d)) * u * η / 20) := min_le_left _ _
    have h2 : min (ε / 2) ((10 / (1 - cfg.d)) * u * η / 20) ≤ (10 / (1 - cfg.d)) * u * η / 20 :=
      min_le_right _ _
    linarith
  have hτ1 : τ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτs : τ ≤ s / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set Rcap : ℝ := M + 3 + s + u + 1 / M with hRcap
  have hRc1 : 1 < Rcap := by have : 0 < 1 / M := by positivity
                             linarith
  have hRcM : Rcap⁻¹ ≤ M := by
    rw [inv_le_comm₀ (by linarith) hM0]
    have : 1 / M ≤ Rcap := by rw [hRcap]; linarith
    simpa [one_div] using this
  filter_upwards [hL τ hτ, index_facts cfg hv, jointCapAt_eventually cfg hv hRc1,
    compare_numerics_eventually (R₀ := R₀) cfg hv hbuf hdep hτ hτη hη 0,
    compare_numerics_eventually (R₀ := R₀) cfg hv hbuf hdep hτ hτη hη 1,
    compare_numerics_eventually (R₀ := R₀) cfg hv hbuf hdep hτ hτη hη 2,
    eventually_const_le_rpow hNt (c := ε - τ) (by linarith) 18,
    eventually_const_le_rpow hNt (c := (10 / (1 - cfg.d)) * u * η - 6 * τ) (by linarith)
      16000000,
    hv.loss_subpower τ hτ] with k hLk hfacts hcap hn0 hn1 hn2 h18 hbig hK
  obtain ⟨L⟩ := hLk
  obtain ⟨hb, hρμ, hμfin, hπfin, hhor, hgood⟩ := hfacts
  set N := cfg.N k with hNdef
  have hN1 : 1 < N := hn0.N_gt
  have hN0 : 0 < N := by linarith
  have hrp : ∀ x : ℝ, 0 < N ^ x := fun x => Real.rpow_pos_of_pos hN0 x
  have hsplit : ∀ x y : ℝ, N ^ (x + y) = N ^ x * N ^ y := fun x y => Real.rpow_add hN0 x y
  have hK1 := hn0.K_one
  -- the caps at the needed resolutions
  have hrr : Rcap⁻¹ ≤ M + 2 * τ := hRcM.trans (by linarith)
  have hrR : M + 2 * τ ≤ Rcap := by
    have : 0 < 1 / M := by positivity
    rw [hRcap]; linarith [hτ1]
  have hMinv : 0 < 1 / M := by positivity
  have hMR : M ≤ Rcap := by rw [hRcap]; linarith
  have hsR : s + u ≤ Rcap := by rw [hRcap]; linarith
  have hcaps : ∀ s' : ℝ, 0 ≤ s' → s' ≤ (![s, s + u, s + v] : Fin 3 → ℝ) 0 →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) N (cfg.K k) cfg.d (M + 2 * τ) s' M := by
    intro s' h0 h1
    have h1' : s' ≤ s := h1
    exact hcap _ _ _ hrr hrR h0 (by linarith) hRcM hMR
  have hcapd : ∀ h : Fin 3, JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) N (cfg.K k) cfg.d (M + 2 * τ)
      ((![s, s + u, s + v] : Fin 3 → ℝ) h - τ) M := by
    intro h
    obtain ⟨hh0, hh1⟩ := depth_sub_mem (s := s) hu hdep.v_pos hdep.v_lt_u h
    exact hcap _ _ _ hrr hrR (by linarith) (by linarith) hRcM hMR
  -- bad masses of layers 1 and 2
  set Nm : ℝ := N ^ ((10 / (1 - cfg.d)) * u) with hNm
  set Mst : ℝ := 3 * N ^ τ * Nm with hMst
  have hbad : ∀ h : Fin 3, CompareNumerics N (cfg.K k) cfg.d τ (N ^ (-M)) (N ^ (-2 * cfg.κ * s₀))
      (N ^ (-cfg.e₀)) (M + 2 * τ) (N ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) 0)))
      (N ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) h))) Nm R₀ η →
      L.ρs (L.badSet h Mst) ≤ ENNReal.ofReal (1000000 * cfg.K k * (cfg.K k + 1) * N ^ (2 * τ) *
        Nm ^ (-η) * (∑ i, refWeight L 0 i + ∑ j, refWeight L h j)) := by
    intro h hnh
    exact (L.badSet_le h Mst).trans (LB cfg k τ R _ _ _ L h (N ^ (-cfg.e₀)) (M + 2 * τ) M Nm rfl
      hb hρμ hμfin hπfin hgood hhor rfl hcaps (hcapd 0) (hcapd h) hn0 hnh)
  have hχ0 : 0 ≤ N ^ (-M) := (hrp _).le
  have hD0 : 0 ≤ N ^ (-2 * cfg.κ * s₀) := (hrp _).le
  have hT : ∀ h : Fin 3, ∑ i, refWeight L h i ≤ N ^ τ := fun h => L.sum_refWeight_le hN0 hχ0 hD0 h
  -- the numerics of the mass
  set P : ℝ := N ^ (-τ) with hP
  set Y : ℝ := N ^ ((10 / (1 - cfg.d)) * u * η - 6 * τ) with hY
  set Z : ℝ := N ^ (ε - τ) with hZ
  set B : ℝ := 1000000 * cfg.K k * (cfg.K k + 1) * N ^ (2 * τ) * Nm ^ (-η) * (2 * N ^ τ) with hB
  have hNmη : Nm ^ (-η) = N ^ (-((10 / (1 - cfg.d)) * u * η)) := by
    rw [hNm, ← Real.rpow_mul hN0.le]; ring_nf
  have hBbound : B ≤ 4000000 * (P / Y) := by
    have hPY : P / Y = N ^ (5 * τ) * N ^ (-((10 / (1 - cfg.d)) * u * η)) := by
      rw [hP, hY, ← Real.rpow_sub hN0, ← hsplit]; ring_nf
    rw [hPY, hB, hNmη]
    have hKτ : cfg.K k ≤ N ^ τ := hK
    have hK0 : 0 ≤ cfg.K k := by linarith
    have hKK : cfg.K k * (cfg.K k + 1) ≤ 2 * (N ^ τ * N ^ τ) := by nlinarith
    have h5 : N ^ (5 * τ) = (N ^ τ * N ^ τ) * N ^ (2 * τ) * N ^ τ := by
      rw [show 5 * τ = (τ + τ) + 2 * τ + τ by ring, hsplit, hsplit, hsplit]
    rw [h5]
    have hE : 0 ≤ N ^ (-((10 / (1 - cfg.d)) * u * η)) := (hrp _).le
    have h2τ : 0 ≤ N ^ (2 * τ) := (hrp _).le
    have hτ0 : 0 ≤ N ^ τ := (hrp _).le
    calc 1000000 * cfg.K k * (cfg.K k + 1) * N ^ (2 * τ) * N ^ (-((10 / (1 - cfg.d)) * u * η)) *
          (2 * N ^ τ)
        = 1000000 * (cfg.K k * (cfg.K k + 1)) * N ^ (2 * τ) *
            N ^ (-((10 / (1 - cfg.d)) * u * η)) * (2 * N ^ τ) := by ring
      _ ≤ 1000000 * (2 * (N ^ τ * N ^ τ)) * N ^ (2 * τ) *
            N ^ (-((10 / (1 - cfg.d)) * u * η)) * (2 * N ^ τ) := by gcongr
      _ = 4000000 * ((N ^ τ * N ^ τ) * N ^ (2 * τ) * N ^ τ *
            N ^ (-((10 / (1 - cfg.d)) * u * η))) := by ring
  have hεPZ : N ^ (-ε) = P / Z := by
    rw [hP, hZ, ← Real.rpow_sub hN0]; ring_nf
  have hmassR : 2 * B + N ^ (-ε) ≤ P := by
    rw [hεPZ]; exact mass_alg (hrp _) hbig h18 hBbound
  -- the good part of the dense measure
  set S : Set (α × ℝ) := (L.badSet 1 Mst ∪ L.badSet 2 Mst)ᶜ with hSdef
  have hSm : MeasurableSet S := ((L.measurableSet_badSet 1 Mst).union (L.measurableSet_badSet 2 Mst)).compl
  have hB0 : 0 ≤ B := by
    rw [hB]; have : 0 ≤ Nm ^ (-η) := Real.rpow_nonneg (hrp _).le _
    have := hrp τ; have := hrp (2 * τ)
    have hK0 : 0 ≤ cfg.K k := by linarith
    positivity
  have hbad12 : L.ρs Sᶜ ≤ ENNReal.ofReal (2 * B) := by
    rw [hSdef, compl_compl]
    have hbB : ∀ h : Fin 3, CompareNumerics N (cfg.K k) cfg.d τ (N ^ (-M)) (N ^ (-2 * cfg.κ * s₀))
        (N ^ (-cfg.e₀)) (M + 2 * τ) (N ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) 0)))
        (N ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) h))) Nm R₀ η → L.ρs (L.badSet h Mst) ≤ ENNReal.ofReal B := by
      intro h hnh
      refine (hbad h hnh).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hB]
      have hpos : 0 ≤ 1000000 * cfg.K k * (cfg.K k + 1) * N ^ (2 * τ) * Nm ^ (-η) := by
        have : 0 ≤ Nm ^ (-η) := Real.rpow_nonneg (hrp _).le _
        have := hrp (2 * τ)
        have hK0 : 0 ≤ cfg.K k := by linarith
        positivity
      apply mul_le_mul_of_nonneg_left _ hpos
      linarith [hT 0, hT h]
    calc L.ρs (L.badSet 1 Mst ∪ L.badSet 2 Mst) ≤ L.ρs (L.badSet 1 Mst) + L.ρs (L.badSet 2 Mst) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add (hbB 1 hn1) (hbB 2 hn2)
      _ = ENNReal.ofReal (2 * B) := by rw [← ENNReal.ofReal_add hB0 hB0]; ring_nf
  have hmassS : ENNReal.ofReal (N ^ (-ε)) ≤ L.ρs S := by
    apply ofReal_le_of_add (b := 2 * B) (hrp _).le (by linarith) (t := L.ρs univ)
    · refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) L.mass
    · calc L.ρs univ ≤ L.ρs S + L.ρs Sᶜ := by
            rw [← measure_union disjoint_compl_right hSm.compl, union_compl_self]
        _ ≤ L.ρs S + ENNReal.ofReal (2 * B) := add_le_add le_rfl hbad12
  -- restrict and conclude
  refine ⟨L.restrictTo (by linarith [hτε]) hN1.le hχ0 hD0 S hmassS, ?_⟩
  have hae : ∀ᵐ p ∂(L.ρs.restrict S), p ∈ S := ae_restrict_mem hSm
  show ∀ᵐ p ∂(L.ρs.restrict S), _
  filter_upwards [hae] with p hp h hh i₀ ih h0 hh' t ht w hw
  have hag := L.agree_off_bad (hrp _) (hrp _) (Mst := Mst) hp h hh i₀ ih h0 hh' t ht w hw
  refine hag.trans ?_
  have hd0 : (![s, s + u, s + v] : Fin 3 → ℝ) 0 = s := rfl
  rw [hd0]
  have hexp : N ^ (ε + (10 / (1 - cfg.d)) * u) = Z * N ^ τ * Nm := by
    rw [hZ, hNm, ← hsplit, ← hsplit]; ring_nf
  rw [hexp, hMst]
  have hNs : 0 ≤ N ^ (-s) := (hrp _).le
  have hτ0 : 0 ≤ N ^ τ := (hrp _).le
  have hNm0 : 0 ≤ Nm := (hrp _).le
  have : 6 * (3 * N ^ τ * Nm) ≤ Z * N ^ τ * Nm := by
    have h' : 18 * (N ^ τ * Nm) ≤ Z * (N ^ τ * Nm) :=
      mul_le_mul_of_nonneg_right h18 (mul_nonneg hτ0 hNm0)
    linarith
  calc N ^ (-s) * (6 * (3 * N ^ τ * Nm)) ≤ N ^ (-s) * (Z * N ^ τ * Nm) :=
        mul_le_mul_of_nonneg_left this hNs
    _ = Z * N ^ τ * Nm * N ^ (-s) := by ring

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
