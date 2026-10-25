import Submission.Obl.k4_raw_critical_segment_forests.RawAppend
import Submission.Obl.k4_raw_critical_segment_forests.ParentAtlas
import Submission.Obl.k4_raw_critical_segment_forests.PreparedInterface
import Submission.Obl.k4_raw_critical_segment_forests.NestedTransfer
import Submission.Obl.k4_finite_width_output_exclusion.RebaseTransfer

set_option maxHeartbeats 2000000

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Extend a prepared prefix through a capped endpoint. All errors in the
near-maximality argument are fixed before any output slack is requested. -/
theorem extend_prepared (hnorm : NestedNormalizationPrepared) (hi : Initial)
    {p : Data} (hp : Valid p) {kr w ε ε₀ q tw b L d : ℝ}
    {m M D : ℕ} {s r : ℕ → ℝ}
    (hm : 0 < m) (hkr : 0 ≤ kr) (hkr1 : kr ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hε₀ : 0 < ε₀) (hε₀ε : ε₀ ≤ ε / 8)
    (hq : 0 < q) (htw : 0 < tw)
    (hLm : L = r m) (hL1 : L ≤ 1) (hLs : L ≤ s m) (hsm : s m ≤ 1)
    (hrp : 0 < r (m - 1)) (hrpL : r (m - 1) < L)
    (hsp : r (m - 1) ≤ s (m - 1)) (hspdist : s (m - 1) - r (m - 1) ≤ ε₀)
    (hb : b + 2 * ε₀ < tw * (L - r (m - 1)))
    (Gv : (k : ℕ) → Fin (p.W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal)
    (hG : Valid {p with L := L, d := d, G := Gv})
    (hH : kr * L - b < Horizon {p with L := L, d := d, G := Gv})
    (hHlo : kr * s m - ε < Horizon {p with L := L, d := d, G := Gv})
    (hwidth : ∀ u : Data, Valid u → u.L = 1 → u.d = d → u.S = p.S → u.η = p.η →
      kr - tw < Horizon u → Narrow u (kr + ε / 8) w)
    (φ : ℕ → ℕ) (a : (n : ℕ) → Forest p (φ n))
    (width : (n : ℕ) → Fin (a n).C → ℝ)
    (lst : (n : ℕ) → ℕ → Fin (p.W (φ n)) → Observation → Finset (Fin (a n).C))
    (hφ : StrictMono φ)
    (ha : ∀ n, (a n).RawData (width n) kr w ε₀ q (1 / ((n : ℝ) + 1)) m s r M D)
    (hprep : ∀ n, (a n).Prepared r (lst n)) :
    ∃ M' D' : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
      RawAt p kr w ε q σ (m + 1) s r M' D' k := by
  classical
  let G : Data := {p with L := L, d := d, G := Gv}
  let rp := r (m - 1)
  let par : (n : ℕ) → Atlas G (φ n) := fun n =>
    toEndpoint ((a n).layerAtlas (m - 1) ((ha n).2.1.j_lt · ·) (lst n)) L d Gv
  have hpar : ∀ n : ℕ, PreparedParent G M D rp (1 / ((n : ℝ) + 1)) (a n).κ (par n) := by
    intro n
    have hcore := (ha n).2.1
    have htrue := (a n).layer_trueDepth hcore (by omega : m - 1 < m) (lst n)
    have hprepared := (a n).layer_prepared (lst n) (hprep n) (m - 1) (hcore.j_lt · ·)
    refine ⟨hcore.1, hcore.2.1, (ha n).1, (ha n).2.2.1 (m - 1) (by omega) |>.2.2,
      ⟨htrue.1, htrue.2.1, ?_, htrue.2.2.2⟩, hprepared.1⟩
    intro z
    apply k4_coarsened_outer_horizon_composition.chart_extra_mono (hc := htrue.2.2.1 z)
    exact fun hfloor => ⟨hfloor, hprepared.2 z⟩
  obtain ⟨rem, ψ, hrem, hremL, hremd, hremS, hremη, hψ, hN, hlift⟩ :=
    hnorm G hG rp hrp.le hrpL M D φ (fun n => 1 / ((n : ℝ) + 1))
      (fun n => (a n).κ) par hφ (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat hpar
  let χ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  have hl : AtlasLift G rem χ (fun n => par (ψ n)) := hlift
  have hparentT : ∀ n, (2 : ℝ) ^ (par (ψ n)).T ≤ G.N (χ n) ^ (kr * s (m - 1) + ε₀) :=
    fun n => (ha (ψ n)).2.2.1 (m - 1) (by omega) |>.2.1
  have hcomp := hl.horizon hi hG hrem hχ.tendsto_atTop hN hparentT
  have hdist : kr * (s (m - 1) - rp) ≤ ε₀ :=
    (mul_le_of_le_one_left (by dsimp [rp]; linarith) hkr1).trans hspdist
  have hremnear : (kr - tw) * rem.L < Horizon rem := by
    rw [hremL]
    change (kr - tw) * (L - rp) < Horizon rem
    change kr * L - b < Horizon G at hH
    nlinarith
  obtain ⟨u, hu, huL, hud, huS, huη, hunit, hunitN⟩ := unit_normalization hi hrem
  have hunear : kr - tw < Horizon u := by
    have hs : rem.L * (kr - tw) < rem.L * Horizon u := by nlinarith
    exact (mul_lt_mul_iff_right₀ hrem.length_pos).mp hs
  have hnu := hwidth u hu huL (hud.trans hremd)
    (huS.trans hremS) (huη.trans hremη) hunear
  have hnr := hunitN (kr + ε / 8) w hnu
  obtain ⟨Mc, Dc, hchild⟩ := (narrow_iff rem _ _).mp hnr
  obtain ⟨Ml, Dl, hlifts⟩ := hl Mc Dc
  let Mf := 2 * (M + Ml + 3)
  let Df := max D Dl
  have hMMf : M ≤ Mf := by dsimp [Mf]; omega
  have hMlMf : Ml ≤ Mf := by dsimp [Mf]; omega
  have hlogMf : 2 * Ml + 2 ≤ Mf := by dsimp [Mf]; omega
  have hsumMf : max M Ml + 1 ≤ Mf := by dsimp [Mf]; omega
  have h2Mf : (2 : ℝ) ≤ (Mf : ℝ) := by exact_mod_cast
    (show 2 ≤ Mf by dsimp [Mf]; omega)
  obtain ⟨τg, hτg, hguard⟩ := eventually_no_short_true_atlas hG hHlo Ml Dl
  refine ⟨Mf, Df, ?_⟩
  intro σ hσ
  let e := min σ (min τg 1)
  have he : 0 < e := by dsimp [e]; positivity
  have heσ : e ≤ σ := min_le_left _ _
  have heg : e ≤ τg := (min_le_right _ _).trans (min_le_left _ _)
  have he1 : e ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ec, hec, hlate⟩ := hlifts e he
  let τ := min ec (min q (ε / 8))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτc : τ ≤ ec := min_le_left _ _
  have hτq : τ ≤ q := (min_le_right _ _).trans (min_le_left _ _)
  have hτε : τ ≤ ε / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hdiagonal : ∀ᶠ n in atTop, 1 / ((ψ n : ℝ) + 1) ≤ σ := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ.tendsto_atTop
    exact (ht.eventually (eventually_lt_nhds hσ)).mono (fun _ hx => hx.le)
  apply hχ.tendsto_atTop.frequently
  apply ((((hchild τ hτ).and_eventually hlate).and_eventually
    (hχ.tendsto_atTop.eventually hguard)).and_eventually hdiagonal).mono
  rintro n ⟨⟨⟨⟨κc, hκc, hKc, hκcN, child, hTc, hWc, hchildc⟩, hlate⟩, hguard⟩, hdiag⟩
  obtain ⟨κl, c, pmap, cmap, hκl, hKl, hκlN, hTl, hcl, hnest, hprod⟩ :=
    hlate κc child hκc hKc (hκcN.trans
      (Real.rpow_le_rpow_of_exponent_le (hrem.scale_ge_one n) hτc)) hchildc
  have hN1 : 1 < p.N (χ n) := by linarith [hp.scale_ge_two (χ n)]
  have hNpos : 0 < p.N (χ n) := hp.scale_pos (χ n)
  have hκlσ : κl ≤ p.N (χ n) ^ σ := hκlN.trans
    (Real.rpow_le_rpow_of_exponent_le hN1.le heσ)
  have hκaσ : (a (ψ n)).κ ≤ p.N (χ n) ^ σ := (ha (ψ n)).1.trans
    (Real.rpow_le_rpow_of_exponent_le hN1.le hdiag)
  let κ := max (a (ψ n)).κ κl
  have hκσ : κ ≤ p.N (χ n) ^ σ := max_le hκaσ hκlσ
  have hcTrue : TrueDepth (fromEndpoint c) Mf Df κ (r m) := by
    rw [← hLm]
    exact trueDepth_mono hp (by linarith : 0 < κl) (le_max_right _ _)
      hMlMf (le_max_right D Dl) (fromEndpoint_trueDepth hcl)
  have haRaw := (ha (ψ n)).mono hp hMMf (le_max_left D Dl)
    (by linarith : ε₀ ≤ ε) (le_max_left (a (ψ n)).κ κl) hκσ
  let pa : Fin c.C → Fin (a (ψ n)).C := fun z => (a (ψ n)).layerEmb (m - 1) (pmap z)
  have hlev : ∀ z, (a (ψ n)).lev (pa z) = m - 1 :=
    fun z => (a (ψ n)).layerEmb_lev (m - 1) (pmap z)
  have hTupper : (2 : ℝ) ^ c.T ≤ p.N (χ n) ^ (kr * s m + ε) := by
    have hTc' : (2 : ℝ) ^ child.T ≤ p.N (χ n) ^ ((L - rp) * (kr + ε / 8) + τ) := by
      rw [hremL, hN n] at hTc
      exact hTc
    have hsum : kr * s (m - 1) + ε₀ + ((L - rp) * (kr + ε / 8) + τ) ≤ kr * s m + ε := by
      have hnew := mul_le_mul_of_nonneg_left hLs hkr
      have hgap : (L - rp) * (ε / 8) ≤ ε / 8 :=
        mul_le_of_le_one_left (by positivity) (by dsimp [rp]; linarith)
      nlinarith
    rw [hTl, pow_add]
    apply (mul_le_mul (hparentT n) hTc' (by positivity)
      (Real.rpow_nonneg hNpos.le _)).trans
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1.le hsum
  have hTlower : p.N (χ n) ^ (kr * s m - ε) ≤ (2 : ℝ) ^ c.T := by
    exact (hguard κl c hκl hKl (hκlN.trans
      (Real.rpow_le_rpow_of_exponent_le hN1.le heg)) hcl).le
  have hTM : (2 : ℝ) ^ c.T ≤ p.N (χ n) ^ Mf := by
    apply hTupper.trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    have hsm0 : 0 ≤ s m := le_trans (by linarith only [hrp, hrpL] : 0 ≤ L) hLs
    have hmuls : kr * s m ≤ 1 :=
      (mul_le_of_le_one_left hsm0 hkr1).trans hsm
    linarith
  have hex := fun z => chart_log_width hN1 (by linarith : 0 ≤ κl) hκlN he1
    (hcl.2.2.1 z)
  choose v hv using hex
  have hnewwidth : ∀ z, |v z| ≤ (Mf : ℝ) ∧
      p.N (χ n) ^ (-v z) = |Matrix.det (c.Q z)| * (4 : ℝ) ^ c.T ∧
      width (ψ n) (pa z) + w * (r m - r ((a (ψ n)).lev (pa z))) - q ≤ v z := by
    intro z
    refine ⟨(hv z).1.trans (by exact_mod_cast hlogMf), (hv z).2, ?_⟩
    have hwp := (ha (ψ n)).2.2.2 (pa z) |>.2.1
    rw [hlev z] at hwp
    have hprod' : |Matrix.det (c.Q z)| * (4 : ℝ) ^ c.T ≤
        p.N (χ n) ^ (-(width (ψ n) (pa z) + (L - rp) * w) + τ) := by
      rw [hprod z]
      change (|Matrix.det ((a (ψ n)).Q (pa z))| * (4 : ℝ) ^ (a (ψ n)).T (m - 1)) *
        (|Matrix.det (child.Q (cmap z))| * (4 : ℝ) ^ child.T) ≤ _
      rw [← hwp]
      rw [show -(width (ψ n) (pa z) + (L - rp) * w) + τ =
        -width (ψ n) (pa z) + (-((L - rp) * w) + τ) by ring, Real.rpow_add hNpos]
      apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
      have hwc := hWc (cmap z)
      rw [hremL, hN n] at hwc
      exact hwc
    have hwlow := width_exponent_lower hN1 (hv z).2 hprod'
    rw [hlev z, ← hLm]
    dsimp [rp] at hwlow
    linarith
  have hC := append_card_bound (hp.scale_ge_two (χ n)) (ha (ψ n)).2.1.2.2.1 hcl.1 hsumMf
  refine ⟨((a (ψ n)).reslack κ).append (fromEndpoint c) m pa,
    Fin.addCases (width (ψ n)) v, ?_⟩
  apply append_rawData pa hm haRaw hcTrue hC
  · intro z
    change (a (ψ n)).lev (pa z) + 1 = m
    rw [hlev z]
    omega
  · intro z
    exact (hnest z).1.symm
  · exact fun z => (hnest z).2.1
  · exact fun z => (hnest z).2.2.1
  · intro z
    change ((a (ψ n)).j (pa z) : ℝ) / (2 : ℝ) ^ (a (ψ n)).T ((a (ψ n)).lev (pa z)) ≤
      ((c.j z : ℕ) : ℝ) / (2 : ℝ) ^ c.T
    rw [hlev z]
    exact (hnest z).2.2.2.1
  · intro z
    change (((c.j z : ℕ) : ℝ) + 1) / (2 : ℝ) ^ c.T ≤
      (((a (ψ n)).j (pa z) : ℝ) + 1) / (2 : ℝ) ^ (a (ψ n)).T ((a (ψ n)).lev (pa z))
    rw [hlev z]
    exact (hnest z).2.2.2.2
  · exact ⟨hTlower, hTupper, hTM⟩
  · exact hnewwidth

end
end Submission.Obl.k4_raw_critical_segment_forests
