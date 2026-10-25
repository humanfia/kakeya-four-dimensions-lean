import Submission.Obl.k4_extremal_profile_setup.Geometry
import Submission.Obl.k4_extremal_profile_setup.TimeExtraction

namespace Submission.Obl.k4_extremal_profile_setup

theorem twoSidedExtraction : TwoSidedExtraction := by
  intro p hp z hz
  obtain ⟨h, hHh, hhz, M, D, hb⟩ := hz.exists_timeBanded_above_horizon hp
  refine ⟨h, hHh, hhz, M, D, fun ε hε => (hb ε hε).mono fun k hk => ?_⟩
  obtain ⟨a, hκ, _, hε, hlo, hhi, hC, hsep, hchart, hmass⟩ := hk
  exact ⟨a.κ, hκ, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
    hlo, hhi, hC, hsep, hchart, hmass⟩

theorem Data.Valid.S_pos {p : Data} (hp : p.Valid) : 0 < p.S := hp.2.2.2.2.2.2.1
theorem Data.Valid.eta_pos {p : Data} (hp : p.Valid) : 0 < p.η := hp.2.2.2.2.2.2.2.1

theorem amplification_of_transfers (hi : InitialHorizon) (ht : TerminalExtension)
    (hx : TwoSidedExtraction) (hr : RemainderTransfer)
    {S η : ℝ} (hS : 0 < S) (hη : 0 < η) : (rateFamily hi S η).Amplifies := by
  intro d₀ hd₀
  obtain ⟨Cx, cx, hCx, hcx, hte⟩ := ht d₀ S η hd₀ hS hη
  let c : ℝ := 3 / (4 * Cx)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro p hpd hpr
  have hp := p.2.1
  have hH : 0 < horizon p.1 := by
    change 0 < horizon p.1 / p.1.L at hpr
    have := (lt_div_iff₀ hp.L_pos).mp hpr
    simpa only [zero_mul] using this
  obtain ⟨e, he, hemax⟩ := exists_between (lt_min hH (mul_pos hcx hp.L_pos))
  have heH := hemax.trans_le (min_le_left _ _)
  have heL := hemax.trans_le (min_le_right _ _)
  have hz : Terminal p.1 (horizon p.1 + e / 8) :=
    terminal_of_horizon_lt hi hp (by linarith)
  obtain ⟨h, hHh, hhz, hex⟩ := hx p.1 hp _ hz
  obtain ⟨r, hr0, hrL, hlen, hk⟩ :=
    hte p.1 hp p.2.2.1 p.2.2.2 hpd h e he (heH.trans_le hHh) heL hex
  obtain ⟨F, hF, hFL, hFd, hFS, hFη, hcost⟩ :=
    hr p.1 hp r (h - e) p.1.d hr0.le hrL hp.d_pos hp.d_lt_one
      (fun s hrs hsL => hp.cap s (hr0.le.trans hrs) hsL) hk
  let q : ValidData S η := ⟨F, hF, hFS.trans p.2.2.1, hFη.trans p.2.2.2⟩
  refine ⟨q, hFd.le, ?_⟩
  change c ≤ horizon F / F.L
  apply (le_div_iff₀ hF.L_pos).mpr
  have hFL' : F.L ≤ Cx * e := by simpa only [hFL] using hlen
  have hmul := mul_le_mul_of_nonneg_left hFL' hc.le
  have hcCx : c * Cx = 3 / 4 := by
    dsimp [c]
    field_simp
  nlinarith

/-- Extension inside a single cropped problem localizes any positive horizon
into its final interval, where only the local cap is needed. -/
theorem horizon_zero_of_local_cap (hi : InitialHorizon) (ht : TerminalExtension)
    (hx : TwoSidedExtraction) (hr : RemainderTransfer)
    {p : Data} (hp : p.Valid) {a q : ℝ} (ha : a < p.L)
    (hq : 0 < q) (hq1 : q < 1)
    (hcap : ∀ s : ℝ, a ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ q * (p.L - s))
    (hzero : ∀ F : Data, F.Valid → F.S = p.S → F.η = p.η → F.d ≤ q →
      horizon F = 0) : horizon p = 0 := by
  apply le_antisymm _ (horizon_nonneg hi hp)
  by_contra hn
  have hH : 0 < horizon p := lt_of_not_ge hn
  obtain ⟨Cx, cx, hCx, hcx, hte⟩ :=
    ht p.d p.S p.η hp.d_lt_one hp.S_pos hp.eta_pos
  have hemax : 0 < min (horizon p) (min (cx * p.L) ((p.L - a) / Cx)) :=
    lt_min hH (lt_min (mul_pos hcx hp.L_pos) (div_pos (sub_pos.mpr ha) hCx))
  obtain ⟨e, he, hem⟩ := exists_between hemax
  have heH := hem.trans_le (min_le_left _ _)
  have heL := hem.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hea := hem.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hz : Terminal p (horizon p + e / 8) := terminal_of_horizon_lt hi hp (by linarith)
  obtain ⟨h, hHh, hhz, hex⟩ := hx p hp _ hz
  obtain ⟨t, ht0, htL, hlen, hk⟩ :=
    hte p hp rfl rfl le_rfl h e he (heH.trans_le hHh) heL hex
  have hta : a < t := by
    have hea' := (lt_div_iff₀ hCx).mp hea
    nlinarith
  obtain ⟨F, hF, _, hFd, hFS, hFη, hcost⟩ :=
    hr p hp t (h - e) q ht0.le htL hq hq1
      (fun s hts hsL => hcap s (hta.le.trans hts) hsL) hk
  have hFzero := hzero F hF hFS hFη hFd.le
  linarith

/-- A minimum of the tilted profile records a quantitative secant deficit. -/
theorem quantitative_tilted_endpoint {f : ℝ → ℝ} {L a b q : ℝ}
    (hf : ProfileIncrement f L) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ L)
    (hsec : f b - f a < q * (b - a)) :
    ∃ r : ℝ, a < r ∧ r ≤ b ∧ q * (b - a) - (f b - f a) ≤ q * (r - a) ∧
      ∀ s ∈ Set.Icc a r, f r - f s ≤ q * (r - s) := by
  have hcont : ContinuousOn (fun s => f s - q * s) (Set.Icc a b) :=
    (hf.continuousOn.mono (Set.Icc_subset_Icc ha hb)).sub
      (continuous_const.mul continuous_id).continuousOn
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab.le) hcont
  have hminb := hmin (Set.right_mem_Icc.mpr hab.le)
  have hne : r ≠ a := by
    intro heq
    dsimp at hminb
    rw [heq] at hminb
    nlinarith
  have har : a < r := lt_of_le_of_ne hr.1 hne.symm
  have hinc := (hf a r ha har.le (hr.2.trans hb)).1
  refine ⟨r, har, hr.2, ?_, ?_⟩
  · dsimp at hminb
    linarith
  · intro s hs
    have h := hmin ⟨hs.1, hs.2.trans hr.2⟩
    dsimp at h
    nlinarith

theorem actual_secant_reduction (hi : InitialHorizon) (ht : TerminalExtension)
    (hx : TwoSidedExtraction) (hr : RemainderTransfer) (hc : CoarseningComposition)
    {p : Data} (hp : p.Valid) {a b q U : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ p.L) (hq : 0 < q) (hq1 : q < 1)
    (hsec : p.f b - p.f a < q * (b - a))
    (hzero : ∀ F : Data, F.Valid → F.S = p.S → F.η = p.η → F.d ≤ q → horizon F = 0)
    (hU : 0 ≤ U)
    (hbound : ∀ F : Data, F.Valid → F.S = p.S → F.η = p.η → F.d ≤ p.d →
      horizon F ≤ U * F.L) :
    ∃ r : ℝ, a < r ∧ r ≤ b ∧ q * (b - a) - (p.f b - p.f a) ≤ q * (r - a) ∧
      horizon p ≤ U * (p.L - r) := by
  obtain ⟨r, har, hrb, hdef, hlocal⟩ := quantitative_tilted_endpoint hp.profile ha hab hb hsec
  obtain ⟨D, hqD, hD, hD1, hglobal⟩ :=
    global_terminal_cap_of_local hp.profile ha har (hrb.trans hb) hq.le hq1 hlocal
  obtain ⟨G, hG, hGL, _, hGS, hGη, hGf, hcost⟩ :=
    hc p hp r D U (ha.trans_lt har) (hrb.trans hb) (hq.trans_le hqD) hD1
      (fun s hs hsr => hglobal s ⟨hs, hsr⟩) hU hbound
  have hGzero : horizon G = 0 := by
    apply horizon_zero_of_local_cap hi ht hx hr hG (by simpa only [hGL] using har) hq hq1
    · intro s has hsL
      simpa only [hGL, hGf] using hlocal s ⟨has, by simpa only [hGL] using hsL⟩
    · intro F hF hFS hFη hFd
      exact hzero F hF (hFS.trans hGS) (hFη.trans hGη) hFd
  refine ⟨r, har, hrb, hdef, ?_⟩
  simpa only [hGzero, zero_add] using hcost

theorem secantReduction_of_transfers (hi : InitialHorizon) (ht : TerminalExtension)
    (hx : TwoSidedExtraction) (hr : RemainderTransfer) (hc : CoarseningComposition)
    (S η : ℝ) : (rateFamily hi S η).SecantReduction relativeProfile := by
  intro p a b q ha hab hb hq hq1 hsec hzero U hU hbound
  have hp := p.2.1
  have hL := hp.L_pos
  have ha' : 0 ≤ p.1.L * a := mul_nonneg hL.le ha
  have hab' : p.1.L * a < p.1.L * b := mul_lt_mul_of_pos_left hab hL
  have hb' : p.1.L * b ≤ p.1.L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hL.le
  have hsec' : p.1.f (p.1.L * b) - p.1.f (p.1.L * a) < q * (p.1.L * b - p.1.L * a) := by
    change p.1.f (p.1.L * b) / p.1.L - p.1.f (p.1.L * a) / p.1.L < q * (b - a) at hsec
    rw [← sub_div] at hsec
    have := (div_lt_iff₀ hL).mp hsec
    nlinarith
  have hz : ∀ F : Data, F.Valid → F.S = p.1.S → F.η = p.1.η → F.d ≤ q → horizon F = 0 := by
    intro F hF hFS hFη hFd
    let F' : ValidData S η := ⟨F, hF, hFS.trans p.2.2.1, hFη.trans p.2.2.2⟩
    have h := hzero F' hFd
    change horizon F / F.L = 0 at h
    exact (div_eq_zero_iff.mp h).resolve_right hF.L_pos.ne'
  have hu : ∀ F : Data, F.Valid → F.S = p.1.S → F.η = p.1.η → F.d ≤ p.1.d →
      horizon F ≤ U * F.L := by
    intro F hF hFS hFη hFd
    let F' : ValidData S η := ⟨F, hF, hFS.trans p.2.2.1, hFη.trans p.2.2.2⟩
    exact (div_le_iff₀ hF.L_pos).mp (hbound F' hFd)
  obtain ⟨r, har, hrb, hdef, hcost⟩ :=
    actual_secant_reduction hi ht hx hr hc hp ha' hab' hb' hq hq1 hsec' hz hU hu
  refine ⟨r / p.1.L, (lt_div_iff₀ hL).mpr (by nlinarith),
    (div_le_iff₀ hL).mpr (by nlinarith), ?_, ?_⟩
  · change q * (b - a) - (p.1.f (p.1.L * b) / p.1.L - p.1.f (p.1.L * a) / p.1.L) ≤
      q * (r / p.1.L - a)
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      (q * (b - a) - (p.1.f (p.1.L * b) / p.1.L - p.1.f (p.1.L * a) / p.1.L)) * p.1.L =
          q * (p.1.L * b - p.1.L * a) - (p.1.f (p.1.L * b) - p.1.f (p.1.L * a)) := by
            field_simp
      _ ≤ q * (r - p.1.L * a) := hdef
      _ = q * (r / p.1.L - a) * p.1.L := by field_simp
  · change horizon p.1 / p.1.L ≤ U * (1 - r / p.1.L)
    apply (div_le_iff₀ hL).mpr
    calc
      horizon p.1 ≤ U * (p.1.L - r) := hcost
      _ = U * (1 - r / p.1.L) * p.1.L := by field_simp

end Submission.Obl.k4_extremal_profile_setup
