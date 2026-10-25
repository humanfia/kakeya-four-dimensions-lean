import Submission.Obl.k4_extremal_profile_setup.Horizon
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_extremal_profile_setup

open Filter MeasureTheory

/-- The genuine dyadic floor is unchanged by the positive-power base change. -/
theorem δ_rebase {N : ℝ} (hN : 0 < N) (a r : ℝ) :
    δ (N ^ a) r = δ N (a * r) := by
  unfold δ
  rw [Real.log_rpow hN]
  congr 3
  ring

theorem rpow_rebase_div {N a : ℝ} (hN : 0 ≤ N) (ha : a ≠ 0) (e t : ℝ) :
    (N ^ a) ^ (e / a + t) = N ^ (e + a * t) := by
  rw [← Real.rpow_mul hN]
  congr 1
  field_simp

/-- Every old polynomial budget is polynomial in the new positive-power base. -/
theorem exists_rebase_budget {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ∃ M' : ℕ, ∀ N : ℝ, 1 ≤ N → N ^ M ≤ (N ^ a) ^ M' := by
  obtain ⟨M', hM⟩ := exists_nat_ge ((M : ℝ) / a)
  refine ⟨M', fun N hN => ?_⟩
  have hexp : (M : ℝ) ≤ a * (M' : ℝ) := by
    have := (div_le_iff₀ ha).mp hM
    nlinarith
  have h := Real.rpow_le_rpow_of_exponent_le hN hexp
  simpa only [Real.rpow_mul (zero_le_one.trans hN), Real.rpow_natCast] using h

/-- Chart geometry depends on the base only through its format budget and width. -/
theorem Chart.change_base {Nk Nk' κ j r r' Bv : ℝ} {M M' D T : ℕ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (hbudget : Nk ^ M ≤ Nk' ^ M') (hwidth : δ Nk r = δ Nk' r')
    (hc : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    Chart Nk' M' D κ T j r' Bv Ev c u Q R A F ex := by
  rcases hc with ⟨hdet, hcu, hQ, hsize, hdeg, hcoeff, hA, hF, hfmt, hline, hsel, hex⟩
  refine ⟨hdet, hcu.trans hbudget, hQ.trans hbudget, hsize, hdeg,
    fun e => (hcoeff e).trans hbudget, hA, hF, ?_, ?_, hsel, hex⟩
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hfmt i).1 hbudget le_rfl,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hfmt i).2 hbudget le_rfl⟩
  · intro l hl
    obtain ⟨hi, hx, ht⟩ := hline l hl
    refine ⟨hi.trans hbudget, fun e => (hx e).trans hbudget, ?_⟩
    simpa only [hwidth] using ht

/-- Express depth in units of `a` and logarithmic exponents in base `N^a`. -/
noncomputable def Data.rebase (p : Data) (a : ℝ) : Data where
  N k := p.N k ^ a
  K := p.K
  L := p.L / a
  d := p.d
  S := p.S
  η := p.η
  W := p.W
  ω := p.ω
  ν := p.ν
  E := p.E
  P := p.P
  B := p.B
  f r := p.f (a * r) / a
  g k γ r := p.g k γ (a * r)
  G k γ u := p.G k γ (a * u)

theorem Data.Valid.rebase {p : Data} (hp : p.Valid) {a : ℝ} (ha : 0 < a)
    (hbase : ∀ k, 2 ≤ p.N k ^ a) : (p.rebase a).Valid := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, htemp, hg, hG, hinc,
    htyp, hcap, hang⟩
  dsimp only [Data.Valid, Data.rebase]
  have hNp (k : ℕ) : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hN k)
  have hcancel : a * (p.L / a) = p.L := by field_simp
  have hm {r : ℝ} (hr : r ≤ p.L / a) : a * r ≤ p.L := by
    have := (le_div_iff₀ ha).mp hr
    nlinarith
  have hmη {u : ℝ} (hu : u ≤ p.η * (p.L / a)) : a * u ≤ p.η * p.L := by
    have h := mul_le_mul_of_nonneg_left hu ha.le
    have heq : a * (p.η * (p.L / a)) = p.η * p.L := by field_simp
    rwa [heq] at h
  refine ⟨hbase, (tendsto_rpow_atTop ha).comp hNt, ⟨hK.1, ?_⟩,
    div_pos hL ha, hd, hd1, hS, hη, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    filter_upwards [hK.2 (a * ε) (mul_pos ha hε)] with k hk
    simpa only [Real.rpow_mul (hNp k).le] using hk
  · obtain ⟨M, D, htemp⟩ := htemp
    obtain ⟨M', hbudget⟩ := exists_rebase_budget ha M
    have hb (k : ℕ) : p.N k ^ M ≤ (p.N k ^ a) ^ M' :=
      hbudget (p.N k) (le_trans (by norm_num) (hN k))
    refine ⟨M', D, fun k => ?_⟩
    obtain ⟨hW, hω, hωsum, hw, hmass⟩ := htemp k
    refine ⟨hW.trans (hb k), hω, hωsum, fun γ => ?_, hmass⟩
    obtain ⟨hprob, hB, hBp, hBi, hdeg, hcoeff, hprior, hE, hEs, hEb, hEf, hae, hsel⟩ := hw γ
    refine ⟨hprob, hB, hBp.trans (hb k), hBi.trans (hb k), hdeg,
      fun b => (hcoeff b).trans (hb k), ?_, hE, hEs, ?_, ?_, hae, hsel⟩
    · obtain ⟨m, hm, c, i, A, hA, hν⟩ := hprior
      refine ⟨m, hm.trans (hb k), c, i, A, fun j => ?_, hν⟩
      obtain ⟨hc0, hcp, hi, hfmt, hx⟩ := hA j
      exact ⟨hc0, hcp.trans (hb k), hi.trans (hb k),
        Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hfmt (hb k) le_rfl,
        fun x hxA b => (hx x hxA b).trans (hb k)⟩
    · intro p hp
      exact ⟨(hEb p hp).1.trans (hb k), fun e => ((hEb p hp).2 e).trans (hb k)⟩
    · intro i
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hEf i) (hb k) le_rfl
  · intro k γ r hr hrL
    simpa only [Data.rebase, δ_rebase (hNp k)] using
      hg k γ (a * r) (mul_nonneg ha.le hr) (hm hrL)
  · intro k γ u hu huL
    simpa only [Data.rebase, δ_rebase (hNp k), hcancel] using
      hG k γ (a * u) (mul_pos ha hu) (hmη huL)
  · intro r s hr hrs hs
    have h := hinc (a * r) (a * s) (mul_nonneg ha.le hr)
      (mul_le_mul_of_nonneg_left hrs ha.le) (hm hs)
    change 0 ≤ p.f (a * s) / a - p.f (a * r) / a ∧
      p.f (a * s) / a - p.f (a * r) / a ≤ s - r
    rw [← sub_div]
    exact ⟨div_nonneg h.1 ha.le, (div_le_iff₀ ha).mpr (by nlinarith [h.2])⟩
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, htail⟩ := htyp (a * r) (a * τ) (mul_nonneg ha.le hr)
      (hm hrL) (mul_pos ha hτ)
    refine ⟨c / a, div_pos hc ha, htail.mono fun k hk => ?_⟩
    have hlo : (p.N k ^ a) ^ (-(p.f (a * r) / a) - τ) =
        p.N k ^ (-p.f (a * r) - a * τ) := by
      rw [← Real.rpow_mul (hNp k).le]
      congr 1
      field_simp
    have hhi : (p.N k ^ a) ^ (-(p.f (a * r) / a) + τ) =
        p.N k ^ (-p.f (a * r) + a * τ) := by
      rw [← Real.rpow_mul (hNp k).le]
      congr 1
      field_simp
    have he : (p.N k ^ a) ^ (-(c / a)) = p.N k ^ (-c) := by
      simpa only [neg_div, add_zero, mul_zero] using
        rpow_rebase_div (hNp k).le ha.ne' (-c) 0
    simpa only [Data.rebase, δ_rebase (hNp k), hlo, hhi, he] using hk
  · intro r hr hrL
    have h := hcap (a * r) (mul_nonneg ha.le hr) (hm hrL)
    change p.f (a * (p.L / a)) / a - p.f (a * r) / a ≤ p.d * (p.L / a - r)
    rw [hcancel, ← sub_div]
    calc
      (p.f p.L - p.f (a * r)) / a ≤ (p.d * (p.L - a * r)) / a :=
        div_le_div_of_nonneg_right h ha.le
      _ = p.d * (p.L / a - r) := by field_simp
  · intro u τ hu huL hτ
    obtain ⟨c, hc, htail⟩ := hang (a * u) (a * τ) (mul_pos ha hu) (hmη huL)
      (mul_pos ha hτ)
    refine ⟨c / a, div_pos hc ha, htail.mono fun k hk => ?_⟩
    have hhi : (p.N k ^ a) ^ (-(p.f p.L / a) - p.S * u + τ) =
        p.N k ^ (-p.f p.L - p.S * (a * u) + a * τ) := by
      rw [← Real.rpow_mul (hNp k).le]
      congr 1
      field_simp
    have he : (p.N k ^ a) ^ (-(c / a)) = p.N k ^ (-c) := by
      simpa only [neg_div, add_zero, mul_zero] using
        rpow_rebase_div (hNp k).le ha.ne' (-c) 0
    simpa only [Data.rebase, δ_rebase (hNp k), hcancel, hhi, he] using hk

/-- Terminal charts in the new base give genuine terminal charts in the old
base.  Their time exponent is multiplied by the fixed change of units. -/
theorem TerminalAt.of_rebase {p : Data} {a : ℝ} (ha : 0 < a) {M M' D k : ℕ}
    {h ε : ℝ} (hN : 0 < p.N k) (hbudget : (p.N k ^ a) ^ M ≤ p.N k ^ M')
    (ht : TerminalAt (p.rebase a) M D h (ε / a) k) :
    TerminalAt p M' D (a * h) ε k := by
  rcases ht with ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, hκ, hK, hε, hT,
    hC, hsep, hcharts, hmass⟩
  have hcancel : a * (p.L / a) = p.L := by field_simp
  have hwidth : δ (p.N k ^ a) (p.L / a) = δ (p.N k) p.L := by
    rw [δ_rebase hN, hcancel]
  have hf : (p.N k ^ a) ^ (-(p.f (a * (p.L / a)) / a)) =
      p.N k ^ (-p.f p.L) := by
    rw [hcancel]
    simpa only [neg_div, add_zero, mul_zero] using
      rpow_rebase_div hN.le ha.ne' (-p.f p.L) 0
  refine ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, hκ, hK, ?_, ?_,
    hC.trans hbudget, hsep, ?_, hmass⟩
  · have he : (p.N k ^ a) ^ (ε / a) = p.N k ^ ε := by
      simpa only [add_zero, mul_zero] using rpow_rebase_div hN.le ha.ne' ε 0
    simpa only [Data.rebase, he] using hε
  · simpa only [Data.rebase, ← Real.rpow_mul hN.le] using hT
  · intro b
    have hc := (hcharts b).change_base hbudget hwidth
    simpa only [Data.rebase, hf] using hc

theorem Terminal.of_rebase {p : Data} (hp : p.Valid) {a : ℝ} (ha : 0 < a)
    {h : ℝ} (ht : Terminal (p.rebase a) h) : Terminal p (a * h) := by
  obtain ⟨M, D, ht⟩ := ht
  obtain ⟨M', hM⟩ := exists_nat_ge (a * (M : ℝ))
  refine ⟨M', D, fun ε hε => (ht (ε / a) (div_pos hε ha)).mono fun k hk => ?_⟩
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.N_ge k)
  have hb : (p.N k ^ a) ^ M ≤ p.N k ^ M' := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (le_trans (by norm_num) (hp.N_ge k)) hM
    simpa only [Real.rpow_mul hN.le, Real.rpow_natCast] using h
  exact hk.of_rebase ha hN hb

/-- The original relative horizon is a lower bound for the new horizon. -/
theorem horizon_div_le_rebase (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {a : ℝ} (ha : 0 < a) (hbase : ∀ k, 2 ≤ p.N k ^ a) :
    horizon p / a ≤ horizon (p.rebase a) := by
  apply le_csInf (terminal_nonempty hi (hp.rebase ha hbase))
  intro h hh
  apply (div_le_iff₀ ha).mpr
  simpa only [mul_comm] using horizon_le hp (hh.of_rebase hp ha)

end Submission.Obl.k4_extremal_profile_setup
