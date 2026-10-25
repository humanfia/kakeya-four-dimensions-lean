import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport
import Submission.Obl.k4_finite_width_output_exclusion.Horizon

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

def Data.rebase (p : Data) : Data :=
  { p with
    N := fun k => p.N k ^ p.L
    L := 1
    f := fun r => p.f (p.L * r) / p.L
    g := fun k γ r => p.g k γ (p.L * r)
    G := fun k γ u => p.G k γ (p.L * u) }

lemma delta_rebase {N : ℝ} (hN : 0 < N) (L r : ℝ) :
    δ (N ^ L) r = δ N (L * r) := by
  unfold δ
  rw [Real.log_rpow hN]
  congr 3
  ring

lemma rebase_power {N L : ℝ} (hN : 0 < N) (hL : 0 < L) (a : ℝ) :
    (N ^ L) ^ (a / L) = N ^ a := by
  rw [← Real.rpow_mul hN.le]
  congr 1
  field_simp

lemma polynomial_rebase {N L : ℝ} {M M' : ℕ} (hN : 1 ≤ N) (hL : 0 < L)
    (hM : (M : ℝ) / L ≤ (M' : ℝ)) : N ^ M ≤ (N ^ L) ^ M' := by
  rw [← Real.rpow_natCast N M, ← Real.rpow_natCast (N ^ L) M',
    ← Real.rpow_mul (by linarith : 0 ≤ N)]
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact (div_le_iff₀ hL).1 hM |>.trans_eq (mul_comm _ _)

lemma valid_rebase {p : Data} (hp : Valid p)
    (hN : ∀ k, 2 ≤ p.N k ^ p.L) : Valid p.rebase := by
  rcases hp with ⟨hN₀, ht, hK, hL, hd, hd1, hS, hη,
    ⟨M, D, hfmt⟩, hg, hG, hLip, htyp, hcap, hang⟩
  obtain ⟨M', hM'⟩ := exists_nat_ge ((M : ℝ) / p.L)
  have hNpos (k : ℕ) : 0 < p.N k := by linarith [hN₀ k]
  have hpoly (k : ℕ) : p.N k ^ M ≤ (p.N k ^ p.L) ^ M' :=
    polynomial_rebase (by linarith [hN₀ k]) hL hM'
  refine ⟨hN, (tendsto_rpow_atTop hL).comp ht,
    ⟨hK.1, ?_⟩, by norm_num [Data.rebase], hd, hd1, hS, hη,
    ⟨M', D, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    filter_upwards [hK.2 (p.L * ε) (mul_pos hL hε)] with k hk
    simpa only [Data.rebase, ← Real.rpow_mul (hNpos k).le] using hk
  · intro k
    rcases hfmt k with ⟨hW, hω, hsum, hw, hm⟩
    refine ⟨hW.trans (hpoly k), hω, hsum, ?_, hm⟩
    intro γ
    rcases hw γ with ⟨hν, hBpos, hB, hBi, hPdeg, hPcoef,
      ⟨m, hm, c, i, A, hA, hνeq⟩, hE, hEsub, hEbd, hEfmt, haet, haep⟩
    refine ⟨hν, hBpos, hB.trans (hpoly k), hBi.trans (hpoly k), hPdeg,
      fun b => (hPcoef b).trans (hpoly k),
      ⟨m, hm.trans (hpoly k), c, i, A, ?_, hνeq⟩, hE, hEsub, ?_, ?_, haet, haep⟩
    · intro j
      exact ⟨(hA j).1, (hA j).2.1.trans (hpoly k), (hA j).2.2.1.trans (hpoly k),
        fmt_mono (hpoly k) (hA j).2.2.2.1,
        fun a ha b => ((hA j).2.2.2.2 a ha b).trans (hpoly k)⟩
    · intro z hz
      exact ⟨(hEbd z hz).1.trans (hpoly k),
        fun b => ((hEbd z hz).2 b).trans (hpoly k)⟩
    · exact fun i => fmt_mono (hpoly k) (hEfmt i)
  · intro k γ r hr hr1
    change r ≤ 1 at hr1
    simpa only [Data.rebase, delta_rebase (hNpos k)] using
      hg k γ (p.L * r) (mul_nonneg hL.le hr) (by nlinarith)
  · intro k γ u hu huη
    change u ≤ p.η * 1 at huη
    rw [mul_one] at huη
    simpa only [Data.rebase, mul_one, delta_rebase (hNpos k)] using
      hG k γ (p.L * u) (mul_pos hL hu) (by nlinarith)
  · intro r s hr hrs hs1
    change s ≤ 1 at hs1
    obtain ⟨h0, h1⟩ := hLip (p.L * r) (p.L * s) (mul_nonneg hL.le hr)
      (mul_le_mul_of_nonneg_left hrs hL.le) (by nlinarith)
    change 0 ≤ p.f (p.L * s) / p.L - p.f (p.L * r) / p.L ∧
      p.f (p.L * s) / p.L - p.f (p.L * r) / p.L ≤ s - r
    rw [← sub_div]
    exact ⟨div_nonneg h0 hL.le, (div_le_iff₀ hL).2 (by nlinarith)⟩
  · intro r τ hr hr1 hτ
    change r ≤ 1 at hr1
    obtain ⟨c, hc, h⟩ := htyp (p.L * r) (p.L * τ)
      (mul_nonneg hL.le hr) (by nlinarith) (mul_pos hL hτ)
    refine ⟨c / p.L, div_pos hc hL, ?_⟩
    have hlo (k : ℕ) :
        (p.N k ^ p.L) ^ (-(p.f (p.L * r) / p.L) - τ) =
          p.N k ^ (-p.f (p.L * r) - p.L * τ) := by
      rw [← Real.rpow_mul (hNpos k).le]
      congr 1
      field_simp
    have hhi (k : ℕ) :
        (p.N k ^ p.L) ^ (-(p.f (p.L * r) / p.L) + τ) =
          p.N k ^ (-p.f (p.L * r) + p.L * τ) := by
      rw [← Real.rpow_mul (hNpos k).le]
      congr 1
      field_simp
    have hc' (k : ℕ) : (p.N k ^ p.L) ^ (-(c / p.L)) = p.N k ^ (-c) := by
      rw [show -(c / p.L) = (-c) / p.L by ring, rebase_power (hNpos k) hL]
    filter_upwards [h] with k hk
    simp only [Data.rebase, delta_rebase (hNpos k), hlo k, hhi k, hc' k]
    convert hk using 1 <;> congr 3
  · intro r hr hr1
    change r ≤ 1 at hr1
    have h := hcap (p.L * r) (mul_nonneg hL.le hr) (by nlinarith)
    change p.f (p.L * 1) / p.L - p.f (p.L * r) / p.L ≤ p.d * (1 - r)
    rw [mul_one, ← sub_div, div_le_iff₀ hL]
    nlinarith
  · intro u τ hu huη hτ
    change u ≤ p.η * 1 at huη
    rw [mul_one] at huη
    obtain ⟨c, hc, h⟩ := hang (p.L * u) (p.L * τ)
      (mul_pos hL hu) (by nlinarith) (mul_pos hL hτ)
    refine ⟨c / p.L, div_pos hc hL, ?_⟩
    have hpow (k : ℕ) :
        (p.N k ^ p.L) ^ (-(p.f p.L / p.L) - p.S * u + τ) =
          p.N k ^ (-p.f p.L - p.S * (p.L * u) + p.L * τ) := by
      rw [← Real.rpow_mul (hNpos k).le]
      congr 1
      field_simp
    have hc' (k : ℕ) : (p.N k ^ p.L) ^ (-(c / p.L)) = p.N k ^ (-c) := by
      rw [show -(c / p.L) = (-c) / p.L by ring, rebase_power (hNpos k) hL]
    filter_upwards [h] with k hk
    simp only [Data.rebase, mul_one, delta_rebase (hNpos k), hpow k, hc' k]
    convert hk using 1 <;> congr 3

end
end Submission.Obl.k4_finite_width_output_exclusion
