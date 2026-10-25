import Submission.Obl.k4_finite_width_output_exclusion.Rebase

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

def Atlas.unrebase {p : Data} {k : ℕ} (a : Atlas p.rebase k) : Atlas p k where
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F
  lst := a.lst

lemma inverse_polynomial_rebase {N L : ℝ} {M M' : ℕ} (hN : 1 ≤ N)
    (hM : L * (M : ℝ) ≤ (M' : ℝ)) : (N ^ L) ^ M ≤ N ^ M' := by
  rw [← Real.rpow_natCast (N ^ L) M, ← Real.rpow_natCast N M',
    ← Real.rpow_mul (by linarith : 0 ≤ N)]
  exact Real.rpow_le_rpow_of_exponent_le hN hM

lemma Atlas.trueAt_unrebase {p : Data} (hp : Valid p) {k M M' D : ℕ}
    {κ : ℝ} (hκ : 0 < κ) (a : Atlas p.rebase k)
    (hbound : (p.N k ^ p.L) ^ M ≤ p.N k ^ M') (ha : a.TrueAt M D κ) :
    a.unrebase.TrueAt M' D κ := by
  rcases ha with ⟨hC, hd, hchart, hmass⟩
  refine ⟨hC.trans hbound, hd, ?_, hmass⟩
  intro b
  have hδ : δ (p.N k ^ p.L) 1 = δ (p.N k) p.L := by
    simpa only [mul_one] using delta_rebase (hp.scale_pos k) p.L 1
  have hf : (p.N k ^ p.L) ^ (-(p.f p.L / p.L)) = p.N k ^ (-p.f p.L) := by
    rw [show -(p.f p.L / p.L) = (-p.f p.L) / p.L by ring,
      rebase_power (hp.scale_pos k) hp.length_pos]
  apply chart_transport hbound hκ le_rfl (hp.B_pos k (a.γ b)).le
      (by simp only [Data.rebase, hδ]; exact le_rfl) (by simp only [Data.rebase, hδ]; exact le_rfl) ?_ (hchart b)
  intro hex
  simpa only [Data.rebase, Atlas.unrebase, priorMass, mul_one, hf] using hex

lemma cost_of_rebase {p : Data} (hp : Valid p) {h : ℝ}
    (hc : Cost p.rebase h) : Cost p (p.L * h) := by
  rw [cost_iff] at hc ⊢
  obtain ⟨M, D, hc⟩ := hc
  obtain ⟨M', hM'⟩ := exists_nat_ge (p.L * (M : ℝ))
  refine ⟨M', D, fun ε hε => (hc (ε / p.L) (div_pos hε hp.length_pos)).mono ?_⟩
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, ha⟩
  refine ⟨κ, hκ, hKκ, ?_, a.unrebase, ?_, ?_⟩
  · simpa only [Data.rebase, rebase_power (hp.scale_pos k) hp.length_pos] using hκε
  · simpa only [Data.rebase, Atlas.unrebase, ← Real.rpow_mul (hp.scale_pos k).le] using hT
  · exact a.trueAt_unrebase hp (by linarith)
      (inverse_polynomial_rebase (hp.scale_ge_one k) hM') ha

lemma narrow_of_rebase {p : Data} (hp : Valid p) {h w : ℝ}
    (hc : Narrow p.rebase h w) : Narrow p (p.L * h) (p.L * w) := by
  rw [narrow_iff] at hc ⊢
  obtain ⟨M, D, hc⟩ := hc
  obtain ⟨M', hM'⟩ := exists_nat_ge (p.L * (M : ℝ))
  refine ⟨M', D, fun ε hε => (hc (ε / p.L) (div_pos hε hp.length_pos)).mono ?_⟩
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, hw, ha⟩
  have ht : (p.N k ^ p.L) ^ (h + ε / p.L) = p.N k ^ (p.L * h + ε) := by
    rw [← Real.rpow_mul (hp.scale_pos k).le]
    congr 1
    field_simp [ne_of_gt hp.length_pos] <;> ring
  have hwidth : (p.N k ^ p.L) ^ (-w + ε / p.L) = p.N k ^ (-(p.L * w) + ε) := by
    rw [← Real.rpow_mul (hp.scale_pos k).le]
    congr 1
    field_simp [ne_of_gt hp.length_pos] <;> ring
  refine ⟨κ, hκ, hKκ, ?_, a.unrebase, ?_, ?_, ?_⟩
  · simpa only [Data.rebase, rebase_power (hp.scale_pos k) hp.length_pos] using hκε
  · simpa only [Data.rebase, Atlas.unrebase, ht] using hT
  · intro b
    simpa only [Data.rebase, Atlas.unrebase, hwidth] using hw b
  · exact a.trueAt_unrebase hp (by linarith)
      (inverse_polynomial_rebase (hp.scale_ge_one k) hM') ha

lemma unit_normalization (hi : Initial) {p : Data} (hp : Valid p) :
    ∃ q : Data, Valid q ∧ q.L = 1 ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
      Horizon p ≤ p.L * Horizon q ∧
      (∀ h w : ℝ, Narrow q h w → Narrow p (p.L * h) (p.L * w)) := by
  have hlarge : ∀ᶠ k in atTop, 2 ≤ p.N k ^ p.L :=
    ((tendsto_rpow_atTop hp.length_pos).comp hp.scale_tendsto).eventually
      (eventually_ge_atTop 2)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hlarge
  let φ : ℕ → ℕ := fun k => k + k₀
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono (fun k => Nat.le_add_right k k₀) tendsto_id
  have hpr : Valid (p.reindex φ) := valid_reindex hp hφ
  let q := (p.reindex φ).rebase
  have hq : Valid q := valid_rebase hpr (fun k => hk₀ (φ k) (by dsimp [φ]; omega))
  refine ⟨q, hq, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hx := horizon_transfer hi hp hq (a := 0) (b := p.L) hp.length_pos
      (fun h hh => by simpa only [zero_add, Data.reindex] using cost_of_reindex hφ (cost_of_rebase hpr hh))
    simpa only [zero_add] using hx
  · intro h w hn
    exact narrow_of_reindex hφ (narrow_of_rebase hpr hn)

end
end Submission.Obl.k4_finite_width_output_exclusion
