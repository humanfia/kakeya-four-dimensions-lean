import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ChartGraph

/-!
# The frozen direct exit from one quadratic test

Any quadratic test which is small at the improved width along a measurable family of lines
of the old packet, with hidden derivative bounds at the old scale and a regular hidden
derivative on a heavy set of counted incidences, is the direct alternative of `cd`.
The improvement exponent is the gain itself (`ag = gain`).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set MvPolynomial

noncomputable section

/-- The dyadic thickness is at least the real power it rounds. -/
lemma rpow_neg_le_δ {N x : ℝ} (hN : 0 < N) : N ^ (-x) ≤ δ N x := by
  unfold δ
  set y : ℝ := x * Real.log N / Real.log 2 with hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : N ^ (-x) = (2:ℝ) ^ (-y) := by
    rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hy]
    congr 1
    field_simp
  rw [hpow, ← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  push_cast
  linarith [Int.floor_le y]

/-- The dyadic thickness is at most twice the real power it rounds. -/
lemma δ_le_two_rpow_neg {N x : ℝ} (hN : 0 < N) : δ N x ≤ 2 * N ^ (-x) := by
  unfold δ
  set y : ℝ := x * Real.log N / Real.log 2 with hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : N ^ (-x) = (2:ℝ) ^ (-y) := by
    rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hy]
    congr 1
    field_simp
  rw [hpow, ← Real.rpow_intCast]
  have htwo : (2:ℝ) * (2:ℝ) ^ (-y) = (2:ℝ) ^ (1 - y) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one, Real.rpow_neg (by norm_num)]
    field_simp
  rw [htwo]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  push_cast
  linarith [Int.lt_floor_add_one y]

/-- **Direct exit from one quadratic test.** -/
theorem direct_of_quadratic_test {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mc : ℕ} {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    (b : Fin C) (hgain8 : gain ≤ 1 / 8) (hroom : r (lev b) + 2 * gain * L ≤ L)
    (R : Po) (A' : Set Ln) (G' : Set Ev) (V D1 D2 lo : ℝ)
    (hRdeg : R.totalDegree ≤ 2) (hRcoef : ∀ e, |R.coeff e| ≤ Nk ^ Mc)
    (hA'm : MeasurableSet A') (hA' : A' ⊆ A b)
    (hval : ∀ l ∈ A', ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |eval (xp l t) R| ≤ V ∧ |eval (xp l t) (pderiv 3 R)| ≤ D1 ∧
        |eval (xp l t) (pderiv 3 (pderiv 3 R))| ≤ D2)
    (hV : V ≤ Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + gain * L))
    (hD1 : D1 ≤ Nk ^ (ρ * gain * L + ε) * B (γ b))
    (hD2 : D2 ≤ Nk ^ (ρ * gain * L + ε) * B (γ b) ^ 2 / δ Nk (r (lev b) + gain * L))
    (hG' : ∀ p ∈ G', p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)) ∧
      lo ≤ |eval (xp p.1 p.2) (pderiv 3 R)|)
    (hlo : B (γ b) / Nk ^ (ρ * gain * L + ε) ≤ lo)
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * gain + ρ * gain) * L) - ε) / (2:ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) G') :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  refine ⟨b, gain, le_rfl, hgain8, hroom, R, A', hRdeg, hRcoef, hA'm, hA', ?_, ?_⟩
  · intro l hl t ht
    obtain ⟨h0, h1, h2⟩ := hval l hl t ht
    exact ⟨h0.trans hV, h1.trans hD1, h2.trans hD2⟩
  · apply hmass.trans
    apply measure_mono
    intro p hp
    obtain ⟨hpH, hpA, hpt, hpd⟩ := hG' p hp
    exact ⟨hpH, hpA, hpt, hlo.trans hpd⟩

/-- The direct alternative is the first disjunct of the frozen candidate. -/
theorem cd_of_direct {cc J D : ℕ} {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mc : ℕ} {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    (h : direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    cd cc J D Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H :=
  Or.inl h

end

end Submission.Obl.k4_physical_parent_potential_candidates
