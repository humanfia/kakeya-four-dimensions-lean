import Submission.Obl.k4_scalar_normalized_exact_refinement.Asymptotics

/-!
# Relative profiles of a Refinement

`RefData.profile_pair`: for depths `s₁, s₂ ∈ [0, L_q]` with `r + s₂ ≥ b`,
`f_q(s₂) - f_q(s₁) ≤ f_p(r + s₂) - f_p(r + s₁)`.

At one index and one world `i` of `q`, a point outside four power-small exceptional sets has
`N^(-f_q(s₁)-τ) ≤ ρ_q(s₁) ≤ 4 λ_i N^(-f_p(r+s₁)+τ)` and
`λ_i N^(-f_p(r+s₂)-3τ) ≤ ρ_q(s₂) ≤ N^(-f_q(s₂)+τ)`; the world factor `λ_i = J_i / ν(A_i)` cancels.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {p q : Code} {r b h : ℝ}

/-- Two density comparisons with a common factor give an exponent inequality. -/
lemma exponent_combine {N lam u x y w : ℝ} (hN : 1 < N) (_hlam : 0 ≤ lam)
    (h1 : N ^ u ≤ lam * N ^ x) (h2 : lam * N ^ y ≤ N ^ w) : u + y ≤ x + w := by
  have hN0 : 0 < N := by linarith
  have h : N ^ (u + y) ≤ N ^ (x + w) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
    calc N ^ u * N ^ y ≤ lam * N ^ x * N ^ y :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
      _ = N ^ x * (lam * N ^ y) := by ring
      _ ≤ N ^ x * N ^ w := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)
  exact (Real.rpow_le_rpow_left_iff hN).mp h

/-- The shape of the weighted lower tail bound. -/
lemma lower_shape {N e τ c : ℝ} (hN : 1 ≤ N) (he : 0 ≤ e) (P : ℝ≥0∞)
    (hP : P ≤ ENNReal.ofReal (N ^ (-c))) :
    4 * ENNReal.ofReal (N ^ (-τ)) + 2 * ENNReal.ofReal (N ^ e) * ENNReal.ofReal (N ^ (-τ)) +
        2 * P ≤ ENNReal.ofReal (N ^ e) * (8 * ENNReal.ofReal (N ^ (-(min τ c)))) := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 ≤ ENNReal.ofReal (N ^ e) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hN he)
  have hτ : ENNReal.ofReal (N ^ (-τ)) ≤ ENNReal.ofReal (N ^ (-(min τ c))) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (by simp))
  have hc : P ≤ ENNReal.ofReal (N ^ (-(min τ c))) :=
    hP.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (by simp)))
  set m := ENNReal.ofReal (N ^ (-(min τ c)))
  set E := ENNReal.ofReal (N ^ e)
  calc 4 * ENNReal.ofReal (N ^ (-τ)) + 2 * E * ENNReal.ofReal (N ^ (-τ)) + 2 * P
      ≤ 4 * (E * m) + 2 * E * m + 2 * (E * m) := by
        gcongr
        · calc ENNReal.ofReal (N ^ (-τ)) ≤ m := hτ
            _ = 1 * m := (one_mul m).symm
            _ ≤ E * m := by gcongr
        · calc P ≤ m := hc
            _ = 1 * m := (one_mul m).symm
            _ ≤ E * m := by gcongr
    _ = E * (8 * m) := by ring

namespace RefData

variable (R : RefData p q r b h)

include R in
/-- The relative profile comparison between an upper depth `s₁` and a lower depth `s₂`. -/
theorem profile_pair (hp : Spec.Exact p) (hqr : Spec.RawScalar q) (hqp : Spec.PureProfile q)
    (hr : 0 ≤ r) (hLq : q.L = p.L - r) (s₁ s₂ : ℝ) (h₁0 : 0 ≤ s₁) (h₁L : s₁ ≤ q.L)
    (h₂0 : 0 ≤ s₂) (h₂L : s₂ ≤ q.L) (hb₂ : b ≤ r + s₂) :
    q.f s₂ - q.f s₁ ≤ p.f (r + s₂) - p.f (r + s₁) := by
  apply le_of_forall_pos_le_add
  intro η hη
  set τ := η / 7 with hτdef
  have hτ : 0 < τ := by positivity
  have hraw := Exact.raw hp
  have hpp := Exact.pure hp
  have hNq : ∀ k, 2 ≤ q.N k := RawScalar.N_ge hqr
  obtain ⟨c₁, hc₁, hp₁⟩ := PureProfile.typical hpp (r + s₁) τ (by linarith) (by linarith) hτ
  obtain ⟨c₂, hc₂, hp₂⟩ := PureProfile.typical hpp (r + s₂) τ (by linarith) (by linarith) hτ
  -- the four exceptional families
  let X0 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | q.ρ k i s₁ (obs (q.N k) s₁ z) < ENNReal.ofReal (q.N k ^ (-q.f s₁ - τ)) ∨
      ENNReal.ofReal (q.N k ^ (-q.f s₁ + τ)) < q.ρ k i s₁ (obs (q.N k) s₁ z)}
  let X1 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | q.ρ k i s₂ (obs (q.N k) s₂ z) < ENNReal.ofReal (q.N k ^ (-q.f s₂ - τ)) ∨
      ENNReal.ofReal (q.N k ^ (-q.f s₂ + τ)) < q.ρ k i s₂ (obs (q.N k) s₂ z)}
  let X2 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | ENNReal.ofReal (R.lam k i) * (4 * ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + s₁) + τ))) <
      q.ρ k i s₁ (obs (q.N k) s₁ z)}
  let X3 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | q.ρ k i s₂ (obs (q.N k) s₂ z) < ENNReal.ofReal (R.lam k i) *
      (ENNReal.ofReal (q.N k ^ (-τ)) * (ENNReal.ofReal (q.N k ^ (-τ)) *
        ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + s₂) - τ))))}
  have hs0 := PureProfile.typical hqp s₁ τ h₁0 h₁L hτ
  have hs1 := PureProfile.typical hqp s₂ τ h₂0 h₂L hτ
  have hs2 : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X2 k i) ≤ ENNReal.ofReal (q.N k ^ (-c)) := by
    refine ⟨c₁ / 2, by positivity, ?_⟩
    apply powerSmall_of_factor (RawScalar.N_tendsto hqr) (fun k => by linarith [hNq k])
      R.ε_lim 8 (by norm_num) hc₁
    filter_upwards [R.along hp₁] with k hk
    calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X2 k i)
        ≤ ENNReal.ofReal (R.Z k)⁻¹ * (8 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
          p.mu (R.φ k) a {z | ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + s₁) + τ)) <
            p.ρ (R.φ k) a (r + s₁) (obs (p.N (R.φ k)) (r + s₁) z)}) :=
          R.weighted_upper hp hqp hLq hr k s₁ h₁0 h₁L _
      _ ≤ ENNReal.ofReal (q.N k ^ R.ε k) * (8 * ENNReal.ofReal (q.N k ^ (-c₁))) := by
          refine mul_le_mul' (R.Z_inv_le hraw k) (mul_le_mul' le_rfl (le_trans ?_ hk))
          exact Finset.sum_le_sum fun a _ =>
            mul_le_mul' le_rfl (measure_mono fun z hz => Or.inr hz)
  have hs3 : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X3 k i) ≤ ENNReal.ofReal (q.N k ^ (-c)) := by
    refine ⟨min τ c₂ / 2, by positivity, ?_⟩
    have hε2 : Tendsto (fun k => 2 * R.ε k) atTop (nhds 0) := by
      simpa using R.ε_lim.const_mul 2
    apply powerSmall_of_factor (RawScalar.N_tendsto hqr) (fun k => by linarith [hNq k])
      hε2 8 (by norm_num) (lt_min hτ hc₂)
    filter_upwards [R.along hp₂] with k hk
    have hN1 : 1 ≤ q.N k := by linarith [hNq k]
    have hNpos : 0 < q.N k := by linarith
    have he : 0 ≤ R.ε k := (R.ε_pos k).le
    have hP : ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a
        {z | p.ρ (R.φ k) a (r + s₂) (obs (p.N (R.φ k)) (r + s₂) z) <
          ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + s₂) - τ))} ≤
        ENNReal.ofReal (q.N k ^ (-c₂)) := by
      refine le_trans ?_ hk
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul' le_rfl (measure_mono fun z hz => Or.inl hz)
    calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X3 k i)
        ≤ ENNReal.ofReal (R.Z k)⁻¹ * (4 * ENNReal.ofReal (q.N k ^ (-τ)) +
          2 * ENNReal.ofReal (p.N (R.φ k) ^ R.ε k) * ENNReal.ofReal (q.N k ^ (-τ)) +
          2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a
            {z | p.ρ (R.φ k) a (r + s₂) (obs (p.N (R.φ k)) (r + s₂) z) <
              ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + s₂) - τ))}) :=
          R.weighted_lower hp hqp hLq hr k s₂ h₂0 h₂L hb₂ _ _ _
      _ ≤ ENNReal.ofReal (q.N k ^ R.ε k) *
          (ENNReal.ofReal (q.N k ^ R.ε k) * (8 * ENNReal.ofReal (q.N k ^ (-(min τ c₂))))) := by
          refine mul_le_mul' (R.Z_inv_le hraw k) ?_
          rw [← R.qN_eq k]
          exact lower_shape (R.qN_eq k ▸ hN1) he _ (R.qN_eq k ▸ hP)
      _ = ENNReal.ofReal (q.N k ^ (2 * R.ε k)) * (8 * ENNReal.ofReal (q.N k ^ (-(min τ c₂)))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _),
            ← Real.rpow_add hNpos]
          ring_nf
  have hgood := exists_good_point hqr ![X0, X1, X2, X3] (by
    intro j
    fin_cases j
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3)
  have hlarge : ∀ᶠ k in atTop, 4 ≤ q.N k ^ τ :=
    ((tendsto_rpow_atTop hτ).comp (RawScalar.N_tendsto hqr)).eventually (eventually_ge_atTop 4)
  obtain ⟨k, ⟨i, z, hz⟩, hk4⟩ := (hgood.and hlarge).exists
  have hz0 : z ∉ X0 k i := hz 0
  have hz1 : z ∉ X1 k i := hz 1
  have hz2 : z ∉ X2 k i := hz 2
  have hz3 : z ∉ X3 k i := hz 3
  simp only [X0, X1, X2, X3, mem_ofPred_eq, not_or, not_lt] at hz0 hz1 hz2 hz3
  rw [← R.qN_eq k] at hz2 hz3
  set N := q.N k with hNdef
  have hN1 : 1 < N := by linarith [hNq k]
  have hN0 : 0 < N := by linarith
  have hlam := (R.lam_pos hraw k i).le
  -- the two real comparisons
  have e1 : N ^ (-q.f s₁ - τ) ≤ R.lam k i * N ^ (-p.f (r + s₁) + τ + τ) := by
    have h := hz0.1.trans hz2
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul hlam, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    calc N ^ (-q.f s₁ - τ) ≤ R.lam k i * (4 * N ^ (-p.f (r + s₁) + τ)) := h
      _ ≤ R.lam k i * (N ^ τ * N ^ (-p.f (r + s₁) + τ)) := by gcongr
      _ = R.lam k i * N ^ (-p.f (r + s₁) + τ + τ) := by
          rw [← Real.rpow_add hN0]
          ring_nf
  have e2 : R.lam k i * N ^ (-p.f (r + s₂) - τ - τ - τ) ≤ N ^ (-q.f s₂ + τ) := by
    have h := hz3.trans hz1.2
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _), ← ENNReal.ofReal_mul hlam,
      ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hN0.le _)] at h
    calc R.lam k i * N ^ (-p.f (r + s₂) - τ - τ - τ)
        = R.lam k i * (N ^ (-τ) * (N ^ (-τ) * N ^ (-p.f (r + s₂) - τ))) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
          ring_nf
      _ ≤ _ := h
  have := exponent_combine hN1 hlam e1 e2
  linarith

include R in
/-- The two relative profile conclusions of the frozen statement. -/
theorem relative_profiles (hp : Spec.Exact p) (hqr : Spec.RawScalar q)
    (hqp : Spec.PureProfile q) (hr : 0 ≤ r) (hbL : b ≤ p.L) (hLq : q.L = p.L - r) :
    (∀ s : ℝ, 0 ≤ s → s ≤ q.L → q.f q.L - q.f s ≤ p.f p.L - p.f (r + s)) ∧
    (b = r → ∀ s : ℝ, 0 ≤ s → s ≤ q.L → q.f s - q.f 0 = p.f (r + s) - p.f r) := by
  have hL0 : 0 ≤ q.L := by
    have h1 := PureProfile.mono hqp 0 0 le_rfl le_rfl
    linarith [RawScalar.L_pos hqr]
  constructor
  · intro s hs0 hsL
    have h := R.profile_pair hp hqr hqp hr hLq s q.L hs0 hsL hL0 le_rfl (by linarith)
    have hrs : r + q.L = p.L := by linarith
    rw [hrs] at h
    exact h
  · intro hbr s hs0 hsL
    have h1 := R.profile_pair hp hqr hqp hr hLq 0 s le_rfl hL0 hs0 hsL (by linarith)
    have h2 := R.profile_pair hp hqr hqp hr hLq s 0 hs0 hsL le_rfl hL0 (by linarith)
    simp only [add_zero] at h1 h2
    linarith

end RefData

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
