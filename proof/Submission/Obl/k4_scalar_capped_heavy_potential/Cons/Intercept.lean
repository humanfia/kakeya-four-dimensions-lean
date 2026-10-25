import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Contract

/-!
# From a potential to the `PotAt` certificate

A polynomial `P` whose residual `X_l - P(u_l)` varies little across the block
along almost every trajectory gives the intercept `c(l)`: the residual at the
block start, clamped to the envelope (the clamp is inactive on bounded
trajectories).
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial

theorem xL_abs_le {l : ℕ × (Fin 5 → ℝ)} {t Y : ℝ} (ht : |t| ≤ 1) (hl : ∀ i, |l.2 i| ≤ Y) :
    |xL l t| ≤ 3 * Y := by
  have ht2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg t) ht
  have e1 := hl 2
  have e2 := hl 3
  have e3 := hl 4
  have hY : 0 ≤ Y := (abs_nonneg _).trans e1
  have hm1 : |t * l.2 3| ≤ Y := by
    rw [abs_mul]
    calc |t| * |l.2 3| ≤ 1 * Y := mul_le_mul ht e2 (abs_nonneg _) (by norm_num)
      _ = Y := one_mul Y
  have hm2 : |t ^ 2 * l.2 4| ≤ Y := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc t ^ 2 * |l.2 4| ≤ 1 * Y := mul_le_mul ht2 e3 (abs_nonneg _) (by norm_num)
      _ = Y := one_mul Y
  unfold xL
  calc
    |l.2 2 + t * l.2 3 + t ^ 2 * l.2 4| ≤ |l.2 2 + t * l.2 3| + |t ^ 2 * l.2 4| := abs_add_le _ _
    _ ≤ |l.2 2| + |t * l.2 3| + |t ^ 2 * l.2 4| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ Y + Y + Y := by linarith
    _ = 3 * Y := by ring

theorem potAt_of_potential {Nk Y H' cs h t₀ Kc Var : ℝ} {D' Tk : ℕ} {jj : Fin (2 ^ Tk)}
    {μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)} {z₀ : Fin 2 → ℝ} {P : MvPolynomial (Fin 2) ℝ}
    (hh : h = ((2 : ℝ) ^ Tk)⁻¹)
    (hI : Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk) =
      Icc t₀ (t₀ + h))
    (ht₀I : t₀ ∈ Icc t₀ (t₀ + h)) (hblock : ∀ t ∈ Icc t₀ (t₀ + h), |t| ≤ 1)
    (hPdeg : P.totalDegree ≤ D') (hPcoeff : ∀ b, |P.coeff b| ≤ H')
    (hPsup : ∀ u : Fin 2 → ℝ, (∀ i, |u i| ≤ Y) → |eval u P| ≤ Kc)
    (hH' : 3 * Y + Kc ≤ H') (hH'1 : 1 ≤ H')
    (hVar : Var ≤ Nk ^ (-1 - 2 * cs)) (hX : 0 ≤ Nk ^ (-1 - 2 * cs))
    (hpath : ∀ᵐ p ∂μ, (∀ i, |p.1.2 i| ≤ Y) ∧ (∀ i, |ubase z₀ h p.1 t₀ i| ≤ Y) ∧
      ∀ t ∈ Icc t₀ (t₀ + h), |(xL p.1 t - eval (ubase z₀ h p.1 t) P) -
        (xL p.1 t₀ - eval (ubase z₀ h p.1 t₀) P)| ≤ Var) :
    ∃ c : ℕ × (Fin 5 → ℝ) → ℝ, PotAt Nk H' cs D' Tk jj μ z₀ P c := by
  set raw : ℕ × (Fin 5 → ℝ) → ℝ := fun l => xL l t₀ - eval (ubase z₀ h l t₀) P with hrawdef
  set c : ℕ × (Fin 5 → ℝ) → ℝ := fun l => max (-H') (min H' (raw l)) with hcdef
  have hrawcont : Continuous raw := by
    have h1 : Continuous fun l : ℕ × (Fin 5 → ℝ) => xL l t₀ := by
      unfold xL; fun_prop
    have h2 : Continuous fun l : ℕ × (Fin 5 → ℝ) => ubase z₀ h l t₀ :=
      (continuous_ubase z₀ h).comp (continuous_id.prodMk continuous_const)
    exact h1.sub ((MvPolynomial.continuous_eval P).comp h2)
  have hcmeas : Measurable c :=
    measurable_const.max (measurable_const.min hrawcont.measurable)
  have hcbound : ∀ l, |c l| ≤ H' := by
    intro l
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  refine ⟨c, hPdeg, hPcoeff, hcmeas, hcbound, ?_⟩
  rw [hI]
  filter_upwards [hpath] with p hp
  obtain ⟨hlp, hup, hvp⟩ := hp
  intro t ht
  have hrawb : |raw p.1| ≤ H' := by
    have h1 : |raw p.1| ≤ |xL p.1 t₀| + |eval (ubase z₀ h p.1 t₀) P| := abs_sub _ _
    have h2 := xL_abs_le (hblock t₀ ht₀I) hlp
    have h3 := hPsup _ hup
    linarith
  have hcraw : c p.1 = raw p.1 := by
    rw [abs_le] at hrawb
    show max (-H') (min H' (raw p.1)) = raw p.1
    rw [min_eq_right hrawb.2, max_eq_right hrawb.1]
  rw [← hh]
  rw [hcraw]
  calc
    |xL p.1 t - eval (fun e => ((![t, yL p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) P - raw p.1| =
        |(xL p.1 t - eval (ubase z₀ h p.1 t) P) - (xL p.1 t₀ - eval (ubase z₀ h p.1 t₀) P)| :=
      rfl
    _ ≤ Var := hvp t ht
    _ ≤ Nk ^ (-1 - 2 * cs) := hVar
    _ ≤ H' * Nk ^ (-1 - 2 * cs) := le_mul_of_one_le_left hX hH'1

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
