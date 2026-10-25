import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.FixedSum

/-!
# The fixed-scale inequality

For a true terminal chart system at tolerance `ε` and a coarsened depth `T₁ ≤ T`,

`N^(-ε)² ≤ pairMass + Σ_w ω_w μ_w(Exc_w) + Kc`,

where `Exc_w` is the exceptional set of the joint terminal/angular cap at angular depth
`uu` and `Kc = 12 N^(-S uu + τ) (96 R² N^ε + 3) N^(3ε) (1 + 2R)`, `R = 2^(T - T₁)`,
provided bad label pairs have boundedly many angular bins (`hFb`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- One capped witness term is charged to the true floor of its source label. -/
lemma cap_term_le {Nk : ℝ} (hN : 0 < Nk) (fL Su τ ε Jv : ℝ) (hJ : 0 < Jv) (T T₁ : ℕ) (R : ℝ)
    (hR : 0 ≤ R) {m : ℝ≥0∞}
    (hfloor : ENNReal.ofReal (Nk ^ (-fL) * Jv / (Nk ^ ε * (2 : ℝ) ^ T)) ≤ m) :
    ENNReal.ofReal ((2 : ℝ) ^ T₁) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
      (ENNReal.ofReal (Nk ^ (-fL - Su + τ)) *
        (ENNReal.ofReal (2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1) * (ENNReal.ofReal (Nk ^ ε) * 6) *
          ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹ * (2 * ((1 + 2 * R) * (Nk ^ ε * Jv)))))))
    ≤ ENNReal.ofReal (12 * Nk ^ (-Su + τ) * (2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1) *
        Nk ^ ε * Nk ^ ε * Nk ^ ε * (1 + 2 * R)) * m := by
  have hNε : 0 < Nk ^ ε := Real.rpow_pos_of_pos hN _
  have hNf : 0 < Nk ^ (-fL) := Real.rpow_pos_of_pos hN _
  have hNc : 0 < Nk ^ (-Su + τ) := Real.rpow_pos_of_pos hN _
  have h6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
  rw [h6]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  have hsplit : Nk ^ (-fL - Su + τ) = Nk ^ (-fL) * Nk ^ (-Su + τ) := by
    rw [← Real.rpow_add hN]; ring_nf
  calc _ = ENNReal.ofReal ((12 * Nk ^ (-Su + τ) * (2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1) *
        Nk ^ ε * Nk ^ ε * Nk ^ ε * (1 + 2 * R)) *
          (Nk ^ (-fL) * Jv / (Nk ^ ε * (2 : ℝ) ^ T))) := by
        congr 1
        rw [hsplit]
        field_simp
        ring
    _ = _ := ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr

open scoped Classical in
/-- The fixed-scale inequality. -/
theorem fixed_scale_bound {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)} {B : ℕ} {hh ε : ℝ}
    (hNpos : 0 < N p k)
    (hω0 : ∀ w, 0 ≤ ω p k w) (hω1 : ∑ w, ω p k w = 1)
    (hν : ∀ w, IsProbabilityMeasure (ν p k w))
    (hcd : ChartData p B (L p) (L p) hh ε true k T n γ j A C u v J P Λ)
    {a e uu τ : ℝ} {T₁ : ℕ} (hT₁ : T₁ ≤ T)
    (hGm : ∀ w, Measurable (G p k w uu))
    (hmap : ∀ w, Measure.map (obsA p k uu) (mu p k w) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G p k w uu))
    (Fb : Fin (2 ^ T₁) → Fin n → Fin n → Finset ℤ)
    (hFb : ∀ w b i i', i ∈ Sblk p k T n γ j T₁ w b → i' ∈ Sblk p k T n γ j T₁ w b →
      ¬ Agrees p k T₁ n u v P a e b i i' →
      (Fb b i i').card ≤ 6 ∧ ∀ l ∈ A i ∩ A i', ⌊l.2 1 / N p k ^ (-uu)⌋ ∈ Fb b i i') :
    ENNReal.ofReal (N p k ^ (-ε)) ^ 2 ≤ pairMass p k T n γ j C u v P a e T₁ +
      ∑ w, ENNReal.ofReal (ω p k w) * mu p k w (Exc p k w uu τ) +
      ENNReal.ofReal (12 * N p k ^ (-(S p * uu) + τ) *
        (2 * (48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * N p k ^ ε + 1) + 1) *
        N p k ^ ε * N p k ^ ε * N p k ^ ε * (1 + 2 * (2 : ℝ) ^ (T - T₁))) := by
  obtain ⟨_, _, hAC, hdisj, hCsub, hlab, hΛcard, hΛmeas, hΛae, hmass⟩ := hcd
  have hA : ∀ i, MeasurableSet (A i) := fun i => (hAC i).1
  have hC : ∀ i, MeasurableSet (C i) := fun i => (hAC i).2
  have hJ : ∀ i, 0 < J i := fun i => (hlab i).2.1
  have hdeg : ∀ i, (P i).totalDegree ≤ 2 := fun i => (hlab i).2.2.2.2.2.1
  have hfit : ∀ i, ∀ l ∈ A i, ∀ t ∈ I T (j i), |y l t - u i - t * v i| ≤ N p k ^ ε * J i ∧
      |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ ε * N p k ^ (-(L p)) :=
    fun i => (hlab i).2.2.2.2.2.2.2.2.2.2.1
  have hfloor : ∀ i, ENNReal.ofReal (N p k ^ (-f p (L p)) * J i / (N p k ^ ε * (2 : ℝ) ^ T)) ≤
      mu p k (γ i) (C i) := fun i => (hlab i).2.2.2.2.2.2.2.2.2.2.2 rfl
  set R : ℝ := (2 : ℝ) ^ (T - T₁) with hR
  have hR0 : 0 ≤ R := by positivity
  set Kc : ℝ := 12 * N p k ^ (-(S p * uu) + τ) *
    (2 * (48 * R ^ 2 * N p k ^ ε + 1) + 1) *
    N p k ^ ε * N p k ^ ε * N p k ^ ε * (1 + 2 * R) with hKc
  have hωsum : ∑ w, ENNReal.ofReal (ω p k w) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω0 w), hω1, ENNReal.ofReal_one]
  -- the one-time mass in coarse blocks
  have hmass' : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ w, ∑ b : Fin (2 ^ T₁),
      ENNReal.ofReal (ω p k w) * ((ν p k w).prod volume) (Dblk p k T n γ j C T₁ w b) := by
    refine hmass.trans (Finset.sum_le_sum fun w _ => ?_)
    rw [← Finset.mul_sum]
    gcongr
    calc mu p k w {q | ∃ i, γ i = w ∧ q ∈ C i}
        ≤ ((ν p k w).prod volume) {q | ∃ i, γ i = w ∧ q ∈ C i} :=
          Measure.restrict_le_self _
      _ ≤ ((ν p k w).prod volume) (⋃ b : Fin (2 ^ T₁), Dblk p k T n γ j C T₁ w b) := by
          apply measure_mono
          intro q hq
          obtain ⟨i, hγi, hqi⟩ := hq
          obtain ⟨b, hb⟩ := exists_coarse hT₁ (j i)
          simp only [mem_iUnion, Dblk]
          exact ⟨b, i, mem_Sblk.mpr ⟨hγi, hb⟩, hqi⟩
      _ ≤ ∑ b : Fin (2 ^ T₁), ((ν p k w).prod volume) (Dblk p k T n γ j C T₁ w b) :=
          measure_iUnion_fintype_le _ _
  -- all pairs
  have hall := all_pairs_lower (K := 2 ^ T₁) (by positivity)
    (fun w => ENNReal.ofReal (ω p k w)) hωsum (ν p k)
    (fun w b => Dblk p k T n γ j C T₁ w b) (fun w b => measurableSet_Dblk hC T₁ w b)
    ENNReal.ofReal_ne_top hmass'
  refine hall.trans ?_
  rw [← ofReal_two_pow]
  -- per block decomposition
  have hblock : ∀ w b, ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      ((ν p k w).prod (volume.prod volume))
        (pairSet (Dblk p k T n γ j C T₁ w b) (Dblk p k T n γ j C T₁ w b)) ≤
      ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ((ν p k w).prod (volume.prod volume)) (goodPairs p k T n γ j C u v P a e T₁ w b) +
      ENNReal.ofReal (ω p k w) * (ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
          mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩
            Exc p k w uu τ)) +
      ENNReal.ofReal (ω p k w) * (ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
          (ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) *
            (ENNReal.ofReal (2 * (48 * R ^ 2 * N p k ^ ε + 1) + 1) *
              (ENNReal.ofReal (N p k ^ ε) * 6) *
              ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹ *
                (2 * ((1 + 2 * R) * (N p k ^ ε * J i))))))) := by
    intro w b
    have := hν w
    have hdec := pair_decomp hA hC hCsub u v P a e T₁ w b (ν p k w)
    calc _ ≤ ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
          (((ν p k w).prod (volume.prod volume)) (goodPairs p k T n γ j C u v P a e T₁ w b) +
            ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
              (mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩
                Exc p k w uu τ) +
              ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) *
                (ENNReal.ofReal (2 * (48 * R ^ 2 * N p k ^ ε + 1) + 1) *
                  (ENNReal.ofReal (N p k ^ ε) * 6) *
                  ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹ *
                    (2 * ((1 + 2 * R) * (N p k ^ ε * J i))))))) := by
          gcongr
          refine hdec.trans ?_
          gcongr with i hi
          exact witness_cap_bound (τ := τ) hNpos hA hC hCsub hfit hJ hdeg hΛcard hΛmeas hΛae w
            (hGm w) (hmap w) hT₁ Fb (hFb w) b i hi
      _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          ring_nf
  calc ∑ w, ∑ b : Fin (2 ^ T₁), ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ((ν p k w).prod (volume.prod volume))
          (pairSet (Dblk p k T n γ j C T₁ w b) (Dblk p k T n γ j C T₁ w b))
      ≤ ∑ w, ∑ b : Fin (2 ^ T₁), (_ + _ + _) := by
        gcongr with w _ b _
        exact hblock w b
    _ = pairMass p k T n γ j C u v P a e T₁ +
        ∑ w, ENNReal.ofReal (ω p k w) * ∑ b : Fin (2 ^ T₁), (ENNReal.ofReal ((2 : ℝ) ^ T₁) *
          ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
            mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩
              Exc p k w uu τ)) +
        ∑ w, ENNReal.ofReal (ω p k w) * ∑ b : Fin (2 ^ T₁), (ENNReal.ofReal ((2 : ℝ) ^ T₁) *
          ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
            (ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) *
              (ENNReal.ofReal (2 * (48 * R ^ 2 * N p k ^ ε + 1) + 1) *
                (ENNReal.ofReal (N p k ^ ε) * 6) *
                ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹ *
                  (2 * ((1 + 2 * R) * (N p k ^ ε * J i))))))) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        rfl
    _ ≤ pairMass p k T n γ j C u v P a e T₁ +
        ∑ w, ENNReal.ofReal (ω p k w) * mu p k w (Exc p k w uu τ) +
        ∑ w, ENNReal.ofReal (ω p k w) * ENNReal.ofReal Kc := by
        gcongr with w _ w _
        · have := hν w
          exact exc_sum_le hA hC hdisj hCsub u v P a e hT₁ uu τ w (hGm w)
        · have := hν w
          refine cap_sum_le hC hdisj hCsub hT₁ w Kc _ ?_
          intro i hγi
          have := cap_term_le hNpos (f p (L p)) (S p * uu) τ ε (J i) (hJ i) T T₁ R hR0
            (m := mu p k w (C i)) (by rw [← hγi]; exact hfloor i)
          exact this
    _ = _ := by
        rw [← Finset.sum_mul, hωsum, one_mul]
