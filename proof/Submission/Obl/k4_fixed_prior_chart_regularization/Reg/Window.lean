-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/Window.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Stages
import Submission.Obl.k4_fixed_prior_chart_regularization.RegKernels

/-!
# Window masses from the mixed cap

At a fixed time, the labeled lines whose normal scalar `S = x̄ - F · y` lies in a window of
length `q ∈ [ζ, 1]` have prior mass at most `200 K⁴ q^d` (`window_mass`): cover the static
coordinates `|y| ≤ K` by `q`-squares; on each square the bounded row turns the scalar window
into at most `8K` cells of `x̄` of width `q`, each capped by the mixed cap `K q^(2+d)`
(`slab_cap_gen`, the slab cap of `JetFit.Chart` with only the cube cap and the row bound).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_scal {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {F : ℝ → Fin 2 → ℝ}
    (hy : Measurable y) (hβ : Measurable β) (hγ : Measurable γ) (hF : Measurable F) :
    Measurable (fun p : Ω × ℝ => FirstJet.scal y β γ F p.1 p.2) := by
  have hy0 : Measurable (fun p : Ω × ℝ => y p.1 0) :=
    (measurable_pi_apply 0).comp (hy.comp measurable_fst)
  have hy1 : Measurable (fun p : Ω × ℝ => y p.1 1) :=
    (measurable_pi_apply 1).comp (hy.comp measurable_fst)
  have hF0 : Measurable (fun p : Ω × ℝ => F p.2 0) :=
    (measurable_pi_apply 0).comp (hF.comp measurable_snd)
  have hF1 : Measurable (fun p : Ω × ℝ => F p.2 1) :=
    (measurable_pi_apply 1).comp (hF.comp measurable_snd)
  unfold FirstJet.scal FirstJet.xbar
  exact ((hβ.comp measurable_fst).add (measurable_snd.mul (hγ.comp measurable_fst))).sub
    ((hF0.mul hy0).add (hF1.mul hy1))

/-- **Slab cap** from cube caps and the row bound (the slab cap of `JetFit.Chart`, with only
the hypotheses it uses). -/
theorem slab_cap_gen {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K d t q : ℝ} (hK : 0 ≤ K) (hq : 0 < q) (hF : ∀ i, |F t i| ≤ K)
    (hcap : ∀ m : Fin 3 → ℤ, ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = m 0 ∧
      ⌊y l 0 / q⌋ = m 1 ∧ ⌊y l 1 / q⌋ = m 2} ≤ ENNReal.ofReal (K * q ^ (2 + d)))
    (a₀ a₁ s₀ : ℝ) (n₀ n₁ n₂ : ℕ) (X : Set Ω)
    (hX : ∀ l ∈ X, (l, t) ∈ E ∧ a₀ ≤ y l 0 ∧ y l 0 ≤ a₀ + n₀ * q ∧ a₁ ≤ y l 1 ∧
      y l 1 ≤ a₁ + n₁ * q ∧ s₀ ≤ FirstJet.scal y β γ F l t ∧
      FirstJet.scal y β γ F l t ≤ s₀ + n₂ * q) :
    ν X ≤ ((n₀ + 1) * (n₁ + 1) * (n₂ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) *
      ENNReal.ofReal (K * q ^ (2 + d)) := by
  classical
  set M : ℕ := ⌈2 * K⌉₊ with hM
  have hMK : 2 * K ≤ (M : ℝ) := Nat.le_ceil _
  set W₀ : Finset ℤ := Finset.Icc ⌊a₀ / q⌋ (⌊a₀ / q⌋ + n₀)
  set W₁ : Finset ℤ := Finset.Icc ⌊a₁ / q⌋ (⌊a₁ / q⌋ + n₁)
  set base : ℤ × ℤ → ℤ := fun m => ⌊(s₀ + (F t 0 * ((m.1 : ℝ) * q) + F t 1 * ((m.2 : ℝ) * q))
    - M * q) / q⌋
  set Cubes : Finset (Fin 3 → ℤ) := (W₀ ×ˢ W₁).biUnion (fun m =>
    (Finset.Icc (base m) (base m + (n₂ + 2 * M))).image (fun m₀ => ![m₀, m.1, m.2]))
  have hsub : X ⊆ ⋃ m ∈ Cubes, {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = m 0 ∧
      ⌊y l 0 / q⌋ = m 1 ∧ ⌊y l 1 / q⌋ = m 2} := by
    intro l hl
    obtain ⟨hlE, h0, h0', h1, h1', hs, hs'⟩ := hX l hl
    set m₁ := ⌊y l 0 / q⌋
    set m₂ := ⌊y l 1 / q⌋
    have hm₁ : m₁ ∈ W₀ := JetFit.floor_window hq h0 h0'
    have hm₂ : m₂ ∈ W₁ := JetFit.floor_window hq h1 h1'
    have e0 : |y l 0 - (m₁ : ℝ) * q| ≤ q := by
      have a := Int.floor_le (y l 0 / q); have b := Int.lt_floor_add_one (y l 0 / q)
      rw [le_div_iff₀ hq] at a; rw [div_lt_iff₀ hq] at b
      rw [abs_le]; constructor <;> nlinarith
    have e1 : |y l 1 - (m₂ : ℝ) * q| ≤ q := by
      have a := Int.floor_le (y l 1 / q); have b := Int.lt_floor_add_one (y l 1 / q)
      rw [le_div_iff₀ hq] at a; rw [div_lt_iff₀ hq] at b
      rw [abs_le]; constructor <;> nlinarith
    have hF0 := hF 0
    have hF1 := hF 1
    have hcorner : |(F t 0 * y l 0 + F t 1 * y l 1) -
        (F t 0 * ((m₁ : ℝ) * q) + F t 1 * ((m₂ : ℝ) * q))| ≤ 2 * K * q := by
      have : (F t 0 * y l 0 + F t 1 * y l 1) -
          (F t 0 * ((m₁ : ℝ) * q) + F t 1 * ((m₂ : ℝ) * q)) =
          F t 0 * (y l 0 - (m₁ : ℝ) * q) + F t 1 * (y l 1 - (m₂ : ℝ) * q) := by ring
      rw [this]
      calc _ ≤ |F t 0 * (y l 0 - (m₁ : ℝ) * q)| + |F t 1 * (y l 1 - (m₂ : ℝ) * q)| :=
            abs_add_le _ _
        _ ≤ K * q + K * q := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hF0 e0 (abs_nonneg _) hK)
              (mul_le_mul hF1 e1 (abs_nonneg _) hK)
        _ = 2 * K * q := by ring
    have hxb : FirstJet.xbar β γ l t =
        FirstJet.scal y β γ F l t + (F t 0 * y l 0 + F t 1 * y l 1) := by
      simp only [FirstJet.scal]; ring
    have hMq : 2 * K * q ≤ (M : ℝ) * q := mul_le_mul_of_nonneg_right hMK hq.le
    have hwin : ⌊FirstJet.xbar β γ l t / q⌋ ∈
        Finset.Icc (base (m₁, m₂)) (base (m₁, m₂) + (n₂ + 2 * M)) := by
      have := JetFit.floor_window
        (a := s₀ + (F t 0 * ((m₁ : ℝ) * q) + F t 1 * ((m₂ : ℝ) * q)) - M * q)
        (x := FirstJet.xbar β γ l t) (n := n₂ + 2 * M) hq
        (by rw [hxb]; linarith [(abs_le.1 hcorner).1])
        (by rw [hxb]; push_cast; linarith [(abs_le.1 hcorner).2])
      exact this
    refine mem_iUnion₂.2 ⟨![⌊FirstJet.xbar β γ l t / q⌋, m₁, m₂], Finset.mem_biUnion.2
      ⟨(m₁, m₂), Finset.mem_product.2 ⟨hm₁, hm₂⟩, Finset.mem_image.2 ⟨_, hwin, rfl⟩⟩, ?_⟩
    exact ⟨hlE, by simp, by simp [m₁], by simp [m₂]⟩
  have hcard : Cubes.card ≤ (n₀ + 1) * (n₁ + 1) * (n₂ + 2 * M + 1) := by
    calc Cubes.card ≤ ∑ m ∈ W₀ ×ˢ W₁, ((Finset.Icc (base m) (base m + (n₂ + 2 * M))).image
          (fun m₀ => ![m₀, m.1, m.2])).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ W₀ ×ˢ W₁, (n₂ + 2 * M + 1) := by
          apply Finset.sum_le_sum
          intro m _
          refine (Finset.card_image_le).trans ?_
          rw [Int.card_Icc]
          omega
      _ = (W₀ ×ˢ W₁).card * (n₂ + 2 * M + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (n₀ + 1) * (n₁ + 1) * (n₂ + 2 * M + 1) := by
          have e0 : (⌊a₀ / q⌋ + n₀ + 1 - ⌊a₀ / q⌋).toNat = n₀ + 1 := by omega
          have e1 : (⌊a₁ / q⌋ + n₁ + 1 - ⌊a₁ / q⌋).toNat = n₁ + 1 := by omega
          rw [Finset.card_product, Int.card_Icc, Int.card_Icc, e0, e1]
  calc ν X ≤ ∑ m ∈ Cubes, ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = m 0 ∧
        ⌊y l 0 / q⌋ = m 1 ∧ ⌊y l 1 / q⌋ = m 2} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _m ∈ Cubes, ENNReal.ofReal (K * q ^ (2 + d)) :=
        Finset.sum_le_sum (fun m _ => hcap m)
    _ = Cubes.card * ENNReal.ofReal (K * q ^ (2 + d)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- **Window mass**: at a fixed time, the labeled scalars in a window of length `q ∈ [ζ, 1]`
carry prior mass at most `200 K⁴ q^d`. -/
theorem window_mass {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (hU : UnregularizedChart ν y β γ E F d K ζ)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (t q b : ℝ) (hq : ζ ≤ q) (hq1 : q ≤ 1) :
    ν {l | (l, t) ∈ E ∧ b ≤ FirstJet.scal y β γ F l t ∧ FirstJet.scal y β γ F l t ≤ b + q} ≤
      ENNReal.ofReal (200 * K ^ 4 * q ^ d) := by
  have hq0 : 0 < q := hζ.trans_le hq
  set n₀ : ℕ := ⌈2 * K / q⌉₊ with hn₀
  have hn₀le : (n₀ : ℝ) ≤ 2 * K / q + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hn₀ge : 2 * K / q ≤ (n₀ : ℝ) := Nat.le_ceil _
  have hn₀q : 2 * K ≤ n₀ * q := by rwa [div_le_iff₀ hq0] at hn₀ge
  have hslab := slab_cap_gen (ν := ν) (y := y) (β := β) (γ := γ) (E := E) (F := F) (d := d)
    (t := t) (by linarith) hq0 (fun i => hU.bound_F t i)
    (fun m => absCap_of_mixedCap hU hζ t q hq hq1 m) (-K) (-K) b n₀ n₀ 1
    {l | (l, t) ∈ E ∧ b ≤ FirstJet.scal y β γ F l t ∧ FirstJet.scal y β γ F l t ≤ b + q}
    (by
      rintro l ⟨hl, h1, h2⟩
      have hy0 := abs_le.1 (hU.bound_y l 0)
      have hy1 := abs_le.1 (hU.bound_y l 1)
      refine ⟨hl, by linarith, by linarith, by linarith, by linarith, h1, by simpa using h2⟩)
  refine hslab.trans ?_
  set M : ℕ := ⌈2 * K⌉₊ with hM
  have hMle : (M : ℝ) ≤ 2 * K + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have hpow : q ^ (2 + d) = q ^ 2 * q ^ d := by
    rw [Real.rpow_add hq0, Real.rpow_two]
  rw [hpow]
  have hqd : 0 ≤ q ^ d := Real.rpow_nonneg hq0.le _
  have h1 : ((n₀ : ℝ) + 1) * q ≤ 4 * K := by
    have : (n₀ : ℝ) * q ≤ (2 * K / q + 1) * q := mul_le_mul_of_nonneg_right hn₀le hq0.le
    have e : (2 * K / q + 1) * q = 2 * K + q := by field_simp
    nlinarith
  have h2 : ((1 : ℝ) + 2 * M + 1) ≤ 8 * K := by nlinarith
  have hA : 0 ≤ ((n₀ : ℝ) + 1) * q := by positivity
  calc ((n₀ : ℝ) + 1) * ((n₀ : ℝ) + 1) * ((1 : ℝ) + 2 * M + 1) * (K * (q ^ 2 * q ^ d))
      = (((n₀ : ℝ) + 1) * q) * (((n₀ : ℝ) + 1) * q) * ((1 : ℝ) + 2 * M + 1) * K * q ^ d := by
        ring
    _ ≤ (4 * K) * (4 * K) * (8 * K) * K * q ^ d := by
        apply mul_le_mul_of_nonneg_right _ hqd
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply mul_le_mul (mul_le_mul h1 h1 hA (by linarith)) h2 (by positivity) (by positivity)
    _ ≤ 200 * K ^ 4 * q ^ d := by nlinarith [pow_pos (show (0:ℝ) < K by linarith) 4]

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
