import Submission.Obl.k4_scalar_tangent_isotropic_improvement.NormalizedPacketRecovery
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.RecoveryNumerics
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.IncidenceFacts
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.FiniteScaleGrid
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.SequenceRecovery
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement
noncomputable section
open Set MeasureTheory MvPolynomial Filter
open scoped Classical BigOperators ENNReal

set_option maxHeartbeats 2000000 in
/-- The complete recovery endpoint for a heavy normalized potential certificate.
This is the former o142 contract; its proof is assembled here from the finite
original-law recovery core and uniform subpower budgets. -/
theorem heavy_potential_quadratic_recovery : ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))), (fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun (z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ) => (fun (phys : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 3 → ℤ) => (fun (coeff : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) → Fin 5 → ℤ) => (fun (vel : ℕ → ℝ → ℤ → Set ℝ) => (fun (rowbin : ℕ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℤ) => (fun (subpower : (ℕ → ℝ) → Prop) => (fun (potential : Prop) => potential → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s c : ℝ) (i : Fin (n k s)) (P : MvPolynomial (Fin 2) ℝ), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧ (∀ b, |P.coeff b| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-d * c - ε) / (2 : ℝ) ^ T k s) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) {p | p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ∀ t ∈ I (T k s) (j k s i), |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤ N k ^ ε * N k ^ (-s - c)}) (∃ (H : ℕ → ℝ) (D : ℕ) (Z B : ℝ), subpower H ∧ 10 ≤ Z ∧ Z + 10 ≤ B ∧ ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∃ (i : Fin (n k 1)) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ), (fun (h c : ℝ) => MeasurableSet (A k 1 i) ∧ MeasureTheory.IsProbabilityMeasure (ν k (γ k 1 i)) ∧ MeasureTheory.IsProbabilityMeasure (π k (γ k 1 i)) ∧ (∀ᵐ l ∂ν k (γ k 1 i), ∀ e, |l.2 e| ≤ H k) ∧ N k ^ (-κ) / H k ≤ h ∧ h ≤ H k * N k ^ (-κ) ∧ 0 < h ∧ h ≤ 1 ∧ ENNReal.ofReal (N k ^ (-d) * h / H k) ≤ ν k (γ k 1 i) (A k 1 i) ∧ ν k (γ k 1 i) (A k 1 i) ≤ ENNReal.ofReal (H k * N k ^ (-d) * h) ∧ μ ≤ ρ k (γ k 1 i) ∧ μ ≤ ENNReal.ofReal (H k) • ((ν k (γ k 1 i)).prod MeasureTheory.volume) ∧ μ {p | p.1 ∈ A k 1 i ∧ p.2 ∈ I (T k 1) (j k 1 i)}ᶜ = 0 ∧ ENNReal.ofReal (h * N k ^ (-d * c) / H k) * ν k (γ k 1 i) (A k 1 i) ≤ μ Set.univ ∧ z₀ 0 = (((j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ T k 1) ∧ (∀ e, |z₀ e| ≤ H k) ∧ (∀ᵐ p ∂μ, ∀ t ∈ I (T k 1) (j k 1 i), ∀ e : Fin 2, |(![t, y p.1 t] e - z₀ e) / h| ≤ H k) ∧ (∀ q : Fin 2 → ℤ, μ {p | (fun e : Fin 2 => (⌊((![p.2,y p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (N k ^ (-Z))⌋ : ℤ)) = q} ≤ ENNReal.ofReal ((H k * h * N k ^ (-d * c)) * N k ^ (-2 * Z)) * ν k (γ k 1 i) (A k 1 i)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∀ c : ℤ, π k (γ k 1 i) (vel k r c) ≤ ENNReal.ofReal (H k * N k ^ (-S * r))) ∧ ∀ (q : Fin 3 → ℤ) (c : ℤ), μ {p | phys k B p = q ∧ p.1.2 1 ∈ vel k r c} ≤ ENNReal.ofReal (H k) * μ {p | phys k B p = q} * π k (γ k 1 i) (vel k r c)) ∧ P.totalDegree ≤ D ∧ (∀ b, |P.coeff b| ≤ H k) ∧ (∀ᵐ p ∂μ, ∀ t ∈ I (T k 1) (j k 1 i), |x p.1 t - MvPolynomial.eval (fun e : Fin 2 => ((![t,y p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) P| ≤ H k * N k ^ (-1 - c))) (((2 : ℝ) ^ T k 1)⁻¹) (κ * (1-d) / 1000))) (fun H => (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N k ^ ε)) (fun k r v e => (⌊v e / (N k ^ (-r))⌋ : ℤ))) (fun k r c => {v : ℝ | (⌊v / (N k ^ (-r))⌋ : ℤ) = c})) (fun k r l e => (⌊l.2 e / (N k ^ (-r))⌋ : ℤ))) (fun k r p e => (⌊(![p.2, y p.1 p.2, x p.1 p.2] : Fin 3 → ℝ) e / (N k ^ (-r))⌋ : ℤ))) (fun B r p e => (⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋ : ℤ))) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)) (fun l t => l.2 0 + t * l.2 1) := by
  intro N K hN hNt hK d κ S hd hd1 hκ hκ1 hS W ν ρ π T n γ j A hpotential
  rcases hpotential with ⟨H, D, Z, B, hH, hZ, hB, hpotential⟩
  obtain ⟨C₀, C₁, Cₜ, Cq, Ca, hC₀, hC₁, hCₜ, hCq, hCa, hfinite⟩ :=
    quadratic_recovery_on_normalized_packet D
  obtain ⟨L, hL, hLsub, hLdom⟩ := exists_subpower_polynomial_buffer N H hN hNt hH.1 hH.2
  obtain ⟨G, hG, hGsub, hGdom⟩ := exists_subpower_polynomial_buffer N L hN hNt hL hLsub
  let c : ℝ := κ * (1 - d) / 1000
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; nlinarith
  let Ccost : ℝ := 1 + C₀ * (4096 * ((D : ℝ) + 1)) ^ (2 * D) * (Cₜ + 3 * C₁)
  let duration : (k : ℕ) → Fin (n k 1) → ℝ := fun k _ => ((2 : ℝ) ^ T k 1)⁻¹
  let currentMass : (k : ℕ) → Fin (n k 1) → ℝ≥0∞ := fun k i => ν k (γ k 1 i) (A k 1 i)
  let law : (k : ℕ) → Fin (n k 1) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
    fun k i => ρ k (γ k 1 i)
  let interval : (k : ℕ) → Fin (n k 1) → Set ℝ := fun k i =>
    Set.Icc (((j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ T k 1)
      ((((j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k 1)
  let Fit : (k : ℕ) → Fin (n k 1) → MvPolynomial (Fin 2) ℝ → ℝ → Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
    fun k i Q E => {p | p.1 ∈ A k 1 i ∧ p.2 ∈ interval k i ∧
      ∀ t ∈ interval k i, |quadraticHidden p.1.2 t - eval (quadraticBase p.1.2 t) Q| ≤ E}
  have hcert : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∃ (i : Fin (n k 1)) (Q : MvPolynomial (Fin 2) ℝ), Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ G k * N k ^ (4 * κ)) ∧
        ENNReal.ofReal (duration k i * N k ^ (-d * c) / G k) * currentMass k i ≤
          law k i (Fit k i Q (G k * N k ^ δ * N k ^ (-1 - c))) := by
    intro δ hδ
    let r : ℝ := min (1 / 2) (δ / 18)
    have hr : 0 < r := lt_min (by norm_num) (by positivity)
    have hr1 : r ≤ 1 / 2 := min_le_left _ _
    have hrδ : 18 * r ≤ δ := by have h := min_le_right (1 / 2 : ℝ) (δ / 18); nlinarith
    let Rtest : ℝ := 2 + B + r⁻¹
    have hBpos : 0 < B := by linarith
    have hR : 1 < Rtest := by dsimp [Rtest]; linarith [inv_pos.mpr hr]
    have hRpos : 0 < Rtest := zero_lt_one.trans hR
    have hBrange : Rtest⁻¹ ≤ B ∧ B ≤ Rtest := by
      constructor
      · exact (inv_le_one_of_one_le₀ hR.le).trans (by linarith)
      · dsimp [Rtest]; linarith [inv_pos.mpr hr]
    have hrrange : Rtest⁻¹ ≤ r ∧ r ≤ Rtest := by
      constructor
      · apply (inv_le_iff_one_le_mul₀ hRpos).mpr
        have he : r * Rtest = r * (2 + B) + 1 := by
          dsimp [Rtest]
          rw [mul_add, mul_inv_cancel₀ hr.ne']
        rw [he]
        linarith [mul_pos hr (by linarith : 0 < 2 + B)]
      · exact (hr1.trans (by linarith : (1 : ℝ) / 2 ≤ Rtest))
    have hang := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (fun k => by linarith [hN k]) hNt hL hLsub 2
      (a := 0) (b := S * r) (by positivity) (A := 40) (by norm_num)
    filter_upwards [hpotential Rtest hR, hLdom 1 2,
      hLdom (2 * D + 1) (Ca * 4 ^ (2 * D)), hGdom (18 * D + 22) Ccost,
      hGdom 9 Cq, hGdom 1 1, hang] with k hk hHL hcoeffL hGloss hGcoeff hLG hang
    simp only [pow_one, one_mul, Real.rpow_zero, mul_one] at hHL hLG hang
    rcases hk with ⟨i, μ, z₀, p, hA, hν, hπ, hcoeff, hscale, hscale', hh, hh1,
      hνlo, hνhi, hμρ, hμdom, hsupport, hmass, hz₀, hzbound, hbox, hgrid,
      hpalette, hp, hpcoeff, hfit⟩
    letI : IsProbabilityMeasure (ν k (γ k 1 i)) := hν
    letI : IsProbabilityMeasure (π k (γ k 1 i)) := hπ
    have hNpos : 0 < N k := by linarith [hN k]
    have hN1 : 1 ≤ N k := by linarith [hN k]
    have hHpos : 0 < H k := zero_lt_one.trans_le (hH.1 k)
    have hLpos : 0 < L k := zero_lt_one.trans_le (hL k)
    have hHL' : H k ≤ L k := by linarith
    have hHG : H k ≤ G k := hHL'.trans hLG
    let h : ℝ := duration k i
    let t₀ : ℝ := ((j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ T k 1
    have hinterval : interval k i = Set.Icc t₀ (t₀ + h) := by
      have hend : (((j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k 1 = t₀ + h := by
        dsimp [t₀, h, duration]
        ring
      exact congrArg (Set.Icc t₀) hend
    have hmembership : ∀ᵐ p ∂μ, p.1 ∈ A k 1 i ∧ p.2 ∈ interval k i :=
      (ae_iff).mpr hsupport
    have htime : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc t₀ (t₀ + h) := by
      filter_upwards [hmembership] with p hp
      simpa only [← hinterval] using hp.2
    letI : IsFiniteMeasure μ := finite_original_incidence (ν k (γ k 1 i)) μ (H k)
      t₀ (t₀ + h) hμdom ((ae_iff).mp htime)
    have haep := ae_original_incidence (ν k (γ k 1 i)) μ (H k) hμdom hcoeff
    have hνpos : 0 < ν k (γ k 1 i) (A k 1 i) :=
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < N k ^ (-d) * h / H k)).trans_le hνlo
    have hμpos : 0 < μ Set.univ := (bot_lt_iff_ne_bot.mpr (mul_ne_zero
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < h * N k ^ (-d * c) / H k)).ne'
      hνpos.ne')).trans_le hmass
    let amass : ℝ := (ν k (γ k 1 i) (A k 1 i)).toReal
    let m : ℝ := h * N k ^ (-d * c) * amass
    have hamass : 0 < amass := ENNReal.toReal_pos hνpos.ne' (measure_ne_top _ _)
    have hm : 0 < m := by dsimp [m]; positivity
    have hmassreal : m / H k ≤ (μ Set.univ).toReal := by
      have ht := ENNReal.toReal_mono (measure_ne_top μ _) hmass
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
      exact ht.trans_eq' (by dsimp [m, amass]; ring)
    have hCaL : Ca * H k * (4 * H k) ^ (2 * D) ≤ L k := by
      calc
        _ = (Ca * 4 ^ (2 * D)) * H k ^ (2 * D + 1) := by
          rw [mul_pow, pow_succ]
          ring
        _ ≤ _ := hcoeffL
    have ht₀ : 0 ≤ t₀ := by dsimp [t₀]; positivity
    have ht₁ : t₀ + h ≤ 1 := by
      have hj : ((j k 1 i : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T k 1 := by
        exact_mod_cast Nat.succ_le_of_lt (j k 1 i).isLt
      dsimp [t₀, h, duration]
      rw [show (((j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ T k 1 + ((2 : ℝ) ^ T k 1)⁻¹) =
        (((j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k 1 by ring]
      exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ T k 1)).mpr hj
    have hgood : ∀ᵐ q ∂μ, q.2 ∈ Set.Icc t₀ (t₀ + h) ∧
        (∀ e, |q.1.2 e| ≤ H k) ∧
        (∀ s ∈ Set.Icc t₀ (t₀ + h), ∀ e,
          |(quadraticBase q.1.2 s e - z₀ e) / h| ≤ H k) ∧
        ∀ s ∈ Set.Icc t₀ (t₀ + h),
          |quadraticHidden q.1.2 s - eval (fun e => (quadraticBase q.1.2 s e - z₀ e) / h) p| ≤
            H k * N k ^ (-1 - c) := by
      filter_upwards [htime, haep, hbox, hfit] with q hqt hqa hqb hqf
      refine ⟨hqt, hqa, ?_, ?_⟩
      · simpa only [← hinterval, interval, quadraticBase] using hqb
      · simpa only [← hinterval, interval, quadraticBase, quadraticHidden, c] using hqf
    have hcondB := (hpalette B hBrange.1 hBrange.2).2
    have hcoarse := (hpalette r hrrange.1 hrrange.2).1
    have hcond : ∀ (q : Fin 3 → ℤ) (b : ℤ),
        μ {p | Submission.Obl.k4_matching_endpoint_volume.gridTag (N k ^ (-B))
          (quadraticPhysical p.1.2 p.2) = q ∧ p.1.2 1 ∈ scalarVelocityBin (N k ^ (-B)) b} ≤
          ENNReal.ofReal (L k) *
            μ {p | Submission.Obl.k4_matching_endpoint_volume.gridTag (N k ^ (-B))
              (quadraticPhysical p.1.2 p.2) = q} *
              π k (γ k 1 i) (scalarVelocityBin (N k ^ (-B)) b) := by
      intro q b
      apply (hcondB q b).trans
      exact mul_le_mul (mul_le_mul (ENNReal.ofReal_le_ofReal hHL') le_rfl bot_le bot_le)
        le_rfl bot_le bot_le
    have hsmall : 5 * (H k * N k ^ (-S * r)) ≤ (L k)⁻¹ / 8 := by
      have h40 : 40 * H k * L k ≤ N k ^ (S * r) := by
        calc
          _ ≤ 40 * L k ^ 2 := by nlinarith
          _ ≤ _ := hang.le
      have he : (L k)⁻¹ / 8 = 1 / (8 * L k) := by field_simp
      rw [show -S * r = -(S * r) by ring, Real.rpow_neg hNpos.le, he]
      apply (le_div_iff₀ (by positivity : 0 < 8 * L k)).mpr
      calc
        _ = (40 * H k * L k) / N k ^ (S * r) := by ring
        _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hNpos _)).mpr h40
    let η : ℝ := 1 / (256 * H k ^ 4 * L k ^ 4)
    have hη : 0 < η := by dsimp [η]; positivity
    have hη1 : η ≤ 1 := by
      have hden : 1 ≤ 256 * H k ^ 4 * L k ^ 4 := by
        have h1 := one_le_pow₀ (hH.1 k) (n := 4)
        have h2 := one_le_pow₀ (hL k) (n := 4)
        nlinarith
      exact (one_div_le_one_div_of_le zero_lt_one hden).trans_eq (one_div_one)
    have hξ₀H : N k ^ (-Z) ≤ H k := by
      calc
        _ ≤ N k ^ 0 := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = 1 := Real.rpow_zero _
        _ ≤ _ := hH.1 k
    have hξᵥL : N k ^ (-B) ≤ L k / 2 := by
      calc
        _ ≤ N k ^ 0 := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = 1 := Real.rpow_zero _
        _ ≤ _ := by linarith [hH.1 k]
    have hξδ : N k ^ (-B) ≤ N k ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hδ1 : N k ^ (-r) ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hN1 (neg_nonpos.mpr hr.le)
    have hKL : L k ≤ L k / N k ^ (-r) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)).mpr
      nlinarith
    have hsep : (L k / N k ^ (-r))⁻¹ ≤ N k ^ (-r) := by
      rw [inv_div]
      exact div_le_self (Real.rpow_nonneg hNpos.le _) (hL k)
    have hbase : ∀ q : Fin 2 → ℤ,
        μ {p | baseGridTag 0 (N k ^ (-Z))
          (fun e => (quadraticBase p.1.2 p.2 e - z₀ e) / h) = q} ≤
          ENNReal.ofReal (H k * m) * ENNReal.ofReal ((N k ^ (-Z)) ^ 2) := by
      intro q
      have hg := hgrid q
      have hνreal : ENNReal.ofReal amass = ν k (γ k 1 i) (A k 1 i) :=
        ENNReal.ofReal_toReal (measure_ne_top _ _)
      have hpow : N k ^ (-2 * Z) = (N k ^ (-Z)) ^ 2 := by
        rw [← Real.rpow_natCast (N k ^ (-Z)) 2, ← Real.rpow_mul hNpos.le]
        congr 1
        ring
      rw [← hνreal, ← ENNReal.ofReal_mul (by positivity)] at hg
      simp only [baseGridTag, sub_zero]
      apply hg.trans_eq
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [m]
      rw [hpow]
      ring
    have hbudget : (4 * H k) ^ 2 * (H k * m) * η ≤
        ((L k)⁻¹ / 2) ^ 4 * (μ Set.univ).toReal :=
      packet_recovery_witness_budget hHpos hLpos hmassreal
    obtain ⟨Q, hQ, hQcoeff, hQfit⟩ := hfinite ((ℕ × (Fin 5 → ℝ)) × ℝ) μ (π k (γ k 1 i))
      (fun p => p.1.2) Prod.snd p z₀ (H k) (L k) h t₀ (H k * N k ^ (-1 - c))
      (N k ^ (-Z)) (N k ^ (-B)) (N k ^ (-r)) (L k / N k ^ (-r)) (H k * m)
      (H k * N k ^ (-S * r)) η
      (by fun_prop) measurable_snd hp hpcoeff (hH.1 k) hHL hCaL hh hh1 ht₀ ht₁ hz₀
      hzbound (by positivity) (by positivity) hξ₀H (by positivity) hξᵥL (by positivity) hξδ
      hKL hsep (by positivity) (by positivity) hη hη1 hμpos hgood hcond hcoarse hsmall hbase hbudget
    have herror := packet_recovery_error_le D hN1 (hH.1 k) hHL' hh hscale hκ1 hc1 hZ hB hr.le
      hC₀.le hC₁.le hCₜ.le
    have hfinalerror : H k * N k ^ (-1 - c) +
        C₀ * (L k / N k ^ (-r)) ^ 18 * (16 * ((D : ℝ) + 1) / η) ^ (2 * D) *
          (Cₜ * H k ^ 3 * (H k * N k ^ (-1 - c)) + C₁ * L k ^ (2 * D + 4) *
            (N k ^ (-Z) / (4 * H k) + N k ^ (-B) / (4 * H k * h) + N k ^ (-B))) ≤
        G k * N k ^ δ * N k ^ (-1 - c) := by
      apply herror.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hGloss (Real.rpow_le_rpow_of_exponent_le hN1 hrδ)
          (Real.rpow_nonneg hNpos.le _) (zero_le_one.trans (hG k)))
        (Real.rpow_nonneg hNpos.le _)
    refine ⟨i, Q, hQ, ?_, ?_⟩
    · have hdiv : H k / h ≤ H k ^ 2 * N k ^ κ := by
        calc
          _ ≤ H k / (N k ^ (-κ) / H k) :=
            div_le_div_of_nonneg_left hHpos.le (by positivity) hscale
          _ = _ := by rw [Real.rpow_neg hNpos.le]; field_simp
      have hpow : (N k ^ κ) ^ 4 = N k ^ (4 * κ) := by
        rw [← Real.rpow_natCast (N k ^ κ) 4, ← Real.rpow_mul hNpos.le]
        congr 1
        ring
      intro b
      calc
        |Q.coeff b| ≤ Cq * L k * (H k / h) ^ 4 := hQcoeff b
        _ ≤ Cq * L k * (H k ^ 2 * N k ^ κ) ^ 4 := by gcongr
        _ = (Cq * L k * H k ^ 8) * N k ^ (4 * κ) := by rw [mul_pow, hpow]; ring
        _ ≤ (Cq * L k ^ 9) * N k ^ (4 * κ) := by
          convert mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHpos.le hHL' 8)
              (by positivity : 0 ≤ Cq * L k)) (Real.rpow_nonneg hNpos.le (4 * κ)) using 1 <;> ring
        _ ≤ G k * N k ^ (4 * κ) :=
          mul_le_mul_of_nonneg_right hGcoeff (Real.rpow_nonneg hNpos.le _)
    · have hevent : ∀ᵐ p ∂μ, p ∈ Fit k i Q (G k * N k ^ δ * N k ^ (-1 - c)) := by
        filter_upwards [hmembership, hQfit] with p hp hfit
        refine ⟨hp.1, hp.2, ?_⟩
        intro s hs
        exact (hfit s (by rwa [← hinterval])).trans hfinalerror
      have hret := original_mass_of_ae_event μ (law k i) hμρ _ hevent
      calc
        ENNReal.ofReal (duration k i * N k ^ (-d * c) / G k) * currentMass k i ≤
            ENNReal.ofReal (h * N k ^ (-d * c) / H k) * ν k (γ k 1 i) (A k 1 i) := by
          gcongr
        _ ≤ μ Set.univ := hmass
        _ ≤ _ := hret
  have himprove := eventual_absorb_subpower_quadratic_packets N G (fun k => n k 1)
    duration currentMass law Fit (4 * κ) d c hN hG hGsub
    (fun k i => by dsimp [duration]; positivity)
    (by intro k i Q E E' hEE p hp; exact ⟨hp.1, hp.2.1, fun t ht => (hp.2.2 t ht).trans hEE⟩) hcert
  let R : ℝ := 10 + c + c⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hc]
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRinv : R⁻¹ ≤ c := by
    apply (inv_le_iff_one_le_mul₀ hRpos).mpr
    have he : c * R = 10 * c + c ^ 2 + 1 := by
      dsimp [R]
      rw [mul_add, mul_inv_cancel₀ hc.ne']
      ring
    rw [he]
    nlinarith
  refine ⟨R, hR, ?_⟩
  intro ε hε
  apply Filter.Eventually.frequently
  filter_upwards [himprove ε hε] with k hk
  rcases hk with ⟨i, Q, hQ, hcoeff, hmass⟩
  refine ⟨1, c, i, Q, inv_le_one_of_one_le₀ hR.le, hR.le, hRinv, ?_, hQ, ?_, ?_⟩
  · dsimp [R]; linarith [inv_pos.mpr hc]
  · intro b
    apply (hcoeff b).trans
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hN k])
      (by dsimp [R]; have hi := inv_pos.mpr hc; nlinarith)
  · simpa only [duration, currentMass, law, Fit, interval, quadraticHidden, quadraticBase,
      div_eq_mul_inv, mul_comm] using hmass

end
end Submission.Obl.k4_scalar_tangent_isotropic_improvement
