import Submission.Obl.k4_scalar_normalized_exact_refinement.Profile
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity

/-!
# Joint densities and the angular cap of a Refinement

* `joint_density_exists`: joint laws of a raw pure family have densities, since their pure
  marginal at the terminal depth has one.
* `RefData.angular_cap`: the angular clause of a Refinement `q` of an exact `p`, with the same
  `S`, at every angular depth `u ≤ U_q ≤ U_p`. In a world with a point that is typical and
  satisfies the terminal lower comparison, the world factor is at most
  `N^(f_p(L_p) - f_q(L_q) + 4τ')`, and the original angular cap at depth `u - η` transfers.
  The remaining worlds lie inside the two exceptional sets.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {p q : Code} {r b h : ℝ}

/-- Joint laws of a raw pure family have densities against the joint reference. -/
theorem joint_density_exists (hqr : Spec.RawScalar q) (hqp : Spec.PureProfile q) :
    ∃ a : (k : ℕ) → Fin (q.1 k) → ℝ → Joint → ℝ≥0∞, ∀ k i u,
      Measurable (a k i u) ∧
        (q.mu k i).map (aug (q.N k) q.L u) = JointRef.withDensity (a k i u) := by
  refine ⟨fun k i u => ((q.mu k i).map (aug (q.N k) q.L u)).rnDeriv JointRef, ?_⟩
  intro k i u
  refine ⟨Measure.measurable_rnDeriv _ _, ?_⟩
  have := mu_isFinite hqr k i
  have hL0 : 0 ≤ q.L := (RawScalar.L_pos hqr).le
  have hlaw := PureProfile.law hqp k i q.L hL0 le_rfl
  have hfst : ((q.mu k i).map (aug (q.N k) q.L u)).map Prod.fst ≪ BaseRef := by
    rw [Measure.map_map measurable_fst (measurable_aug _ _ _)]
    have : Prod.fst ∘ aug (q.N k) q.L u = obs (q.N k) q.L := rfl
    rw [this, hlaw.2]
    exact withDensity_absolutelyContinuous _ _
  have hac := k4_dyadic_crop_affine_laws.Framework.absolutelyContinuous_prod_count_of_fst
    ((q.mu k i).map (aug (q.N k) q.L u)) BaseRef hfst
  exact (Measure.withDensity_rnDeriv_eq _ _ hac).symm

/-- Three power-small quantities have a power-small sum. -/
lemma powerSmall_add3 {N : ℕ → ℝ} (hNt : Tendsto N atTop atTop) (hN1 : ∀ k, 1 ≤ N k)
    {a₁ a₂ a₃ : ℕ → ℝ≥0∞} {c₁ c₂ c₃ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁ : ∀ᶠ k in atTop, a₁ k ≤ ENNReal.ofReal (N k ^ (-c₁)))
    (h₂ : ∀ᶠ k in atTop, a₂ k ≤ ENNReal.ofReal (N k ^ (-c₂)))
    (h₃ : ∀ᶠ k in atTop, a₃ k ≤ ENNReal.ofReal (N k ^ (-c₃))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, a₁ k + a₂ k + a₃ k ≤ ENNReal.ofReal (N k ^ (-c)) := by
  set c := min c₁ (min c₂ c₃)
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂ hc₃)
  refine ⟨c / 2, by positivity, ?_⟩
  apply powerSmall_of_factor hNt hN1 (tendsto_const_nhds (x := (0 : ℝ))) 3 (by norm_num) hc
  filter_upwards [h₁, h₂, h₃] with k hk₁ hk₂ hk₃
  have hm : ∀ c' : ℝ, c ≤ c' → ENNReal.ofReal (N k ^ (-c')) ≤ ENNReal.ofReal (N k ^ (-c)) :=
    fun c' hc' => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith))
  have e1 := hk₁.trans (hm c₁ (min_le_left _ _))
  have e2 := hk₂.trans (hm c₂ ((min_le_right _ _).trans (min_le_left _ _)))
  have e3 := hk₃.trans (hm c₃ ((min_le_right _ _).trans (min_le_right _ _)))
  rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  calc a₁ k + a₂ k + a₃ k ≤ ENNReal.ofReal (N k ^ (-c)) + ENNReal.ofReal (N k ^ (-c)) +
      ENNReal.ofReal (N k ^ (-c)) := by gcongr
    _ = 3 * ENNReal.ofReal (N k ^ (-c)) := by ring

namespace RefData

variable (R : RefData p q r b h)

include R in
/-- The angular clause of a Refinement. -/
theorem angular_cap (hp : Spec.Exact p) (hqr : Spec.RawScalar q) (hqp : Spec.PureProfile q)
    (hr : 0 ≤ r) (hbL : b ≤ p.L) (hLq : q.L = p.L - r) (hS : q.S = p.S) (hU : q.U ≤ p.U)
    (a : (k : ℕ) → Fin (q.1 k) → ℝ → Joint → ℝ≥0∞)
    (ha : ∀ k i u, 0 < u → u ≤ q.U → Measurable (a k i u) ∧
      (q.mu k i).map (aug (q.N k) q.L u) = JointRef.withDensity (a k i u))
    (u τ : ℝ) (hu : 0 < u) (huU : u ≤ q.U) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i {z | ENNReal.ofReal (q.N k ^
        (-q.f q.L - q.S * u + τ)) < a k i u (aug (q.N k) q.L u z)} ≤
        ENNReal.ofReal (q.N k ^ (-c)) := by
  have hraw := Exact.raw hp
  have hpp := Exact.pure hp
  have hSp := RawScalar.S_pos hraw
  have hNq : ∀ k, 2 ≤ q.N k := RawScalar.N_ge hqr
  have hN1 : ∀ k, 1 ≤ q.N k := fun k => by linarith [hNq k]
  have hL0 : 0 ≤ q.L := (RawScalar.L_pos hqr).le
  have hrs : r + q.L = p.L := by linarith
  set τ' := τ / 8 with hτ'def
  have hτ' : 0 < τ' := by positivity
  set η := min (u / 2) (τ' / p.S) with hηdef
  have hη : 0 < η := lt_min (by linarith) (div_pos hτ' hSp)
  have hηu : η ≤ u / 2 := min_le_left _ _
  have hηS : p.S * η ≤ τ' := by
    have := min_le_right (u / 2) (τ' / p.S)
    calc p.S * η ≤ p.S * (τ' / p.S) := by gcongr
      _ = τ' := by field_simp
  set u' := u - η with hu'def
  have hu' : 0 < u' := by linarith
  have hu'U : u' ≤ p.U := by linarith
  -- original estimates
  obtain ⟨c₁, hc₁, hpL⟩ := PureProfile.typical hpp p.L τ' (RawScalar.L_pos hraw).le le_rfl hτ'
  obtain ⟨c₂, hc₂, hpA⟩ := Exact.angular hp u' τ' hu' hu'U hτ'
  obtain ⟨c₃, hc₃, hqL⟩ := PureProfile.typical hqp q.L τ' hL0 le_rfl hτ'
  -- the three exceptional families
  let Y1 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | q.ρ k i q.L (obs (q.N k) q.L z) < ENNReal.ofReal (q.N k ^ (-q.f q.L - τ')) ∨
      ENNReal.ofReal (q.N k ^ (-q.f q.L + τ')) < q.ρ k i q.L (obs (q.N k) q.L z)}
  let Y2 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | q.ρ k i q.L (obs (q.N k) q.L z) < ENNReal.ofReal (R.lam k i) *
      (ENNReal.ofReal (q.N k ^ (-τ')) * (ENNReal.ofReal (q.N k ^ (-τ')) *
        ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + q.L) - τ'))))}
  let Y3 : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | ENNReal.ofReal (R.lam k i) *
      (8 * ENNReal.ofReal (p.N (R.φ k) ^ (-p.f p.L - p.S * u' + τ'))) <
        a k i u (aug (q.N k) q.L u z)}
  let Bad : (k : ℕ) → Fin (q.1 k) → Set Inc := fun k i =>
    {z | ENNReal.ofReal (q.N k ^ (-q.f q.L - q.S * u + τ)) < a k i u (aug (q.N k) q.L u z)}
  -- power-small weighted masses of the three families
  have hW2 : ∀ᶠ k in atTop, ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y2 k i) ≤
      ENNReal.ofReal (q.N k ^ (-(min τ' c₁ / 2))) := by
    have hε2 : Tendsto (fun k => 2 * R.ε k) atTop (nhds 0) := by
      simpa using R.ε_lim.const_mul 2
    apply powerSmall_of_factor (RawScalar.N_tendsto hqr) hN1 hε2 8 (by norm_num)
      (lt_min hτ' hc₁)
    filter_upwards [R.along hpL] with k hk
    have hNpos : 0 < q.N k := by linarith [hNq k]
    have he : 0 ≤ R.ε k := (R.ε_pos k).le
    have hP : ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a
        {z | p.ρ (R.φ k) a (r + q.L) (obs (p.N (R.φ k)) (r + q.L) z) <
          ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + q.L) - τ'))} ≤
        ENNReal.ofReal (q.N k ^ (-c₁)) := by
      refine le_trans ?_ hk
      rw [hrs]
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul' le_rfl (measure_mono fun z hz => Or.inl hz)
    calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y2 k i)
        ≤ ENNReal.ofReal (R.Z k)⁻¹ * (4 * ENNReal.ofReal (q.N k ^ (-τ')) +
          2 * ENNReal.ofReal (p.N (R.φ k) ^ R.ε k) * ENNReal.ofReal (q.N k ^ (-τ')) +
          2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a
            {z | p.ρ (R.φ k) a (r + q.L) (obs (p.N (R.φ k)) (r + q.L) z) <
              ENNReal.ofReal (p.N (R.φ k) ^ (-p.f (r + q.L) - τ'))}) :=
          R.weighted_lower hp hqp hLq hr k q.L hL0 le_rfl (by linarith) _ _ _
      _ ≤ ENNReal.ofReal (q.N k ^ R.ε k) *
          (ENNReal.ofReal (q.N k ^ R.ε k) * (8 * ENNReal.ofReal (q.N k ^ (-(min τ' c₁))))) := by
          refine mul_le_mul' (R.Z_inv_le hraw k) ?_
          rw [← R.qN_eq k]
          exact lower_shape (R.qN_eq k ▸ hN1 k) he _ (R.qN_eq k ▸ hP)
      _ = ENNReal.ofReal (q.N k ^ (2 * R.ε k)) * (8 * ENNReal.ofReal (q.N k ^ (-(min τ' c₁)))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _),
            ← Real.rpow_add hNpos]
          ring_nf
  have hεη : ∀ᶠ k in atTop, R.ε k ≤ η := R.ε_lim.eventually (ge_mem_nhds hη)
  have hW3 : ∀ᶠ k in atTop, ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y3 k i) ≤
      ENNReal.ofReal (q.N k ^ (-(c₂ / 2))) := by
    apply powerSmall_of_factor (RawScalar.N_tendsto hqr) hN1 R.ε_lim 16 (by norm_num) hc₂
    filter_upwards [R.along hpA, hεη] with k hk hkε
    have hα : ∀ i, R.J k i / R.dt k * p.N (R.φ k) ^ (-u) ≤ p.N (R.φ k) ^ (-u') := by
      intro i
      have hNp : 1 ≤ p.N (R.φ k) := by rw [← R.qN_eq k]; exact hN1 k
      have hNp0 : 0 < p.N (R.φ k) := by linarith
      have hJ := ChartData.J_le (R.chart k) i
      have hdt := R.dt_pos k
      have h1 : R.J k i / R.dt k ≤ p.N (R.φ k) ^ R.ε k := by
        rw [div_le_iff₀ hdt]
        calc R.J k i ≤ p.N (R.φ k) ^ R.ε k / (2 : ℝ) ^ R.T k := hJ
          _ = p.N (R.φ k) ^ R.ε k * R.dt k := by rw [dt, div_eq_mul_inv]
      calc R.J k i / R.dt k * p.N (R.φ k) ^ (-u) ≤ p.N (R.φ k) ^ R.ε k * p.N (R.φ k) ^ (-u) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNp0.le _)
        _ = p.N (R.φ k) ^ (R.ε k + -u) := (Real.rpow_add hNp0 _ _).symm
        _ ≤ p.N (R.φ k) ^ (-u') := Real.rpow_le_rpow_of_exponent_le hNp (by linarith)
    calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y3 k i)
        ≤ ENNReal.ofReal (R.Z k)⁻¹ * (16 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
          p.mu (R.φ k) a {z | ENNReal.ofReal (p.N (R.φ k) ^ (-p.f p.L - p.S * u' + τ')) <
            p.ρA (R.φ k) a u' (aug (p.N (R.φ k)) p.L u' z)}) :=
          R.weighted_angular hp hLq k u u' hu' hu'U hα (fun i => a k i u)
            (fun i => (ha k i u hu huU).1) (fun i => (ha k i u hu huU).2) _
      _ ≤ ENNReal.ofReal (q.N k ^ R.ε k) * (16 * ENNReal.ofReal (q.N k ^ (-c₂))) :=
          mul_le_mul' (R.Z_inv_le hraw k) (mul_le_mul' le_rfl hk)
  have hlarge : ∀ᶠ k in atTop, 8 ≤ q.N k ^ τ' :=
    ((tendsto_rpow_atTop hτ').comp (RawScalar.N_tendsto hqr)).eventually (eventually_ge_atTop 8)
  -- each world's bad angular mass is covered
  have hcover : ∀ᶠ k in atTop, ∀ i, q.mu k i (Bad k i) ≤
      q.mu k i (Y1 k i) + q.mu k i (Y2 k i) + q.mu k i (Y3 k i) := by
    filter_upwards [hlarge] with k hk8 i
    by_cases hgood : ∃ z₀, z₀ ∉ Y1 k i ∧ z₀ ∉ Y2 k i
    · obtain ⟨z₀, hz1, hz2⟩ := hgood
      simp only [Y1, Y2, mem_ofPred_eq, not_or, not_lt] at hz1 hz2
      rw [← R.qN_eq k] at hz2
      rw [hrs] at hz2
      set N := q.N k with hNdef
      have hN0 : 0 < N := by linarith [hNq k]
      have hlam := (R.lam_pos hraw k i).le
      -- the world factor
      have hfac : R.lam k i * N ^ (-p.f p.L - τ' - τ' - τ') ≤ N ^ (-q.f q.L + τ') := by
        have hh := hz2.trans hz1.2
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _), ← ENNReal.ofReal_mul hlam,
          ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hN0.le _)] at hh
        calc R.lam k i * N ^ (-p.f p.L - τ' - τ' - τ')
            = R.lam k i * (N ^ (-τ') * (N ^ (-τ') * N ^ (-p.f p.L - τ'))) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
              ring_nf
          _ ≤ _ := hh
      have hthr : R.lam k i * (8 * N ^ (-p.f p.L - p.S * u' + τ')) ≤
          N ^ (-q.f q.L - q.S * u + τ) := by
        have hpos : 0 < N ^ (p.f p.L + τ' + τ' + τ') := Real.rpow_pos_of_pos hN0 _
        have hlam' : R.lam k i ≤ N ^ (-q.f q.L + τ') * N ^ (p.f p.L + τ' + τ' + τ') := by
          have := mul_le_mul_of_nonneg_right hfac hpos.le
          rw [mul_assoc, ← Real.rpow_add hN0] at this
          simpa using this
        calc R.lam k i * (8 * N ^ (-p.f p.L - p.S * u' + τ'))
            ≤ N ^ (-q.f q.L + τ') * N ^ (p.f p.L + τ' + τ' + τ') *
                (N ^ τ' * N ^ (-p.f p.L - p.S * u' + τ')) := by
              gcongr
          _ = N ^ (-q.f q.L - p.S * u' + τ' * 6) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
              ring_nf
          _ ≤ N ^ (-q.f q.L - q.S * u + τ) := by
              apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
              rw [hS, hu'def]
              nlinarith
      have hsub : Bad k i ⊆ Y3 k i := by
        intro z hz
        simp only [Bad, Y3, mem_ofPred_eq] at hz ⊢
        rw [← R.qN_eq k]
        refine lt_of_le_of_lt ?_ hz
        rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul hlam]
        exact ENNReal.ofReal_le_ofReal hthr
      calc q.mu k i (Bad k i) ≤ q.mu k i (Y3 k i) := measure_mono hsub
        _ ≤ _ := le_add_self
    · push_neg at hgood
      calc q.mu k i (Bad k i) ≤ q.mu k i (Y1 k i ∪ Y2 k i) := by
            apply measure_mono
            intro z _
            by_cases h1 : z ∈ Y1 k i
            · exact Or.inl h1
            · exact Or.inr (hgood z h1)
        _ ≤ q.mu k i (Y1 k i) + q.mu k i (Y2 k i) := measure_union_le _ _
        _ ≤ _ := le_self_add
  obtain ⟨c, hc, hsum⟩ := powerSmall_add3 (RawScalar.N_tendsto hqr) hN1 hc₃ (by
      have := lt_min hτ' hc₁
      positivity) (by positivity : 0 < c₂ / 2) hqL hW2 hW3
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsum, hcover] with k hk hkc
  calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Bad k i)
      ≤ ∑ i, ENNReal.ofReal (q.ω k i) *
          (q.mu k i (Y1 k i) + q.mu k i (Y2 k i) + q.mu k i (Y3 k i)) := by
        gcongr with i
        exact hkc i
    _ = ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y1 k i) +
        ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y2 k i) +
        ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (Y3 k i) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ _ := hk

end RefData

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
