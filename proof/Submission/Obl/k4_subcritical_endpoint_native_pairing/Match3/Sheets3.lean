/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/Sheets3.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/Sheets3.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Quad3
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_subcritical_endpoint_native_pairing.MatchingInput

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Quadratic graphs as algebraic sheets, and matching for them

The complexification `q3C a` of a real three-variable quadratic is an entire function on `ℂ³`, real
on real points, satisfying the degree-two relation `X₃ − q3(a)(X₀, X₁, X₂) = 0`.  Feeding such
sheets to accepted o112 (`k4_local_algebraic_graph_matching`, from the frozen two-colour matching
premise) gives `match_quad3`: for coefficient vectors bounded by `3`, lists of size
`≤ N^(d+η)`, a probability pair law on base points of `EuclideanSpace ℝ (Fin 3)` with marginal
densities `≤ N^η π_i`, it is impossible that almost every pair has its base point in the ball of
radius `1/2`, values within `30/N` there, and coefficient vectors at distance `≥ 1`.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open MvPolynomial MeasureTheory

/-- The real quadratic evaluated at a point of `EuclideanSpace ℝ (Fin 3)`. -/
def q3E (a : Fin 10 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ := q3 a (fun i => x i)

/-- Its complexification. -/
noncomputable def q3C (a : Fin 10 → ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  (a 0 : ℂ) + a 1 * z 0 + a 2 * z 1 + a 3 * z 2 + a 4 * z 0 ^ 2 + a 5 * z 1 ^ 2 +
    a 6 * z 2 ^ 2 + a 7 * (z 0 * z 1) + a 8 * (z 0 * z 2) + a 9 * (z 1 * z 2)

/-- The defining degree-two relation `X₃ − q3(a)`. -/
noncomputable def P3 (a : Fin 10 → ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 - (C (a 0 : ℂ) + C (a 1 : ℂ) * X 0 + C (a 2 : ℂ) * X 1 + C (a 3 : ℂ) * X 2 +
    C (a 4 : ℂ) * X 0 ^ 2 + C (a 5 : ℂ) * X 1 ^ 2 + C (a 6 : ℂ) * X 2 ^ 2 +
    C (a 7 : ℂ) * (X 0 * X 1) + C (a 8 : ℂ) * (X 0 * X 2) + C (a 9 : ℂ) * (X 1 * X 2))

/-- The real embedding used by o112. -/
noncomputable def emb3 (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

theorem q3C_emb (a : Fin 10 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    q3C a (emb3 x) = (q3E a x : ℂ) := by
  simp [q3C, q3E, q3, emb3]

theorem q3C_toLp (a : Fin 10 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    q3C a (WithLp.toLp 2 fun i => ((x.ofLp i : ℝ) : ℂ)) = (q3E a x : ℂ) := q3C_emb a x

theorem eval_P3 (a : Fin 10 → ℝ) (z : EuclideanSpace ℂ (Fin 3)) (w : ℂ) :
    eval (Fin.snoc (fun j : Fin 3 => z j) w) (P3 a) = w - q3C a z := by
  simp [P3, q3C, Fin.snoc]
  rfl

theorem P3_relation (a : Fin 10 → ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    eval (Fin.snoc (fun j : Fin 3 => z j) (q3C a z)) (P3 a) = 0 := by
  rw [eval_P3]; ring

theorem P3_ne_zero (a : Fin 10 → ℝ) : P3 a ≠ 0 := by
  intro h
  have := eval_P3 a 0 (q3C a 0 + 1)
  rw [h, map_zero] at this
  have : (0 : ℂ) = 1 := by rw [this]; ring
  exact zero_ne_one this

theorem P3_totalDegree (a : Fin 10 → ℝ) : (P3 a).totalDegree ≤ 2 := by
  have hX : ∀ i : Fin 4, (X i : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 := fun i => by
    rw [totalDegree_X]; norm_num
  have hCX : ∀ (c : ℂ) (i : Fin 4), (C c * X i : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 :=
    fun c i => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X]; norm_num)
  have hCXX : ∀ (c : ℂ) (i j : Fin 4),
      (C c * (X i * X j) : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 :=
    fun c i j => (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X]))
  have hCX2 : ∀ (c : ℂ) (i : Fin 4), (C c * X i ^ 2 : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 :=
    fun c i => by rw [sq]; exact hCXX c i i
  have hadd : ∀ p q : MvPolynomial (Fin 4) ℂ, p.totalDegree ≤ 2 → q.totalDegree ≤ 2 →
      (p + q).totalDegree ≤ 2 := fun p q hp hq => (totalDegree_add _ _).trans (max_le hp hq)
  have hC0 : (C (a 0 : ℂ) : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 := by
    rw [totalDegree_C]; norm_num
  unfold P3
  exact (totalDegree_sub _ _).trans (max_le (hX 3)
    (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _
      (hadd _ _ hC0 (hCX _ _)) (hCX _ _)) (hCX _ _)) (hCX2 _ _)) (hCX2 _ _)) (hCX2 _ _))
      (hCXX _ _ _)) (hCXX _ _ _)) (hCXX _ _ _)))

theorem q3C_differentiable (a : Fin 10 → ℝ) : Differentiable ℂ (q3C a) := by
  unfold q3C; fun_prop

theorem q3E_sub (a b : Fin 10 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    q3E (a - b) x = q3E a x - q3E b x := q3_sub a b _

/-- Coordinates of a point of the closed unit ball are bounded by one. -/
theorem abs_coord_le_one {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 1) (i : Fin 3) :
    |x i| ≤ 1 := by
  have h := PiLp.norm_apply_le (p := 2) x i
  exact (Real.norm_eq_abs _ ▸ h).trans hx

/-- The sample points as points of `EuclideanSpace ℝ (Fin 3)`, of norm `≤ 1/2`. -/
noncomputable def samplesE (k : Fin 10) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (samples k)

theorem norm_samplesE_le (k : Fin 10) : ‖samplesE k‖ ≤ 1 / 2 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(samplesE k) i‖ ^ 2 ≤ (1 / 4) ^ 2 := fun i => by
    rw [Real.norm_eq_abs, sq_abs]
    have := samples_norm k i
    simp only [samplesE]
    nlinarith [abs_nonneg (samples k i), sq_abs (samples k i)]
  calc Real.sqrt (∑ i, ‖(samplesE k) i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin 3, (1 / 4 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
    _ ≤ 1 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num

theorem q3E_samplesE (a : Fin 10 → ℝ) (k : Fin 10) : q3E a (samplesE k) = q3 a (samples k) := by
  simp [q3E, samplesE]

/-- **Matching for three-variable quadratic graphs**, from o112. -/
theorem match_quad3 (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (n₁ n₂ : ℕ) (a₁ : Fin n₁ → Fin 10 → ℝ) (a₂ : Fin n₂ → Fin 10 → ℝ)
      (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
      (μ : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))),
      (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ 3) → (∀ j k, |a₂ j k| ≤ 3) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume U) →
      (∀ (j : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume U) →
      ¬ (∀ᵐ p ∂μ, ‖p.2‖ ≤ 1 / 2 ∧
          |q3E (a₁ p.1.1) p.2 - q3E (a₂ p.1.2) p.2| ≤ 30 / N ∧
          1 ≤ cnorm3 (a₁ p.1.1 - a₂ p.1.2)) := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hloc⟩ := Submission.k4_local_algebraic_graph_matching hM 2 d hd0 hd1
  set ε := min ε₀ (1 / 4) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  -- a threshold making `30 N^(-2ε) ≤ 1/128`
  set N₁ : ℝ := (3840 : ℝ) ^ (1 / (2 * ε)) with hN₁
  refine ⟨ε, hε, max (max R₀ N₁) 2, le_max_right _ _, ?_⟩
  intro N hN n₁ n₂ a₁ a₂ π₁ π₂ μ hn₁ hn₂ ha₁ ha₂ hπ₁ hπ₂ hs₁ hs₂ hμ hd₁' hd₂' hall
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by linarith
  have hNR : R₀ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNN₁ : N₁ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hpow : ∀ x y : ℝ, N ^ x * N ^ y = N ^ (x + y) := fun x y => (Real.rpow_add hNpos x y).symm
  have hsmall : 30 * N ^ (-ε) * N ^ (-ε) ≤ 1 / 128 := by
    have h1 : (3840 : ℝ) ≤ N ^ (2 * ε) := by
      calc (3840 : ℝ) = N₁ ^ (2 * ε) := by
            rw [hN₁, ← Real.rpow_mul (by norm_num)]; field_simp; simp
        _ ≤ N ^ (2 * ε) := Real.rpow_le_rpow (by positivity) hNN₁ (by positivity)
    have h2 : N ^ (-ε) * N ^ (-ε) = (N ^ (2 * ε))⁻¹ := by
      rw [hpow, ← Real.rpow_neg hNpos.le]; ring_nf
    rw [mul_assoc, h2]
    have h3 : 0 < N ^ (2 * ε) := Real.rpow_pos_of_pos hNpos _
    rw [← div_eq_mul_inv, div_le_iff₀ h3]
    linarith
  have hM : (0 : ℝ) < 30 * N ^ (-ε) := by positivity
  have hcont := hloc N (30 * N ^ (-ε)) ε hNR hM hε hεε₀ n₁ n₂ (fun i => q3C (a₁ i))
    (fun j => q3C (a₂ j)) (fun i => P3 (a₁ i)) (fun j => P3 (a₂ j)) (fun _ => 0) π₁ π₂ μ
  simp only at hcont
  apply hcont
  · exact hn₁.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) le_rfl)
  · exact hn₂.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) le_rfl)
  · intro i
    refine ⟨P3_ne_zero _, P3_totalDegree _, (q3C_differentiable _).differentiableOn,
      fun z _ => P3_relation _ z, fun x hx => ?_⟩
    have he : q3C (a₁ i) (WithLp.toLp 2 fun i => (x i : ℂ)) = (q3E (a₁ i) x : ℂ) := q3C_emb _ x
    rw [he]
    refine ⟨by simp, ?_⟩
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
    calc |q3E (a₁ i) x| ≤ 10 * 3 := abs_q3_le (ha₁ i) (fun k => abs_coord_le_one hx k)
      _ = 30 * N ^ (-ε) * N ^ ε := by rw [mul_assoc, hpow]; simp; norm_num
  · intro j
    refine ⟨P3_ne_zero _, P3_totalDegree _, (q3C_differentiable _).differentiableOn,
      fun z _ => P3_relation _ z, fun x hx => ?_⟩
    have he : q3C (a₂ j) (WithLp.toLp 2 fun i => (x i : ℂ)) = (q3E (a₂ j) x : ℂ) := q3C_emb _ x
    rw [he]
    refine ⟨by simp, ?_⟩
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
    calc |q3E (a₂ j) x| ≤ 10 * 3 := abs_q3_le (ha₂ j) (fun k => abs_coord_le_one hx k)
      _ = 30 * N ^ (-ε) * N ^ ε := by rw [mul_assoc, hpow]; simp; norm_num
  · exact hπ₁
  · exact hπ₂
  · exact hs₁
  · exact hs₂
  · rw [measure_univ]
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by linarith))
  · rw [measure_univ]
  · intro i U hU
    exact (hd₁' i U hU)
  · intro j U hU
    exact (hd₂' j U hU)
  · refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hall] with p hp
    rw [Set.mem_compl_iff, not_not]
    obtain ⟨hpx, hclose, hfar⟩ := hp
    refine ⟨hpx, ?_, ?_⟩
    · rw [q3C_toLp, q3C_toLp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      calc |q3E (a₁ p.1.1) p.2 - q3E (a₂ p.1.2) p.2| ≤ 30 / N := hclose
        _ = 30 * N ^ (-ε) * N ^ (-1 + ε) := by
            rw [mul_assoc, hpow, show -ε + (-1 + ε) = (-1 : ℝ) by ring, Real.rpow_neg_one]
            ring
    · obtain ⟨k, hk⟩ := exists_sample_large hfar
      refine ⟨samplesE k, norm_samplesE_le k, ?_⟩
      rw [q3C_toLp, q3C_toLp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        ← q3E_sub, q3E_samplesE]
      calc 30 * N ^ (-ε) * N ^ (-ε) ≤ 1 / 128 := hsmall
        _ ≤ |q3 (a₁ p.1.1 - a₂ p.1.2) (samples k)| := hk

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open MeasureTheory

/-- A bijection between discrete measurable spaces is a measurable equivalence (as in o227/x0788
`MatchCor.discreteEquiv`). -/
def discreteEquiv3 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] (e : α ≃ β) : α ≃ᵐ β where
  toEquiv := e
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

/-- `match_quad3` for arbitrary finite index types (transport to `Fin` as in o227/x0788
`MatchCor.match_quad`). -/
theorem match_quad3_fintype (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (a₁ : ι₁ → Fin 10 → ℝ) (a₂ : ι₂ → Fin 10 → ℝ) (π₁ : ι₁ → ℝ) (π₂ : ι₂ → ℝ)
      (μ : Measure ((ι₁ × ι₂) × E3)),
      (Fintype.card ι₁ : ℝ) ≤ N ^ (d + η) → (Fintype.card ι₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ 3) → (∀ j k, |a₂ j k| ≤ 3) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ i (U : Set E3), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume U) →
      (∀ j (U : Set E3), MeasurableSet U →
        μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume U) →
      ¬ (∀ᵐ p ∂μ, ‖p.2‖ ≤ 1 / 2 ∧
          |q3E (a₁ p.1.1) p.2 - q3E (a₂ p.1.2) p.2| ≤ 30 / N ∧
          1 ≤ cnorm3 (a₁ p.1.1 - a₂ p.1.2)) := by
  obtain ⟨η, hη, N₀, hN₀, H⟩ := match_quad3 hM hd0 hd1
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN ι₁ ι₂ _ _ _ _ _ _ a₁ a₂ π₁ π₂ μ hc₁ hc₂ ha₁ ha₂ hπ₁ hπ₂ hs₁ hs₂ hμ hm₁ hm₂ hbad
  let e₁ := discreteEquiv3 (Fintype.equivFin ι₁)
  let e₂ := discreteEquiv3 (Fintype.equivFin ι₂)
  let Φ : (ι₁ × ι₂) × E3 ≃ᵐ (Fin (Fintype.card ι₁) × Fin (Fintype.card ι₂)) × E3 :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e₁ e₂) (MeasurableEquiv.refl E3)
  have hΦ : ∀ p : (ι₁ × ι₂) × E3, Φ p = ((e₁ p.1.1, e₂ p.1.2), p.2) := fun p => rfl
  have key := H N hN (Fintype.card ι₁) (Fintype.card ι₂) (fun i => a₁ (e₁.symm i))
    (fun j => a₂ (e₂.symm j)) (fun i => π₁ (e₁.symm i)) (fun j => π₂ (e₂.symm j)) (μ.map Φ)
    hc₁ hc₂ (fun i k => ha₁ _ k) (fun j k => ha₂ _ k) (fun i => hπ₁ _) (fun j => hπ₂ _)
    (by rw [← hs₁]; exact Equiv.sum_comp e₁.symm.toEquiv π₁)
    (by rw [← hs₂]; exact Equiv.sum_comp e₂.symm.toEquiv π₂)
    ⟨by rw [MeasurableEquiv.map_apply]; simp⟩
    (fun i U hU => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.1 = i ∧ p.2 ∈ U} = {p | p.1.1 = e₁.symm i ∧ p.2 ∈ U} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₁ _ U hU)
    (fun j U hU => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.2 = j ∧ p.2 ∈ U} = {p | p.1.2 = e₂.symm j ∧ p.2 ∈ U} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₂ _ U hU)
  apply key
  rw [ae_iff, MeasurableEquiv.map_apply]
  refine measure_mono_null ?_ (ae_iff.mp hbad)
  intro p hpS
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ, MeasurableEquiv.symm_apply_apply] at hpS ⊢
  exact hpS

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
