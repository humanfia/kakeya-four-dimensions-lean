import Submission.Obl.k4_scalar_true_terminal_lifting.LiftDefs

/-!
# Lifted chart: masses

The selected-law transport gives the masses of the lifted incidences; the normalized weights
give the weighted mass of the lifted chart as `Z` times the weighted mass of the q-chart, and
the parent chart gives `Z ≥ N ^ (-ε₁)`. Good parent worlds give the true floor.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A polynomial of total degree zero takes the same value at every point. -/
lemma msr_eval_eq_of_totalDegree_zero {m : ℕ} {P : MvPolynomial (Fin m) ℝ}
    (hP : P.totalDegree ≤ 0) (x y : Fin m → ℝ) :
    MvPolynomial.eval x P = MvPolynomial.eval y P := by
  have h0 : P.totalDegree = 0 := Nat.le_zero.mp hP
  rw [totalDegree_eq_zero_iff_eq_C.mp h0, eval_C, eval_C]

/-- A nonempty set with a format of degree zero is everything. -/
lemma msr_format_zero_univ {m : ℕ} {B : ℝ} {X : Set (Fin m → ℝ)} (hX : Format m B 0 X)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ X) (x : Fin m → ℝ) : x ∈ X := by
  unfold Format at hX
  obtain ⟨k', -, P, hP, S', hS'⟩ := hX
  rw [hS'] at hx₀ ⊢
  have heq : (fun j => SignType.sign (MvPolynomial.eval x (P j))) =
      (fun j => SignType.sign (MvPolynomial.eval x₀ (P j))) := by
    funext j
    rw [msr_eval_eq_of_totalDegree_zero (hP j).1 x x₀]
  show (fun j => SignType.sign (MvPolynomial.eval x (P j))) ∈ S'
  rw [heq]
  exact hx₀

/-- A chart with at least one piece forces `1 ≤ N`. -/
lemma msr_one_le_N {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool} {k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {Cs : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B r b h ε isTrue k T n γ j A Cs u v J P Λ) (hN : 0 < N p k)
    (i : Fin n) : 1 ≤ N p k := by
  unfold ChartData at hcd
  obtain ⟨-, h2, -, -, h5, h6, -⟩ := hcd
  obtain ⟨c1, -, -, -, -, -, -, c8, c9, -⟩ := h6 i
  by_contra hlt'
  have hlt : N p k < 1 := not_le.mp hlt'
  have hn : (1 : ℝ) ≤ N p k ^ (B : ℝ) := by
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    linarith
  have hB : B = 0 := by
    by_contra hB
    have hBpos : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
    have := Real.rpow_lt_one hN.le hlt hBpos
    linarith
  subst hB
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero c1.ne'
  have hzA : z.1 ∈ A i := ((h5 i) hz).2.1
  have hall : ∀ a : Fin 5 → ℝ, (z.1.1, a) ∈ A i := by
    intro a
    have hmem : z.1.2 ∈ {a | (z.1.1, a) ∈ A i} := by
      show (z.1.1, z.1.2) ∈ A i
      exact hzA
    exact msr_format_zero_univ (c9 z.1.1) hmem a
  have hbad : |N p k ^ ε + 1| ≤ N p k ^ ε := (c8 _ (hall (fun _ => N p k ^ ε + 1))).2 0
  have hpos : 0 < N p k ^ ε := Real.rpow_pos_of_pos hN ε
  rw [abs_of_pos (by linarith)] at hbad
  linarith

/-- Cancellation of a finite nonzero factor. -/
lemma msr_cancel {a c X : ENNReal} (h0 : c ≠ 0) (ht : c ≠ ⊤) :
    a * c * (c⁻¹ * X) = a * X := by
  rw [mul_assoc a c, ← mul_assoc c, ENNReal.mul_inv_cancel h0 ht, one_mul]

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)
variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

lemma ν_pos (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k)) :
    0 < ν p K (S.γ₁ i) (S.A₁ i) := by
  have h := S.hcd
  unfold ChartData at h
  obtain ⟨-, -, -, -, h5, h6, -⟩ := h
  have hpos := (h6 i).1
  have := hν (S.γ₁ i)
  have hle : mu p K (S.γ₁ i) (S.C₁ i) ≤
      ν p K (S.γ₁ i) (S.A₁ i) * ENNReal.ofReal (((2 : ℝ) ^ S.T₁)⁻¹) :=
    mu_le_of_subset p K (S.γ₁ i) (fun z hz => (h5 i hz).2)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at hle
  exact (lt_of_lt_of_le hpos hle).false

lemma msr_c_ne_zero (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k)) :
    ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i) ≠ 0 :=
  mul_ne_zero (ENNReal.ofReal_pos.mpr S.dt_pos).ne' (S.ν_pos hν i).ne'

lemma msr_c_ne_top (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k)) :
    ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i) ≠ ⊤ := by
  have := hν (S.γ₁ i)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

lemma mu_q_apply (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k))
    {T' : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hT' : MeasurableSet T') :
    mu q k i T' = (ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i))⁻¹ *
      mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' T') := by
  rw [S.mu_q_eq i, Measure.smul_apply, Measure.map_apply (S.measurable_Φ i) hT',
    Measure.restrict_apply (S.measurable_Φ i hT'), Set.inter_comm (S.Φ i ⁻¹' T'), smul_eq_mul]

lemma mu_p_eq (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k))
    {T' : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hT' : MeasurableSet T') :
    mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' T') =
      ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i) * mu q k i T' := by
  rw [S.mu_q_apply hν i hT', ← mul_assoc, ENNReal.mul_inv_cancel (S.msr_c_ne_zero hν i)
    (S.msr_c_ne_top hν i), one_mul]

lemma mass_q_eq (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hω : ∀ a, 0 ≤ ω p K a)
    (i : Fin (W q k)) {T' : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hT' : MeasurableSet T') :
    ENNReal.ofReal (ω q k i) * mu q k i T' =
      ENNReal.ofReal (ω p K (S.γ₁ i)) * ENNReal.ofReal S.Z⁻¹ *
        mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' T') := by
  have := hν (S.γ₁ i)
  have hω' : ENNReal.ofReal (ω q k i) =
      ENNReal.ofReal (ω p K (S.γ₁ i)) * ENNReal.ofReal S.Z⁻¹ *
        (ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i)) := by
    have h1 : 0 ≤ ω p K (S.γ₁ i) * S.dt := mul_nonneg (hω _) S.dt_pos.le
    have h2 : 0 ≤ ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal :=
      mul_nonneg h1 ENNReal.toReal_nonneg
    rw [S.ω_q_eq i, div_eq_mul_inv, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h1,
      ENNReal.ofReal_mul (hω _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    ring
  rw [S.mu_q_apply hν i hT', hω', msr_cancel (S.msr_c_ne_zero hν i) (S.msr_c_ne_top hν i)]

lemma Z_ge (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hω : ∀ a, 0 ≤ ω p K a)
    (hN : 0 < N p K) : N p K ^ (-S.ε₁) ≤ S.Z := by
  have h := S.hcd
  unfold ChartData at h
  obtain ⟨-, -, -, -, h5, -, -, -, -, h10⟩ := h
  rw [← ENNReal.ofReal_le_ofReal_iff S.Z_pos.le]
  refine h10.trans ?_
  have key : ∀ a : Fin (W p K),
      ENNReal.ofReal (ω p K a) * mu p K a {z | ∃ i, S.γ₁ i = a ∧ z ∈ S.C₁ i} ≤
      ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
        ENNReal.ofReal (ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal) := by
    intro a
    have hset : {z | ∃ i, S.γ₁ i = a ∧ z ∈ S.C₁ i} =
        ⋃ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a), S.C₁ i := by
      ext z
      simp
    rw [hset]
    calc ENNReal.ofReal (ω p K a) *
          mu p K a (⋃ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a), S.C₁ i)
        ≤ ENNReal.ofReal (ω p K a) *
            ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a), mu p K a (S.C₁ i) :=
          mul_le_mul' le_rfl (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
            ENNReal.ofReal (ω p K a) * mu p K a (S.C₁ i) := Finset.mul_sum _ _ _
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hia : S.γ₁ i = a := (Finset.mem_filter.mp hi).2
          subst hia
          have := hν (S.γ₁ i)
          have hle : mu p K (S.γ₁ i) (S.C₁ i) ≤ ν p K (S.γ₁ i) (S.A₁ i) * ENNReal.ofReal S.dt :=
            mu_le_of_subset p K (S.γ₁ i) (fun z hz => (h5 i hz).2)
          have h1 : 0 ≤ ω p K (S.γ₁ i) * S.dt := mul_nonneg (hω _) S.dt_pos.le
          rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (hω _),
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
          calc ENNReal.ofReal (ω p K (S.γ₁ i)) * mu p K (S.γ₁ i) (S.C₁ i)
              ≤ ENNReal.ofReal (ω p K (S.γ₁ i)) *
                  (ν p K (S.γ₁ i) (S.A₁ i) * ENNReal.ofReal S.dt) := mul_le_mul' le_rfl hle
            _ = _ := by ring
  calc ∑ a, ENNReal.ofReal (ω p K a) * mu p K a {z | ∃ i, S.γ₁ i = a ∧ z ∈ S.C₁ i}
      ≤ ∑ a, ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
          ENNReal.ofReal (ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal) :=
        Finset.sum_le_sum fun a _ => key a
    _ = ∑ i, ENNReal.ofReal (ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal) :=
        Finset.sum_fiberwise _ _ _
    _ = ENNReal.ofReal S.Z := by
        rw [RefStep.Z, ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (mul_nonneg (hω _) S.dt_pos.le) ENNReal.toReal_nonneg

lemma lift_mu_eq (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (d : Fin Q.n) :
    mu p K (S.γ₃ Q d) (S.C₃ Q d) =
      ENNReal.ofReal S.dt * ν p K (S.γ₁ (Q.γ d)) (S.A₁ (Q.γ d)) * mu q k (Q.γ d) (Q.C d) := by
  have h := Q.hcd
  unfold ChartData at h
  obtain ⟨-, -, h3, -⟩ := h
  exact S.mu_p_eq hν (Q.γ d) (h3 d).2

lemma lift_pos (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (d : Fin Q.n) :
    0 < mu p K (S.γ₃ Q d) (S.C₃ Q d) := by
  have h := Q.hcd
  unfold ChartData at h
  obtain ⟨-, -, -, -, -, h6, -⟩ := h
  rw [S.lift_mu_eq Q hν d]
  exact ENNReal.mul_pos (S.msr_c_ne_zero hν (Q.γ d)) (h6 d).1.ne'

lemma lift_floor (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hN : 0 < N p K) {δ ε₃ : ℝ}
    (hε₃ : ε₂ + δ ≤ ε₃) (d : Fin Q.n)
    (hgood : ENNReal.ofReal (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) ≤
      ν p K (S.γ₁ (Q.γ d)) (S.A₁ (Q.γ d))) :
    ENNReal.ofReal (N p K ^ (-f p (L p)) * S.J₃ Q d / (N p K ^ ε₃ * (2 : ℝ) ^ (S.T₁ + Q.T))) ≤
      mu p K (S.γ₃ Q d) (S.C₃ Q d) := by
  have hN1 : 1 ≤ N p K := msr_one_le_N S.hcd hN (Q.γ d)
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, -, -, -, hS6, -⟩ := hS
  have hQ := Q.hcd
  unfold ChartData at hQ
  obtain ⟨-, -, -, -, -, hQ6, -⟩ := hQ
  obtain ⟨-, hJ₁, -⟩ := hS6 (Q.γ d)
  obtain ⟨-, hJ₂, -, -, -, -, -, -, -, -, -, hfl⟩ := hQ6 d
  have hfl' := hfl rfl
  rw [S.hN] at hfl'
  have hreal : N p K ^ (-f p (L p)) * S.J₃ Q d / (N p K ^ ε₃ * (2 : ℝ) ^ (S.T₁ + Q.T)) ≤
      S.dt * (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) *
        (N p K ^ (-f q (L q)) * Q.J d / (N p K ^ ε₂ * (2 : ℝ) ^ Q.T)) := by
    have he : N p K ^ δ * N p K ^ ε₂ ≤ N p K ^ ε₃ := by
      rw [← Real.rpow_add hN]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have ha := Real.rpow_pos_of_pos hN (f p (L p))
    have hb := Real.rpow_pos_of_pos hN (f q (L q))
    have hd := Real.rpow_pos_of_pos hN δ
    have h2' := Real.rpow_pos_of_pos hN ε₂
    have h3' := Real.rpow_pos_of_pos hN ε₃
    have ht1 : (0 : ℝ) < 2 ^ S.T₁ := by positivity
    have ht2 : (0 : ℝ) < 2 ^ Q.T := by positivity
    rw [Real.rpow_sub hN, Real.rpow_sub hN, Real.rpow_neg hN.le, Real.rpow_neg hN.le, pow_add]
    unfold RefStep.J₃ RefStep.dt
    have hc : 0 ≤ S.J₁ (Q.γ d) * Q.J d /
        ((2 : ℝ) ^ S.T₁ * N p K ^ f p (L p) * 2 ^ Q.T) :=
      div_nonneg (mul_pos hJ₁ hJ₂).le (mul_pos (mul_pos ht1 ha) ht2).le
    calc (N p K ^ f p (L p))⁻¹ * (S.J₁ (Q.γ d) * Q.J d) /
          (N p K ^ ε₃ * (2 ^ S.T₁ * 2 ^ Q.T))
        = S.J₁ (Q.γ d) * Q.J d / ((2 : ℝ) ^ S.T₁ * N p K ^ f p (L p) * 2 ^ Q.T) /
            N p K ^ ε₃ := by
          field_simp
      _ ≤ S.J₁ (Q.γ d) * Q.J d / ((2 : ℝ) ^ S.T₁ * N p K ^ f p (L p) * 2 ^ Q.T) /
            (N p K ^ δ * N p K ^ ε₂) :=
          div_le_div_of_nonneg_left hc (mul_pos hd h2') he
      _ = ((2 : ℝ) ^ S.T₁)⁻¹ *
            (N p K ^ f q (L q) / N p K ^ f p (L p) / N p K ^ δ * S.J₁ (Q.γ d)) *
            ((N p K ^ f q (L q))⁻¹ * Q.J d / (N p K ^ ε₂ * 2 ^ Q.T)) := by
          field_simp
  have hnn : 0 ≤ S.dt * (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) :=
    mul_nonneg S.dt_pos.le (mul_nonneg (Real.rpow_nonneg hN.le _) hJ₁.le)
  rw [S.lift_mu_eq Q hν d]
  calc ENNReal.ofReal (N p K ^ (-f p (L p)) * S.J₃ Q d / (N p K ^ ε₃ * (2 : ℝ) ^ (S.T₁ + Q.T)))
      ≤ ENNReal.ofReal (S.dt * (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) *
          (N p K ^ (-f q (L q)) * Q.J d / (N p K ^ ε₂ * (2 : ℝ) ^ Q.T))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal S.dt *
          ENNReal.ofReal (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) *
          ENNReal.ofReal (N p K ^ (-f q (L q)) * Q.J d / (N p K ^ ε₂ * (2 : ℝ) ^ Q.T)) := by
        rw [ENNReal.ofReal_mul hnn, ENNReal.ofReal_mul S.dt_pos.le]
    _ ≤ ENNReal.ofReal S.dt * ν p K (S.γ₁ (Q.γ d)) (S.A₁ (Q.γ d)) *
          mu q k (Q.γ d) (Q.C d) :=
        mul_le_mul' (mul_le_mul' le_rfl hgood) hfl'

lemma lift_mass (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hω : ∀ a, 0 ≤ ω p K a)
    (hN : 1 ≤ N p K) {ε₃ : ℝ} (hε₃ : S.ε₁ + ε₂ ≤ ε₃) :
    ENNReal.ofReal (N p K ^ (-ε₃)) ≤ ∑ a : Fin (W p K),
      ENNReal.ofReal (ω p K a) * mu p K a {z | ∃ d, S.γ₃ Q d = a ∧ z ∈ S.C₃ Q d} := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, hS3, -⟩ := hS
  have hQ := Q.hcd
  unfold ChartData at hQ
  obtain ⟨-, -, hQ3, -, -, -, -, -, -, hQ10⟩ := hQ
  rw [S.hN] at hQ10
  have hS'meas : ∀ i : Fin (W q k), MeasurableSet {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d} := by
    intro i
    have : {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d} = ⋃ d, ⋃ (_ : Q.γ d = i), Q.C d := by
      ext z
      simp
    rw [this]
    exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _ => (hQ3 d).2
  have hUmeas : ∀ i : Fin (W q k),
      MeasurableSet (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) :=
    fun i => (hS3 i).2.inter (S.measurable_Φ i (hS'meas i))
  have hset : ∀ a : Fin (W p K), {z | ∃ d, S.γ₃ Q d = a ∧ z ∈ S.C₃ Q d} =
      ⋃ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
        (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) := by
    intro a
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop, Set.mem_inter_iff, Set.mem_preimage, γ₃, C₃]
    constructor
    · rintro ⟨d, hd, hz1, hz2⟩
      exact ⟨Q.γ d, hd, hz1, d, rfl, hz2⟩
    · rintro ⟨i, hi, hz1, d, hd, hz2⟩
      subst hd
      exact ⟨d, hi, hz1, hz2⟩
  have hmeas_a : ∀ a : Fin (W p K), mu p K a {z | ∃ d, S.γ₃ Q d = a ∧ z ∈ S.C₃ Q d} =
      ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
        mu p K a (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) := by
    intro a
    rw [hset a]
    apply measure_biUnion_finset₀
    · intro i hi i' hi' hii'
      have hia : S.γ₁ i = a := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      have hia' : S.γ₁ i' = a := (Finset.mem_filter.mp (Finset.mem_coe.mp hi')).2
      have hnull := mu_inter_null_of_chart S.hcd hν hii' (hia.trans hia'.symm)
      rw [hia] at hnull
      exact measure_mono_null
        (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) hnull
    · intro i _
      exact (hUmeas i).nullMeasurableSet
  have hiden : ∀ i : Fin (W q k),
      ENNReal.ofReal (ω p K (S.γ₁ i)) *
        mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) =
      ENNReal.ofReal S.Z *
        (ENNReal.ofReal (ω q k i) * mu q k i {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) := by
    intro i
    rw [S.mass_q_eq hν hω i (hS'meas i), ← mul_assoc, ← mul_assoc,
      mul_comm (ENNReal.ofReal S.Z) (ENNReal.ofReal (ω p K (S.γ₁ i))),
      mul_assoc (ENNReal.ofReal (ω p K (S.γ₁ i))), ← ENNReal.ofReal_mul S.Z_pos.le,
      mul_inv_cancel₀ S.Z_pos.ne', ENNReal.ofReal_one, mul_one]
  calc ENNReal.ofReal (N p K ^ (-ε₃))
      ≤ ENNReal.ofReal (N p K ^ (-S.ε₁) * N p K ^ (-ε₂)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = ENNReal.ofReal (N p K ^ (-S.ε₁)) * ENNReal.ofReal (N p K ^ (-ε₂)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _)
    _ ≤ ENNReal.ofReal S.Z * ∑ i : Fin (W q k),
          ENNReal.ofReal (ω q k i) * mu q k i {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d} :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (S.Z_ge hν hω hN0)) hQ10
    _ = ∑ i : Fin (W q k), ENNReal.ofReal (ω p K (S.γ₁ i)) *
          mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (hiden i).symm
    _ = ∑ a : Fin (W p K), ∑ i ∈ Finset.univ.filter (fun i => S.γ₁ i = a),
          ENNReal.ofReal (ω p K (S.γ₁ i)) *
            mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' {z' | ∃ d, Q.γ d = i ∧ z' ∈ Q.C d}) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ a : Fin (W p K),
          ENNReal.ofReal (ω p K a) * mu p K a {z | ∃ d, S.γ₃ Q d = a ∧ z ∈ S.C₃ Q d} := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hmeas_a a, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
