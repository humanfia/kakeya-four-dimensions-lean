import Submission.Obl.k4_scalar_true_terminal_lifting.LiftDefs

/-!
# Lifted chart: label lists

Cardinality and measurability of the composed label lists, and the null set of selected
incidences missing from their list.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

lemma lst_measurable_coarseLab (NN L b : ℝ) (s : Fin 2) :
    Measurable (coarseLab NN L b s) := by
  unfold coarseLab
  exact measurable_fst.prodMk ((measurable_of_countable
    (fun n : ℤ => ⌊(n : ℝ) * (NN ^ (-L) / NN ^ (-b))⌋ + ((s : ℕ) : ℤ))).comp measurable_snd)

/-- A chart with at least one piece forces `1 ≤ N`: with budget `B = 0` the assignment
formats are trivial (empty or everything), which contradicts the bounded nonempty
assignments; with `B ≥ 1` the count bound `1 ≤ n ≤ N ^ B` does it. -/
lemma lst_one_le_N_of_chart {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool} {k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (hN : 0 < N p k) (i : Fin n) : 1 ≤ N p k := by
  unfold ChartData at hcd
  obtain ⟨-, h2, -, -, h5, h6, -⟩ := hcd
  by_contra hlt
  rw [not_le] at hlt
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    obtain ⟨hpos, -, -, -, -, -, -, hA, hF5, -⟩ := h6 i
    have hne : (C i).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      rw [hem, measure_empty] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨w, hw⟩ := hne
    have hwA : (w.1.1, w.1.2) ∈ A i := ((h5 i hw).2).1
    obtain ⟨kk, -, pp, hpp, SS, hSS⟩ := hF5 w.1.1
    have hmem : w.1.2 ∈ {a | (w.1.1, a) ∈ A i} := hwA
    rw [hSS] at hmem
    have hconst : ∀ (jj : Fin kk) (a : Fin 5 → ℝ),
        MvPolynomial.eval a (pp jj) = MvPolynomial.eval w.1.2 (pp jj) := by
      intro jj a
      have h0 : (pp jj).totalDegree = 0 := Nat.le_zero.mp (hpp jj).1
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0, eval_C, eval_C]
    have ha' : (fun _ : Fin 5 => N p k ^ ε + 1) ∈ {a | (w.1.1, a) ∈ A i} := by
      rw [hSS]
      have hfun : (fun jj => SignType.sign
          (MvPolynomial.eval (fun _ : Fin 5 => N p k ^ ε + 1) (pp jj))) =
          (fun jj => SignType.sign (MvPolynomial.eval w.1.2 (pp jj))) := by
        funext jj
        rw [hconst jj]
      exact (show _ ∈ SS from hfun ▸ hmem)
    have hb := (hA _ ha').2 0
    simp only at hb
    have hpos' : 0 < N p k ^ ε + 1 := by positivity
    rw [abs_of_pos hpos'] at hb
    linarith
  · have hn : (1 : ℝ) ≤ n := by
      have := i.pos
      exact_mod_cast this
    have hlt1 : N p k ^ (B : ℝ) < 1 := Real.rpow_lt_one hN.le hlt (by exact_mod_cast hB)
    linarith

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)
variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

lemma lst_measurable_qlab (i : Fin (W q k)) (s : Fin 2) : Measurable (S.qlab i s) := by
  unfold qlab
  have h1 : Measurable (fun w : Fin 2 → ℝ =>
      (![(w 0 - S.t₀ i) / S.dt, (w 1 - S.u₁ i - w 0 * S.v₁ i) / S.J₁ i] : Fin 2 → ℝ)) := by
    apply Continuous.measurable
    refine continuous_pi fun e => ?_
    fin_cases e
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  have h2 : Measurable (fun z : (Fin 2 → ℝ) × ℤ => (z.2 : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp measurable_snd
  have h3 : Measurable (fun z : (Fin 2 → ℝ) × ℤ => MvPolynomial.eval z.1 (S.P₁ i)) :=
    (MvPolynomial.continuous_eval (S.P₁ i)).measurable.comp measurable_fst
  have h4 : Measurable (fun z : (Fin 2 → ℝ) × ℤ =>
      ⌊(z.2 : ℝ) - MvPolynomial.eval z.1 (S.P₁ i) / N p K ^ (-L p)⌋) :=
    (h2.sub (h3.div_const _)).floor
  exact (h1.comp measurable_fst).prodMk
    ((measurable_of_countable (fun n : ℤ => n + ((s : ℕ) : ℤ))).comp h4)

lemma lift_card (hN : 1 ≤ N p K) {ε₃ : ℝ} (hε₃ : 4 * N p K ^ (S.ε₁ + ε₂) ≤ N p K ^ ε₃)
    (a : Fin (W p K)) (z : (Fin 2 → ℝ) × ℤ) :
    ((S.Λ₃ Q a z).card : ℝ) ≤ N p K ^ ε₃ := by
  classical
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, -, -, -, -, hS7, -, -, -⟩ := hS
  have hQ := Q.hcd
  unfold ChartData at hQ
  obtain ⟨-, -, -, -, -, -, hQ7, -, -, -⟩ := hQ
  rw [S.hN] at hQ7
  have hN0 : 0 < N p K := by linarith
  have hsub : S.Λ₃ Q a z ⊆ (Finset.univ : Finset (Fin 2 × Fin 2)).biUnion
      (fun s => (S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z)).biUnion
        (fun i => Q.Λ i (S.qlab i s.2 z))) := by
    intro d hd
    rw [mem_Λ₃] at hd
    obtain ⟨s₁, s₂, h1, h2⟩ := hd
    simp only [Finset.mem_biUnion]
    exact ⟨(s₁, s₂), Finset.mem_univ _, Q.γ d, h1, h2⟩
  have hnat : (S.Λ₃ Q a z).card ≤ ∑ s : Fin 2 × Fin 2,
      ∑ i ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z), (Q.Λ i (S.qlab i s.2 z)).card := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum fun s _ => Finset.card_biUnion_le
  have hreal : ((S.Λ₃ Q a z).card : ℝ) ≤ ∑ s : Fin 2 × Fin 2,
      ∑ i ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z),
        ((Q.Λ i (S.qlab i s.2 z)).card : ℝ) := by
    exact_mod_cast hnat
  have hinner : ∀ s : Fin 2 × Fin 2,
      ∑ i ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z), ((Q.Λ i (S.qlab i s.2 z)).card : ℝ) ≤
        N p K ^ S.ε₁ * N p K ^ ε₂ := by
    intro s
    calc ∑ i ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z), ((Q.Λ i (S.qlab i s.2 z)).card : ℝ)
        ≤ ∑ i ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z), N p K ^ ε₂ :=
          Finset.sum_le_sum fun i _ => hQ7 i _
      _ = ((S.Λ₁ a (coarseLab (N p K) (L p) b s.1 z)).card : ℝ) * N p K ^ ε₂ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N p K ^ S.ε₁ * N p K ^ ε₂ :=
          mul_le_mul_of_nonneg_right (hS7 a _) (Real.rpow_nonneg hN0.le _)
  calc ((S.Λ₃ Q a z).card : ℝ)
      ≤ ∑ s : Fin 2 × Fin 2, N p K ^ S.ε₁ * N p K ^ ε₂ :=
        hreal.trans (Finset.sum_le_sum fun s _ => hinner s)
    _ = 4 * N p K ^ (S.ε₁ + ε₂) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Real.rpow_add hN0]
        norm_num
    _ ≤ N p K ^ ε₃ := hε₃

lemma lift_Λmeas (a : Fin (W p K)) (d : Fin Q.n) : MeasurableSet {z | d ∈ S.Λ₃ Q a z} := by
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, -, -, -, -, -, hS8, -, -⟩ := hS
  have hQ := Q.hcd
  unfold ChartData at hQ
  obtain ⟨-, -, -, -, -, -, -, hQ8, -, -⟩ := hQ
  have heq : {z | d ∈ S.Λ₃ Q a z} = ⋃ s₁ : Fin 2, ⋃ s₂ : Fin 2,
      (coarseLab (N p K) (L p) b s₁ ⁻¹' {w | Q.γ d ∈ S.Λ₁ a w} ∩
        S.qlab (Q.γ d) s₂ ⁻¹' {w | d ∈ Q.Λ (Q.γ d) w}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    exact S.mem_Λ₃ Q a z d
  rw [heq]
  refine MeasurableSet.iUnion fun s₁ => MeasurableSet.iUnion fun s₂ => ?_
  exact ((lst_measurable_coarseLab _ _ _ s₁) (hS8 a (Q.γ d))).inter
    ((S.lst_measurable_qlab (Q.γ d) s₂) (hQ8 (Q.γ d) d))

/-- The `i`-th selected incidences whose normalization falls in a q-null set are null. -/
lemma lst_null_Φ (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (i : Fin (W q k))
    {T' : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hT : mu q k i T' = 0) :
    mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' T') = 0 := by
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, hS3, -⟩ := hS
  have hc : (ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i))⁻¹ ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    have := hν (S.γ₁ i)
    exact measure_ne_top _ _
  have hmap : Measure.map (S.Φ i) ((mu p K (S.γ₁ i)).restrict (S.C₁ i)) T' = 0 := by
    have h := hT
    rw [S.mu_q_eq i, Measure.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  have hle := Measure.le_map_apply (μ := (mu p K (S.γ₁ i)).restrict (S.C₁ i))
    (S.measurable_Φ i).aemeasurable T'
  rw [hmap, Measure.restrict_apply' (hS3 i).2] at hle
  rw [Set.inter_comm]
  exact nonpos_iff_eq_zero.mp hle

/-- Two candidate coarse floors of a fine floor. -/
lemma lst_floor_coarse (X₀ : ℝ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ s : Fin 2, ⌊X₀ * ρ⌋ = ⌊((⌊X₀⌋ : ℤ) : ℝ) * ρ⌋ + ((s : ℕ) : ℤ) := by
  apply floor_two
  · exact mul_le_mul_of_nonneg_right (Int.floor_le X₀) hρ0.le
  · have h := Int.lt_floor_add_one X₀
    calc X₀ * ρ < (((⌊X₀⌋ : ℤ) : ℝ) + 1) * ρ := mul_lt_mul_of_pos_right h hρ0
      _ = ((⌊X₀⌋ : ℤ) : ℝ) * ρ + ρ := by ring
      _ ≤ ((⌊X₀⌋ : ℤ) : ℝ) * ρ + 1 := by linarith

/-- Two candidate floors of a shifted fine floor. -/
lemma lst_floor_shift (X₀ c : ℝ) :
    ∃ s : Fin 2, ⌊X₀ - c⌋ = ⌊((⌊X₀⌋ : ℤ) : ℝ) - c⌋ + ((s : ℕ) : ℤ) := by
  apply floor_two
  · linarith [Int.floor_le X₀]
  · linarith [Int.lt_floor_add_one X₀]

/-- `lift_null` with the extra hypothesis `1 ≤ N p K` (derived from the chart in `lift_null`). -/
lemma lst_null (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hN : 0 < N p K)
    (hN1 : 1 ≤ N p K) (hLq : L q = L p - r) (hbL : b ≤ L p) (d : Fin Q.n) :
    mu p K (S.γ₃ Q d) {z | z ∈ S.C₃ Q d ∧ d ∉ S.Λ₃ Q (S.γ₃ Q d)
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-L p)⌋ : ℤ))} = 0 := by
  have hS := S.hcd
  unfold ChartData at hS
  obtain ⟨-, -, -, -, -, -, -, -, hS9, -⟩ := hS
  have hQ := Q.hcd
  unfold ChartData at hQ
  obtain ⟨-, -, -, -, -, -, -, -, hQ9, -⟩ := hQ
  set i := Q.γ d with hi
  have hγ : S.γ₃ Q d = S.γ₁ i := rfl
  rw [hγ]
  set Xs : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) := {z | z ∈ S.C₁ i ∧ i ∉ S.Λ₁ (S.γ₁ i)
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-b)⌋ : ℤ))} with hXs
  set T' : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) := {z | z ∈ Q.C d ∧ d ∉ Q.Λ i
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N q k ^ (-L q)⌋ : ℤ))} with hT'
  have hX0 : mu p K (S.γ₁ i) Xs = 0 := hS9 i
  have hY0 : mu p K (S.γ₁ i) (S.C₁ i ∩ S.Φ i ⁻¹' T') = 0 := S.lst_null_Φ hν i (hQ9 d)
  -- the ratio of the two resolutions
  have hNL : 0 < N p K ^ (-L p) := Real.rpow_pos_of_pos hN _
  have hNb : 0 < N p K ^ (-b) := Real.rpow_pos_of_pos hN _
  have hρ0 : 0 < N p K ^ (-L p) / N p K ^ (-b) := div_pos hNL hNb
  have hρ1 : N p K ^ (-L p) / N p K ^ (-b) ≤ 1 := by
    rw [div_le_one hNb]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hNq : N q k ^ (-L q) = N p K ^ (-(L p - r)) := by rw [S.hN, hLq]
  have hsub : {z | z ∈ S.C₃ Q d ∧ d ∉ S.Λ₃ Q (S.γ₁ i)
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-L p)⌋ : ℤ))} ⊆
      Xs ∪ (S.C₁ i ∩ S.Φ i ⁻¹' T') := by
    rintro z ⟨⟨hzC, hzΦ⟩, hzΛ⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hnX, hnY⟩ := hcon
    have hin1 : i ∈ S.Λ₁ (S.γ₁ i)
        ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-b)⌋ : ℤ)) := by
      by_contra h
      exact hnX ⟨hzC, h⟩
    have hin2 : d ∈ Q.Λ i ((![(S.Φ i z).2, y (S.Φ i z).1 (S.Φ i z).2] : Fin 2 → ℝ),
        (⌊x (S.Φ i z).1 (S.Φ i z).2 / N q k ^ (-L q)⌋ : ℤ)) := by
      by_contra h
      exact hnY ⟨hzC, hzΦ, h⟩
    apply hzΛ
    rw [S.mem_Λ₃]
    obtain ⟨s₁, hs₁⟩ := lst_floor_coarse (x z.1 z.2 / N p K ^ (-L p)) hρ0 hρ1
    obtain ⟨s₂, hs₂⟩ := lst_floor_shift (x z.1 z.2 / N p K ^ (-L p))
      (MvPolynomial.eval (![z.2, y z.1 z.2] : Fin 2 → ℝ) (S.P₁ i) / N p K ^ (-L p))
    refine ⟨s₁, s₂, ?_, ?_⟩
    · have hxb : x z.1 z.2 / N p K ^ (-L p) * (N p K ^ (-L p) / N p K ^ (-b)) =
          x z.1 z.2 / N p K ^ (-b) := div_mul_div_cancel₀ hNL.ne'
      have hcl : coarseLab (N p K) (L p) b s₁
          ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-L p)⌋ : ℤ)) =
          ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-b)⌋ : ℤ)) := by
        unfold coarseLab
        rw [← hs₁, hxb]
      rw [hcl]
      exact hin1
    · have hql : S.qlab i s₂
          ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-L p)⌋ : ℤ)) =
          ((![(S.Φ i z).2, y (S.Φ i z).1 (S.Φ i z).2] : Fin 2 → ℝ),
            (⌊x (S.Φ i z).1 (S.Φ i z).2 / N q k ^ (-L q)⌋ : ℤ)) := by
        unfold qlab Φ
        simp only
        rw [S.hy, S.hx, hNq]
        have hx' : (x z.1 z.2 - MvPolynomial.eval (![z.2, y z.1 z.2] : Fin 2 → ℝ) (S.P₁ i)) /
            N p K ^ (-r) / N p K ^ (-(L p - r)) =
            x z.1 z.2 / N p K ^ (-L p) -
              MvPolynomial.eval (![z.2, y z.1 z.2] : Fin 2 → ℝ) (S.P₁ i) / N p K ^ (-L p) := by
          rw [div_div, ← Real.rpow_add hN, ← sub_div]
          congr 2
          ring
        rw [hx', hs₂]
        simp
      rw [hql]
      exact hin2
  exact measure_mono_null hsub (measure_union_null hX0 hY0)

lemma lift_null (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hN : 0 < N p K)
    (hLq : L q = L p - r) (hbL : b ≤ L p) (d : Fin Q.n) :
    mu p K (S.γ₃ Q d) {z | z ∈ S.C₃ Q d ∧ d ∉ S.Λ₃ Q (S.γ₃ Q d)
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / N p K ^ (-L p)⌋ : ℤ))} = 0 :=
  S.lst_null Q hν hN (lst_one_le_N_of_chart S.hcd hN (Q.γ d)) hLq hbL d

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
