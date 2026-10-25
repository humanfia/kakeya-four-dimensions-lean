import Submission.Obl.k4_matching_homogeneous_records.Input
import Submission.Obl.k4_matching_homogeneous_records.MeasureHomogenize

/-!
# From raw records to homogeneous records with fixed exponents

`RawRecords` carries exact records with only the finest count `N ^ (d + r 1 + ε)`.
At one scale we homogenize the record tree (`measure_homogenize`), restrict and renormalize the
event law, and read off exponents `v k = log_N #(F k '' S')`. Along a cofinal sequence of
scales these exponents lie in a compact box; a convergent subsequence gives one `u`.
-/

namespace Submission.Obl.k4_matching_homogeneous_records

open MeasureTheory Set Filter Topology

/-- `Records` is monotone in the tolerance and stable under moving the exponents by a little. -/
theorem records_mono {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {q : ℕ} {u v : ℕ → ℝ} {ε ε' η N : ℝ}
    (hN : 1 ≤ N) (hη : 0 ≤ η) (hεε' : ε + η ≤ ε')
    (hk : ∀ k, k ≤ q → v k ≤ u k + η)
    (hab : ∀ a b, a ≤ b → b ≤ q → v b - v a ≤ u b - u a + η)
    (hv : Records J d β q v ε N) : Records J d β q u ε' N := by
  obtain ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hn₁, hn₂, hf₁, hf₂, hd₁, hd₂, hπ₁, hπ₂, hs₁, hs₂,
    hμ, hm₁, hm₂, hSm, hSc, hgood, hhmono, hhb, hFm, hFchar, hcount, hdesc⟩ := hv
  have hpow : ∀ {x y : ℝ}, x ≤ y → N ^ x ≤ N ^ y := fun hxy =>
    Real.rpow_le_rpow_of_exponent_le hN hxy
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hn₁.trans (hpow (by linarith)),
    hn₂.trans (hpow (by linarith)), hf₁, hf₂,
    fun i j hj t ht => (hd₁ i j hj t ht).trans (hpow (by linarith)),
    fun i j hj t ht => (hd₂ i j hj t ht).trans (hpow (by linarith)),
    hπ₁, hπ₂, hs₁, hs₂, hμ, ?_, ?_, hSm, hSc, ?_, hhmono, hhb, hFm, hFchar, ?_, ?_⟩
  · intro i E hE
    refine (hm₁ i E hE).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact mul_le_mul_of_nonneg_right (hpow (by linarith)) (hπ₁ i)
  · intro i E hE
    refine (hm₂ i E hE).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact mul_le_mul_of_nonneg_right (hpow (by linarith)) (hπ₂ i)
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hgood p hp
    refine ⟨h1, h2.trans (hpow (by linarith)), fun j hj hjJ => ⟨?_, fun hβ => ?_⟩⟩
    · exact (h3 j hj hjJ).1.trans (hpow (by linarith))
    · exact (hpow (by linarith)).trans ((h3 j hj hjJ).2 hβ)
  · intro k hk'
    exact (hcount k hk').trans (hpow (by linarith [hk k hk']))
  · intro a b hab' hbq x hx
    exact (hdesc a b hab' hbq x hx).trans (hpow (by linarith [hab a b hab' hbq]))

/-- `Nat.log 2 n ≤ e * log₂ N` when `n ≤ N ^ e`. -/
lemma natLog_le_mul_logb {n : ℕ} {N e : ℝ} (hN : 1 ≤ N) (he : 0 ≤ e) (hn : (n : ℝ) ≤ N ^ e) :
    (Nat.log 2 n : ℝ) ≤ e * Real.logb 2 N := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.log_zero_right, CharP.cast_eq_zero]
    exact mul_nonneg he (Real.logb_nonneg (by norm_num) hN)
  · have h1 := Real.natLog_le_logb n 2
    push_cast at h1
    refine h1.trans ?_
    rw [← Real.logb_rpow_eq_mul_logb_of_pos (by linarith)]
    exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hn

/-- **One scale.** Homogenize the raw records at one scale `N`. -/
theorem records_of_raw {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {q : ℕ} {ε δ N : ℝ}
    (hN : 1 < N) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hA : 0 ≤ d + radius J β 1 + ε)
    (hlog : (((d + radius J β 1 + ε) * Real.logb 2 N + 1) * 2) ^ q ≤ N ^ δ)
    (hraw : RawRecords J d β q ε N) :
    ∃ v : ℕ → ℝ, (∀ k, k ≤ q → 0 ≤ v k) ∧ (∀ a b, a ≤ b → b ≤ q → v a ≤ v b) ∧
      v q ≤ d + radius J β 1 + ε ∧ Records J d β q v (ε + δ) N := by
  obtain ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hn₁, hn₂, hf₁, hf₂, hd₁, hd₂, hπ₁, hπ₂, hs₁, hs₂,
    hμ, hm₁, hm₂, hSm, hSc, hgood, hhmono, hhb, hFm, hFchar, hcount⟩ := hraw
  have hN0 : 0 < N := by linarith
  have hpow : ∀ {x y : ℝ}, x ≤ y → N ^ x ≤ N ^ y := fun hxy =>
    Real.rpow_le_rpow_of_exponent_le hN.le hxy
  -- the records are nested
  have hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S, F b x = F b y → F a x = F a y := by
    intro a b hab hbq x hx y hy hxy
    rw [hFchar a (hab.trans hbq) x hx y hy]
    intro v hv
    exact (hFchar b hbq x hx y hy).1 hxy v (hv.trans hab)
  obtain ⟨S', hS'S, hS'm, hmass, hmono, hdesc⟩ :=
    measure_homogenize μ q F (hFm q le_rfl).1 S hSm (hFm q le_rfl).2 hnest
  set K : ℝ := ((Nat.log 2 (F q '' S).ncard + 1 : ℕ) : ℝ) with hK
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.succ_pos _
  -- the loss `K ^ q` and the factor `2 ^ q` are at most `N ^ δ`
  have hKlog : K ≤ (d + radius J β 1 + ε) * Real.logb 2 N + 1 := by
    rw [hK]
    push_cast
    linarith [natLog_le_mul_logb hN.le hA hcount]
  have hK2 : (K * 2) ^ q ≤ N ^ δ :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hKlog (by norm_num)) q).trans
      hlog
  have hKq : K ^ q ≤ N ^ δ := by
    refine le_trans ?_ hK2
    rw [mul_pow]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have h2q : (2 : ℝ) ^ q ≤ N ^ δ := by
    refine le_trans ?_ hK2
    rw [mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK1)
  -- the mass of `S'`
  have hS1 : μ S = 1 := (prob_compl_eq_zero_iff hSm).1 hSc
  have hSr : μ.real S = 1 := by rw [measureReal_def, hS1, ENNReal.toReal_one]
  rw [hSr] at hmass
  have hS'pos : 0 < μ.real S' := by
    by_contra hneg
    have : μ.real S' = 0 := le_antisymm (not_lt.1 hneg) measureReal_nonneg
    rw [this, mul_zero] at hmass
    linarith
  have hS'0 : μ S' ≠ 0 := by
    intro h0
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hS'pos
    exact lt_irrefl _ hS'pos
  have hS'top : μ S' ≠ ⊤ := measure_ne_top μ S'
  have hinv : (μ S')⁻¹ ≤ ENNReal.ofReal (N ^ δ) := by
    rw [← ofReal_measureReal hS'top, ← ENNReal.ofReal_inv_of_pos hS'pos]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans ?_ hKq
    rw [inv_le_iff_one_le_mul₀ hS'pos]
    linarith
  have hS'ne : S'.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hS'0
    exact hS'0 measure_empty
  -- the selected law
  set μ' : Measure ((Fin n₁ × Fin n₂) × ℝ) := (μ S')⁻¹ • μ.restrict S' with hμ'
  have hμ'le : ∀ A, μ' A ≤ ENNReal.ofReal (N ^ δ) * μ A := by
    intro A
    rw [hμ', Measure.smul_apply, Measure.restrict_apply' hS'm, smul_eq_mul]
    exact mul_le_mul' hinv (measure_mono Set.inter_subset_left)
  have hμ'prob : IsProbabilityMeasure μ' := by
    constructor
    rw [hμ', Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel hS'0 hS'top]
  have hμ'c : μ' S'ᶜ = 0 := by
    rw [hμ', Measure.smul_apply, Measure.restrict_apply' hS'm, Set.compl_inter_self,
      measure_empty, smul_zero]
  -- the exponents
  have hfin' : ∀ k, k ≤ q → (F k '' S').Finite := fun k hk =>
    (hFm k hk).2.subset (Set.image_mono hS'S)
  have hcpos : ∀ k, k ≤ q → (0 : ℝ) < (F k '' S').ncard := by
    intro k hk
    exact_mod_cast (Set.ncard_pos (hfin' k hk)).2 (hS'ne.image _)
  set v : ℕ → ℝ := fun k => Real.logb N ((F k '' S').ncard : ℝ) with hv
  have hNv : ∀ k, k ≤ q → N ^ v k = (F k '' S').ncard := fun k hk =>
    Real.rpow_logb hN0 hN.ne' (hcpos k hk)
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact Real.logb_nonneg hN (by exact_mod_cast (Set.ncard_pos (hfin' k hk)).2 (hS'ne.image _))
  · intro a b hab hbq
    exact Real.logb_le_logb_of_le hN (hcpos a (hab.trans hbq)) (by exact_mod_cast hmono a b hab hbq)
  · have h1 : ((F q '' S').ncard : ℝ) ≤ (F q '' S).ncard := by
      exact_mod_cast Set.ncard_le_ncard (Set.image_mono hS'S) (hFm q le_rfl).2
    calc v q ≤ Real.logb N (N ^ (d + radius J β 1 + ε)) :=
          Real.logb_le_logb_of_le hN (hcpos q le_rfl) (h1.trans hcount)
      _ = d + radius J β 1 + ε := Real.logb_rpow hN0 hN.ne'
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ', h, F, S', hn₁.trans (hpow (by linarith)),
    hn₂.trans (hpow (by linarith)), hf₁, hf₂,
    fun i j hj t ht => (hd₁ i j hj t ht).trans (hpow (by linarith)),
    fun i j hj t ht => (hd₂ i j hj t ht).trans (hpow (by linarith)),
    hπ₁, hπ₂, hs₁, hs₂, hμ'prob, ?_, ?_, hS'm, hμ'c, ?_, hhmono, hhb,
    fun k hk => ⟨(hFm k hk).1, hfin' k hk⟩,
    fun k hk x hx y hy => hFchar k hk x (hS'S hx) y (hS'S hy), ?_, ?_⟩
  · intro i E hE
    calc μ' {p | p.1.1 = i ∧ p.2 ∈ E}
        ≤ ENNReal.ofReal (N ^ δ) * μ {p | p.1.1 = i ∧ p.2 ∈ E} := hμ'le _
      _ ≤ ENNReal.ofReal (N ^ δ) * (ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) :=
          mul_le_mul_right (hm₁ i E hE) _
      _ = ENNReal.ofReal (N ^ δ * (N ^ ε * π₁ i)) * MeasureTheory.volume E := by
          rw [ENNReal.ofReal_mul (p := N ^ δ) (by positivity), mul_assoc]
      _ = ENNReal.ofReal (N ^ (ε + δ) * π₁ i) * MeasureTheory.volume E := by
          congr 2; rw [Real.rpow_add hN0]; ring
  · intro i E hE
    calc μ' {p | p.1.2 = i ∧ p.2 ∈ E}
        ≤ ENNReal.ofReal (N ^ δ) * μ {p | p.1.2 = i ∧ p.2 ∈ E} := hμ'le _
      _ ≤ ENNReal.ofReal (N ^ δ) * (ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) :=
          mul_le_mul_right (hm₂ i E hE) _
      _ = ENNReal.ofReal (N ^ δ * (N ^ ε * π₂ i)) * MeasureTheory.volume E := by
          rw [ENNReal.ofReal_mul (p := N ^ δ) (by positivity), mul_assoc]
      _ = ENNReal.ofReal (N ^ (ε + δ) * π₂ i) * MeasureTheory.volume E := by
          congr 2; rw [Real.rpow_add hN0]; ring
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hgood p (hS'S hp)
    refine ⟨h1, h2.trans (hpow (by linarith)), fun j hj hjJ => ⟨?_, fun hβ => ?_⟩⟩
    · exact (h3 j hj hjJ).1.trans (hpow (by linarith))
    · exact (hpow (by linarith)).trans ((h3 j hj hjJ).2 hβ)
  · intro k hk
    rw [← hNv k hk]
    exact hpow (by linarith)
  · intro a b hab hbq x hx
    have hd := hdesc a b hab hbq x hx
    have hdR : ((F b '' {y | y ∈ S' ∧ F a y = F a x}).ncard : ℝ) * (F a '' S').ncard ≤
        2 ^ (b - a) * (F b '' S').ncard := by exact_mod_cast hd
    have hca := hcpos a (hab.trans hbq)
    have h2 : (2 : ℝ) ^ (b - a) ≤ N ^ δ :=
      (pow_le_pow_right₀ (by norm_num) (by omega)).trans h2q
    calc ((F b '' {y | y ∈ S' ∧ F a y = F a x}).ncard : ℝ)
        ≤ 2 ^ (b - a) * (F b '' S').ncard / (F a '' S').ncard := by
          rw [le_div_iff₀ hca]; exact hdR
      _ = 2 ^ (b - a) * N ^ (v b - v a) := by
          rw [Real.rpow_sub hN0, hNv a (hab.trans hbq), hNv b hbq, mul_div_assoc]
      _ ≤ N ^ δ * N ^ (v b - v a) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = N ^ (v b - v a + δ) := by rw [← Real.rpow_add hN0]; ring_nf
      _ ≤ N ^ (v b - v a + (ε + δ)) := hpow (by linarith)

/-- `((C log₂ N + 1) * 2) ^ q` grows slower than any power of `N`. -/
lemma exists_log_pow_le (C δ : ℝ) (q : ℕ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ N₀ : ℝ, ∀ N, N₀ ≤ N → ((C * Real.logb 2 N + 1) * 2) ^ q ≤ N ^ δ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨1, fun N hN => ?_⟩
    simp only [pow_zero]
    exact Real.one_le_rpow hN hδ.le
  set s := δ / q with hs
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < s := div_pos hδ hq'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := (isLittleO_log_rpow_atTop hs0).bound
    (c := Real.log 2 / (4 * (C + 1))) (by positivity)
  have h2 := (tendsto_rpow_atTop hs0).eventually_ge_atTop 4
  have h3 := eventually_ge_atTop (1 : ℝ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hl, hp, hN1⟩ := hN₀ N hN
  have hN0 : 0 < N := by linarith
  have hNs : 0 < N ^ s := Real.rpow_pos_of_pos hN0 s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNs] at hl
  have hlog : Real.log N ≤ Real.log 2 / (4 * (C + 1)) * N ^ s := (le_abs_self _).trans hl
  have hlogb : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN1
  have hkey : (C * Real.logb 2 N + 1) * 2 ≤ N ^ s := by
    have e1 : C * Real.logb 2 N ≤ C * (Real.log 2 / (4 * (C + 1)) * N ^ s / Real.log 2) := by
      rw [Real.logb]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hlog2.le) hC
    have e2 : C * (Real.log 2 / (4 * (C + 1)) * N ^ s / Real.log 2) =
        C / (C + 1) * (N ^ s / 4) := by
      field_simp
    have e3 : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have e4 : C / (C + 1) * (N ^ s / 4) ≤ N ^ s / 4 :=
      mul_le_of_le_one_left (by positivity) e3
    linarith
  calc ((C * Real.logb 2 N + 1) * 2) ^ q ≤ (N ^ s) ^ q :=
        pow_le_pow_left₀ (by positivity) hkey q
    _ = N ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, hs, div_mul_cancel₀ _ hq'.ne']

/-- **Selection.** Cofinal raw records give one exponent function `u` with cofinal
homogeneous records. -/
theorem records_select {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {q : ℕ}
    (hA : 0 ≤ d + radius J β 1)
    (hraw : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ RawRecords J d β q ε N) :
    ∃ u : ℕ → ℝ, ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧
        u q ≤ d + radius J β 1) ∧
      ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ Records J d β q u ε N := by
  set C := d + radius J β 1 with hC
  -- one scale for each `m`
  have hstep : ∀ m : ℕ, ∃ N : ℝ, (m : ℝ) + 2 ≤ N ∧ ∃ v : ℕ → ℝ,
      (∀ k, k ≤ q → 0 ≤ v k ∧ v k ≤ C + 1) ∧ (∀ a b, a ≤ b → b ≤ q → v a ≤ v b) ∧
      v q ≤ C + 1 / ((m : ℝ) + 1) ∧ Records J d β q v (2 / ((m : ℝ) + 1)) N := by
    intro m
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    set e : ℝ := 1 / ((m : ℝ) + 1) with he
    have he0 : 0 < e := by positivity
    have he1 : e ≤ 1 := by rw [he, div_le_one (by positivity)]; linarith
    obtain ⟨N₀, hN₀⟩ := exists_log_pow_le (C + 1) e q (by linarith) he0
    obtain ⟨N, hRN, hN⟩ := hraw e he0 (max (max ((m : ℝ) + 2) N₀) 2) (le_max_right _ _)
    have hN2 : (m : ℝ) + 2 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hRN)
    have hN1 : 1 < N := by linarith
    have hNN₀ : N₀ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hRN)
    have hlogN : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN1.le
    have hlog : (((d + radius J β 1 + e) * Real.logb 2 N + 1) * 2) ^ q ≤ N ^ e := by
      refine le_trans (pow_le_pow_left₀ (by positivity) ?_ q) (hN₀ N hNN₀)
      have : (d + radius J β 1 + e) * Real.logb 2 N ≤ (C + 1) * Real.logb 2 N :=
        mul_le_mul_of_nonneg_right (by linarith) hlogN
      linarith
    obtain ⟨v, hv0, hvmono, hvq, hrec⟩ :=
      records_of_raw hN1 he0.le he0.le (by linarith) hlog hN
    refine ⟨N, hN2, v, fun k hk => ⟨hv0 k hk, ?_⟩, hvmono, hvq, ?_⟩
    · exact (hvmono k q hk le_rfl).trans (by linarith)
    · have : e + e = 2 / ((m : ℝ) + 1) := by rw [he]; ring
      rw [← this]
      exact hrec
  choose N hN v hv0 hvmono hvq hrec using hstep
  -- compactness of the exponent box
  let x : ℕ → (Fin (q + 1) → ℝ) := fun m k => v m k
  have hx : ∀ m, x m ∈ Set.Icc (0 : Fin (q + 1) → ℝ) (fun _ => C + 1) := by
    intro m
    constructor
    · intro k; exact (hv0 m k (Nat.lt_succ_iff.1 k.2)).1
    · intro k; exact (hv0 m k (Nat.lt_succ_iff.1 k.2)).2
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  let u : ℕ → ℝ := fun k => if hk : k < q + 1 then a ⟨k, hk⟩ else 0
  have hu : ∀ k (hk : k ≤ q), u k = a ⟨k, Nat.lt_succ_of_le hk⟩ := fun k hk =>
    dite_eq_left (Nat.lt_succ_of_le hk)
  have hcoord : ∀ k, k ≤ q → Tendsto (fun m => v (φ m) k) atTop (𝓝 (u k)) := by
    intro k hk
    rw [hu k hk]
    exact tendsto_pi_nhds.1 hlim ⟨k, Nat.lt_succ_of_le hk⟩
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hinv : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφtop
  refine ⟨u, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro k hk
    exact ge_of_tendsto' (hcoord k hk) (fun m => (hv0 (φ m) k hk).1)
  · intro a' b' hab hbq
    exact le_of_tendsto_of_tendsto' (hcoord a' (hab.trans hbq)) (hcoord b' hbq)
      (fun m => hvmono (φ m) a' b' hab hbq)
  · have h := (tendsto_const_nhds (x := C)).add hinv
    rw [add_zero] at h
    exact le_of_tendsto_of_tendsto' (hcoord q le_rfl) h (fun m => hvq (φ m))
  · intro ε hε R _
    have hclose : ∀ᶠ m in atTop, ∀ k : Fin (q + 1), |v (φ m) k - u k| < ε / 4 := by
      rw [Filter.eventually_all]
      intro k
      exact (Metric.tendsto_nhds.1 (hcoord k (Nat.lt_succ_iff.1 k.2)) (ε / 4) (by positivity)).mono
        (fun m hm => by rw [Real.dist_eq] at hm; exact hm)
    have hsmall : ∀ᶠ m in atTop, 2 / ((φ m : ℝ) + 1) ≤ ε / 2 := by
      have h2 : Tendsto (fun m => 2 * (1 / ((φ m : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
        hinv.const_mul 2
      rw [mul_zero] at h2
      exact (h2.eventually (eventually_le_nhds (show (0 : ℝ) < ε / 2 by positivity))).mono
        (fun m hm => by rw [mul_one_div] at hm; exact hm)
    have hbig : ∀ᶠ m in atTop, R ≤ N (φ m) := by
      have : ∀ᶠ m in atTop, R ≤ (φ m : ℝ) :=
        (tendsto_natCast_atTop_atTop.comp hφtop).eventually_ge_atTop R
      exact this.mono (fun m hm => hm.trans (by linarith [hN (φ m)]))
    obtain ⟨m, hm1, hm2, hm3⟩ := (hclose.and (hsmall.and hbig)).exists
    refine ⟨N (φ m), hm3, ?_⟩
    have hN1 : 1 ≤ N (φ m) := by
      have := hN (φ m)
      have : (0 : ℝ) ≤ φ m := (φ m).cast_nonneg
      linarith
    refine records_mono (η := ε / 2) hN1 (by positivity) (by linarith) ?_ ?_ (hrec (φ m))
    · intro k hk
      have h1 := (abs_lt.1 (hm1 ⟨k, Nat.lt_succ_of_le hk⟩)).2
      simp only at h1
      linarith
    · intro a' b' hab hbq
      have h1 := abs_lt.1 (hm1 ⟨a', Nat.lt_succ_of_le (hab.trans hbq)⟩)
      have h2 := abs_lt.1 (hm1 ⟨b', Nat.lt_succ_of_le hbq⟩)
      simp only at h1 h2
      linarith [h1.1, h1.2, h2.1, h2.2]

end Submission.Obl.k4_matching_homogeneous_records
