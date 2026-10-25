import Submission.Obl.k4_quadratic_atlas_normalization.LowNumerics
import Submission.Obl.k4_quadratic_atlas_normalization.LowCurvatureChart
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_quadratic_atlas_normalization.PowerBins

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MeasureTheory MvPolynomial

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- A discarded chart retains its frame and uses empty assignments and the zero test. -/
theorem empty_chart_of_rough
    {N κ κ' j L a r B : ℝ} {M M' D D' T : ℕ} {E : Set Incidence}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Incidence} {ex ex' : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hκ : κ ≤ κ')
    (h : rough N M D κ T j L a B E c u Q R A F ex) (hext : ex') :
    chart N M' D' κ' T j r B E c u Q 0 ∅ ∅ ex' := by
  obtain ⟨hdet, hcu, hframe, hsize, _⟩ := h
  have hp : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  refine ⟨hdet, hcu.trans hp, hframe.trans hp,
    hsize.trans (div_le_div_of_nonneg_right hκ (by positivity)), by simp,
    ?_, MeasurableSet.empty, MeasurableSet.empty, ?_, ?_, ?_, hext⟩
  · intro e
    simp
    positivity
  · intro i
    exact ⟨fmt_empty 6 D' (by positivity), fmt_empty 7 D' (by positivity)⟩
  · simp
  · simp

/-- Deterministic low-curvature normalization under explicit large-scale caps. -/
theorem low_sample_normalization
    (L a h ε₀ ε : ℝ) (M D m : ℕ) (ha : 0 < a) (hε : 0 < ε) (hm : 0 < m)
    (hεa : ε₀ ≤ a / 4) (hεε : ε₀ ≤ ε / 4) (hstep : 4 * a / (m : ℝ) ≤ ε / 4)
    (N : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Line)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (hN : 2 ≤ N) (hNa : 4 ≤ N ^ (a / 2)) (hmN : 64 * (m : ℝ) ≤ N ^ (ε / 2))
    (hω0 : ∀ g, 0 ≤ ω g) (hω1 : ∑ g, ω g = 1)
    (hν : ∀ g, IsProbabilityMeasure (ν g)) (hB : ∀ g, 0 < B g)
    (hR : RoughAtSel (fun Bv R => lowCase N L a Bv R) N W ω ν E B L a h M D ε₀) :
    KnownAt N W ω ν E B L (L - 4 * a) h (lowOutputExponent M a) (max D 2) ε := by
  classical
  obtain ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst,
    hT, hC, hdisj, hlst, hch, hmass⟩ := hR
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hNpos : 0 < N := zero_lt_one.trans_le hN1
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ1
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let d : ℝ := 4 * a / (m : ℝ)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hNd : 1 ≤ N ^ d := Real.one_le_rpow hN1 hdpos.le
  have hκa : κ ≤ N ^ (a / 4) :=
    hκε.trans (Real.rpow_le_rpow_of_exponent_le hN1 hεa)
  have hκsq : κ ^ 2 ≤ N ^ (a / 2) := by
    calc
      _ ≤ (N ^ (a / 4)) ^ 2 := pow_le_pow_left₀ hκpos.le hκa 2
      _ = N ^ (a / 2) := by
        rw [← Real.rpow_mul_natCast hNpos.le]
        congr 1
        ring
  have hlarge : 4 * κ ^ 2 ≤ N ^ a := by
    calc
      _ ≤ 4 * N ^ (a / 2) := mul_le_mul_of_nonneg_left hκsq (by norm_num)
      _ ≤ N ^ (a / 2) * N ^ (a / 2) := mul_le_mul_of_nonneg_right hNa (by positivity)
      _ = N ^ a := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hNa2 : 2 ≤ N ^ a := by nlinarith only [hlarge, hκ1, sq_nonneg (κ - 1)]
  have hκNa : κ ≤ N ^ a := by nlinarith only [hlarge, hκ1, sq_nonneg (κ - 1)]
  let τ : ℝ := 64 * (m : ℝ) * κ * N ^ d
  have hτbase : 64 * (m : ℝ) * κ ≤ τ := by
    dsimp [τ]
    exact le_mul_of_one_le_right (by positivity) hNd
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτbase
  have hτ1 : 1 ≤ τ := by nlinarith only [hκ1, hm1, hτbase]
  have hτ2 : 2 ≤ τ := by nlinarith only [hκ1, hm1, hτbase]
  have hκτ : κ ≤ τ := by nlinarith only [hκ1, hm1, hτbase]
  have hNdτ : N ^ d ≤ τ := by
    dsimp [τ]
    apply le_mul_of_one_le_left (by positivity)
    nlinarith [hκ1, hm1]
  have hτlo : 16 * κ * (m : ℝ) ≤ τ := by
    nlinarith only [hτbase, mul_nonneg hκpos.le hmpos.le]
  have hτε : τ ≤ N ^ ε := by
    calc
      τ ≤ N ^ (ε / 2) * (N ^ (ε / 4) * N ^ (ε / 4)) := by
        dsimp [τ]
        rw [mul_assoc]
        apply mul_le_mul hmN _ (by positivity) (by positivity)
        apply mul_le_mul
        · exact hκε.trans (Real.rpow_le_rpow_of_exponent_le hN1 hεε)
        · exact Real.rpow_le_rpow_of_exponent_le hN1 hstep
        · positivity
        · positivity
      _ = N ^ ε := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
  let s : Fin C' → ℝ := fun b => ((j b : ℕ) : ℝ) / (2 : ℝ) ^ T
  let e : Fin C' → ℝ := fun b => (((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hse (b) : s b ≤ e b := by
    dsimp [s, e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have heq (b) : e b = s b + q := by dsimp [e, s, q]; ring
  have hdeg (b) : (R b).totalDegree ≤ 2 := by
    obtain ⟨_, _, _, _, hd, _⟩ := hch b
    exact hd
  have hAm (b) : MeasurableSet (A b) := by
    obtain ⟨_, _, _, _, _, _, hA, _⟩ := hch b
    exact hA
  have hFm (b) : MeasurableSet (F b) := by
    obtain ⟨_, _, _, _, _, _, _, hF, _⟩ := hch b
    exact hF
  have hselected (b) (p) (hp : p ∈ F b) : p.1 ∈ A b ∧ p.2 ∈ Icc (s b) (e b) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := hch b
    obtain ⟨_, hA, ht⟩ := hsel p hp
    exact ⟨hA, ht⟩
  have hmaxupper (b) (l) (hl : l ∈ A b) :
      derivativeMax (R b) (s b) (e b) l / B (γ b) ≤ N ^ (2 * a) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hwhole, _⟩ := hch b
    have hs := ((hwhole l hl).2.2 (s b) ⟨le_rfl, hse b⟩).2.2.1
    have he := ((hwhole l hl).2.2 (e b) ⟨hse b, le_rfl⟩).2.2.1
    have hm : derivativeMax (R b) (s b) (e b) l ≤ κ * B (γ b) * N ^ a :=
      max_le hs he
    calc
      _ ≤ (κ * B (γ b) * N ^ a) / B (γ b) := div_le_div_of_nonneg_right hm (hB _).le
      _ = κ * N ^ a := by field_simp [(hB (γ b)).ne']
      _ ≤ N ^ a * N ^ a := mul_le_mul_of_nonneg_right hκNa (by positivity)
      _ = N ^ (2 * a) := by rw [← Real.rpow_add hNpos]; congr 1; ring
  let G : ℕ → Fin C' → Set Incidence := fun z b => F b ∩ {p |
    lowCase N L a (B (γ b)) (R b) ∧
      p.1 ∈ binRegion (R b) (s b) (e b)
        (powerBin N a m z * B (γ b)) (powerBin N a m z * B (γ b) * N ^ d)}
  have hcover (b) : F b ∩ {_p | lowCase N L a (B (γ b)) (R b)} ⊆
      ⋃ z ∈ Finset.range m, G z b := by
    rintro p ⟨hpF, hpLow⟩
    have hpA := (hselected b p hpF).1
    have hlo := low_chart_derivative_witness hN1 ha hκ1 (hB _) hlarge hpLow (hch b) p.1 hpA
    obtain ⟨z, hz, hzl, hzu⟩ := powerBin_cover hNpos hm hlo (hmaxupper b p.1 hpA)
    refine mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hpF, hpLow, ?_⟩⟩
    refine ⟨(le_div_iff₀ (hB _)).mp hzl, ?_⟩
    convert (div_le_iff₀ (hB _)).mp hzu using 1 <;> dsimp [d] <;> ring
  obtain ⟨z, hz, hzMass⟩ := exists_common_bin_mass
    (fun b => (ν (γ b)).prod volume) (fun b => ENNReal.ofReal (ω (γ b)))
    (fun b => F b ∩ {_p | lowCase N L a (B (γ b)) (R b)})
    (Finset.range m) G (κ⁻¹ / 2) (by exact ⟨0, Finset.mem_range.mpr hm⟩) hcover hmass
  let v : ℝ := powerBin N a m z
  have hvpos : 0 < v := powerBin_pos hNpos a m z
  have hv : N ^ (-2 * a) ≤ v :=
    (powerBin_bounds hN1 ha.le hm (Nat.le_of_lt (Finset.mem_range.mp hz))).1
  let A' : Fin C' → Set Line := fun b =>
    A b ∩ {l | lowCase N L a (B (γ b)) (R b) ∧
      l ∈ binRegion (R b) (s b) (e b) (v * B (γ b)) (v * B (γ b) * N ^ d)}
  let F₀ : Fin C' → Set Incidence := G z
  let F' : Fin C' → Set Incidence := fun b => F₀ b ∩ derivativeFloorSet (R b) (v * B (γ b) / τ)
  let Bad : Fin C' → Set Incidence := fun b => F₀ b \ derivativeFloorSet (R b) (v * B (γ b) / τ)
  let R' : Fin C' → MvPolynomial (Fin 4) ℝ := fun b =>
    if lowCase N L a (B (γ b)) (R b) then C v⁻¹ * R b else 0
  have hAA' (b) : A' b ⊆ A b := inter_subset_left
  have hF₀F (b) : F₀ b ⊆ F b := inter_subset_left
  have hF'F (b) : F' b ⊆ F b := inter_subset_left.trans (hF₀F b)
  have hF₀A' (b) (p) (hp : p ∈ F₀ b) : p.1 ∈ A' b :=
    ⟨(hselected b p hp.1).1, hp.2⟩
  have hF'A' (b) (p) (hp : p ∈ F' b) : p.1 ∈ A' b := hF₀A' b p hp.1
  have hA'm (b) : MeasurableSet (A' b) := by
    by_cases hl : lowCase N L a (B (γ b)) (R b)
    · simpa [A', hl] using (hAm b).inter
        (measurableSet_binRegion (R b) (s b) (e b) (v * B (γ b)) (v * B (γ b) * N ^ d))
    · simp [A', hl]
  have hF₀m (b) : MeasurableSet (F₀ b) := by
    by_cases hl : lowCase N L a (B (γ b)) (R b)
    · simpa [F₀, G, v, hl, Set.preimage] using (hFm b).inter
        ((measurableSet_binRegion (R b) (s b) (e b) (v * B (γ b))
          (v * B (γ b) * N ^ d)).preimage measurable_fst)
    · simp [F₀, G, hl]
  have hF'm (b) : MeasurableSet (F' b) :=
    (hF₀m b).inter (measurableSet_derivativeFloorSet _ _)
  have hBadm (b) : MeasurableSet (Bad b) :=
    (hF₀m b).diff (measurableSet_derivativeFloorSet _ _)
  have hdisj' : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A' b) (A' b') :=
    fun b b' hne hg hj => (hdisj b b' hne hg hj).mono (hAA' b) (hAA' b')
  choose mm dd hmd using fun b l => derivative_affine (R b) (hdeg b) l
  have hscale (b) (l) (t) :
      |(mm b l / v) * t + dd b l / v| = |eval (x l t) (pderiv (3 : Fin 4) (R b))| / v := by
    rw [hmd b l t]
    rw [show mm b l / v * t + dd b l / v = (mm b l * t + dd b l) / v by ring,
      abs_div, abs_of_pos hvpos]
  have hBadSub (b) (p) (hp : p ∈ Bad b) : p.1 ∈ A' b ∧
      p.2 ∈ Icc (s b) (s b + q) ∧
        |(mm b p.1 / v) * p.2 + dd b p.1 / v| < B (γ b) / τ := by
    refine ⟨hF₀A' b p hp.1, ?_, ?_⟩
    · rw [← heq]
      exact (hselected b p (hF₀F b hp.1)).2
    · rw [hscale]
      apply (div_lt_iff₀ hvpos).mpr
      have hp' : |eval (x p.1 p.2) (pderiv (3 : Fin 4) (R b))| < v * B (γ b) / τ :=
        lt_of_not_ge hp.2
      convert hp' using 1 <;> ring
  have hlarge' (b) (l) (hl : l ∈ A' b) :
      ∃ t ∈ Icc (s b) (s b + q), B (γ b) ≤ |(mm b l / v) * t + dd b l / v| := by
    obtain ⟨t, ht, hat⟩ := derivativeMax_attained (R b) l (hse b)
    refine ⟨t, by simpa only [heq b] using ht, ?_⟩
    rw [hscale]
    apply (le_div_iff₀ hvpos).mpr
    rw [← hat]
    simpa only [mul_comm] using hl.2.2.1
  have hbad := weighted_affine_deletion_bound ν ω γ j A' Bad
    (fun b l => mm b l / v) (fun b l => dd b l / v) B s q τ
    hν hω0 hω1 hB hq hτ2 (by simp [q]) hA'm hBadm hdisj' hBadSub hlarge'
  let α : ℝ := (κ⁻¹ / 2) / (m : ℝ)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαhalf : α / 2 = 1 / (4 * κ * (m : ℝ)) := by dsimp [α]; field_simp; ring
  have hbadhalf : 4 / τ ≤ α / 2 := by
    rw [hαhalf]
    apply (div_le_div_iff₀ hτpos (by positivity : 0 < 4 * κ * (m : ℝ))).mpr
    nlinarith only [hτlo]
  have hcover' := weighted_mass_le_retained_add_deleted
    (fun b => (ν (γ b)).prod volume) (fun b => ENNReal.ofReal (ω (γ b))) F₀ F' Bad
    (by intro b p hp; by_cases hf : p ∈ derivativeFloorSet (R b) (v * B (γ b) / τ)
        · exact Or.inl ⟨hp, hf⟩
        · exact Or.inr ⟨hp, hf⟩)
  have hret := retain_half_mass _ _ _ α hα
    (by simpa only [Finset.card_range] using hzMass) hcover'
    (hbad.trans (ENNReal.ofReal_le_ofReal hbadhalf))
  have hmass' : ENNReal.ofReal τ⁻¹ ≤
      ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F' b) := by
    apply (ENNReal.ofReal_le_ofReal _).trans hret
    rw [hαhalf, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hτlo, mul_nonneg hκpos.le hmpos.le]
  refine ⟨τ, hτ1, hτε, T, C', γ, j, c, u, Q, R', A', F', lst,
    hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)),
    hC.trans (pow_le_pow_right₀ hN1 (lowOutputExponent_ge M a)), hdisj',
    fun g o => (hlst g o).trans hκτ, ?_, hmass'⟩
  intro b
  by_cases hl : lowCase N L a (B (γ b)) (R b)
  · have hAa : A' b = A b ∩ binRegion (R b) (s b) (e b) (v * B (γ b))
        (v * B (γ b) * N ^ d) := by ext l; simp [A', hl]
    have hFa : F' b = F b ∩ (Prod.fst ⁻¹' binRegion (R b) (s b) (e b) (v * B (γ b))
        (v * B (γ b) * N ^ d) ∩ derivativeFloorSet (R b) (v * B (γ b) / τ)) := by
      ext p; simp [F', F₀, G, v, hl, and_assoc]
    have hFmt (i) : fmt 6 (N ^ lowOutputExponent M a) (max D 2) {z | (i, z) ∈ A' b} ∧
        fmt 7 (N ^ lowOutputExponent M a) (max D 2) {z : Fin 7 → ℝ |
          ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ F' b} := by
      obtain ⟨_, _, _, _, _, _, _, _, hfmt, _⟩ := hch b
      constructor
      · rw [hAa]
        apply Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono
          (format_bin_assignment (R b) (hdeg b) (s b) (e b) _ _ (N ^ M) D (A b)
            (fun i => (hfmt i).1) i)
        · linarith [low_format_budget hN M a]
        · exact max_le (le_max_left _ _) (by omega)
      · rw [hFa]
        exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono
          (format_bin_selection (R b) (hdeg b) (s b) (e b) _ _ _ (N ^ M) D (F b)
            (fun i => (hfmt i).2) i) (low_format_budget hN M a) le_rfl
    dsimp only [R']
    rw [ite_eq_left hl]
    refine low_curvature_chart hN1 (lowOutputExponent_ge M a) hκ1 hκτ hτ2 (hB _) hvpos
      (low_scaled_thickness_bound hN1 hNa2 hv L)
      (low_scaled_coefficient_budget hN1 hv M) ?_ (hAA' b) (hF'F b) (hF'A' b)
      (hA'm b) (hF'm b) hFmt ?_ ?_ (hch b) ?_
    · exact (low_scaled_curvature_bound hN1 ha.le hNa2 hv (R b) hl).trans
        (div_le_div_of_nonneg_right
          (le_mul_of_one_le_left (sq_nonneg _) hτ1) (by unfold δ; positivity))
    · intro l hla t ht
      calc
        _ ≤ derivativeMax (R b) (s b) (e b) l := derivative_le_max (R b) (hdeg b) l ht
        _ ≤ v * B (γ b) * N ^ d := hla.2.2.2
        _ ≤ τ * v * B (γ b) := by nlinarith only [mul_le_mul_of_nonneg_left hNdτ (mul_nonneg hvpos.le (hB (γ b)).le)]
    · intro p hp
      exact hp.2
    · intro p hp
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hext⟩ := hch b
      exact hext p (hF'F b hp)
  · have hAa : A' b = ∅ := by ext l; simp [A', hl]
    have hFa : F' b = ∅ := by ext p; simp [F', F₀, G, hl]
    dsimp only [R']
    rw [ite_eq_right hl, hAa, hFa]
    exact empty_chart_of_rough hN1 (lowOutputExponent_ge M a) hκτ (hch b) (by simp)

end Submission.Obl.k4_quadratic_atlas_normalization
