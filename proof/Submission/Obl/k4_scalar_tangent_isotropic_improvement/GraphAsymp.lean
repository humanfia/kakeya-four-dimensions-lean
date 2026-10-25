import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphWrapAux
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.FiniteScaleGrid

/-!
# Stage bundles and the slow scale for the velocity-graph wrapper
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Filter Submission.Lib.K4ContinuousKakeya
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The hypotheses of `graph_stage_world` for one world. -/
def StageHyp (C : ℝ) (θ : Measure (ℕ × (Fin 5 → ℝ))) (ρ : Measure Inc) (π : Measure ℝ)
    (E₀ : Set Inc) (N H₀ K d S L b' : ℝ) (B : ℕ) : Prop :=
  IsFiniteMeasure θ ∧ θ Set.univ ≤ 1 ∧ IsFiniteMeasure ρ ∧ MeasurableSet E₀ ∧
  ρ.restrict E₀ ≤ ENNReal.ofReal H₀ • (θ.prod volume).restrict E₀ ∧
  ENNReal.ofReal H₀⁻¹ • (θ.prod volume).restrict E₀ ≤ ρ.restrict E₀ ∧
  (∀ p ∈ E₀, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H₀) ∧
  Set.Finite {q : Fin 3 → ℤ | ρ.restrict E₀ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0} ∧
  ({q : Fin 3 → ℤ | ρ.restrict E₀ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0}.ncard : ℝ) ≤
    H₀ * N ^ ((2 + d) * B) ∧
  (∀ q, ρ (physOf ⁻¹' cellSet (N ^ (-(((B : ℝ) + 1) / 2))) q) ≤
    ENNReal.ofReal (K * N ^ (-(2 + d) * (((B : ℝ) + 1) / 2)))) ∧
  (∀ (f : Fin 3 → ℤ) (c : ℤ), ρ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f ∩
    {p | ⌊p.1.2 1 / N ^ (-b')⌋ = c}) ≤
      ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * π {v | ⌊v / N ^ (-b')⌋ = c}) ∧
  (∀ c : ℤ, π {v | ⌊v / N ^ (-b')⌋ = c} ≤ ENNReal.ofReal (K * N ^ (-S * b'))) ∧
  H₀ ≤ N ∧ 144 * H₀ * N ^ (-(((B : ℝ) + 1) / 2)) ≤ N ^ (-2 * L) ∧
  N ^ (-L) * (1 + 4 * H₀) * (1 + 4 * (3 * H₀ + 1) * N ^ b') ≤ 1 / 2 ∧
  600 * K ^ 2 * H₀ ^ 2 ≤ N ^ (S * b') ∧
  10 ^ 25 * K * (C ^ 2 + 1) * H₀ ^ 20 ≤ N ^ ((1 - d) * ((B : ℝ) - 1) / 2 - 2 * L)

/-- The conclusions of `graph_stage_world` for one world. -/
def StageConcl (ρ : Measure Inc) (E₀ E : Set Inc) (G : (Fin 3 → ℤ) → ℝ × ℝ)
    (N H₀ d L b' : ℝ) (B : ℕ) : Prop :=
  MeasurableSet E ∧ E ⊆ E₀ ∧
  (ρ.restrict E₀ Set.univ).toReal ≤
    2 * (ρ.restrict E Set.univ).toReal + 1 / (100 * H₀) + 1 / (4 * H₀) ∧
  (∀ p ∈ E, |(G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1| ≤ graphBd H₀ N b' ∧
    |(G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2| ≤ graphBd H₀ N b' ∧
    |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1 -
        (G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2 * p.1.2 1| ≤
      N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b') ∧
  (∀ q, ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0 →
    ENNReal.ofReal (N ^ (-(2 + d) * B) / (200 * H₀ ^ 2)) ≤
      ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q))

theorem graph_stage {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK 3 C)
    {θ : Measure (ℕ × (Fin 5 → ℝ))} {ρ : Measure Inc} {π : Measure ℝ} {E₀ : Set Inc}
    {N H₀ K d S L b' : ℝ} {B : ℕ} (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hB : 3 ≤ B) (hL : 0 < L) (hb' : 0 < b') (h : StageHyp C θ ρ π E₀ N H₀ K d S L b' B) :
    ∃ (E : Set Inc) (G : (Fin 3 → ℤ) → ℝ × ℝ), StageConcl ρ E₀ E G N H₀ d L b' B := by
  obtain ⟨hθf, hθ1, hρf, hE₀, hle, hge, hE₀H, hOccFin, hOccCard, hcoarse, hjoint, hπ,
    n1, n2, n3, n4, n5⟩ := h
  haveI := hθf; haveI := hρf
  exact graph_stage_world hC0 hC θ hθ1 ρ π hE₀ hN hH₀ hK hd hB hL hb' hle hge hE₀H hOccFin hOccCard
    hcoarse hjoint hπ n1 n2 n3 n4 n5

/-- **Slow scale.** A scale `1 / (J k + 2)` tending to zero slowly enough that a given eventual
family of properties holds at `R = J k + 2` and `N^(S / (J k + 2))` beats a power of a subpower
sequence. -/
lemma exists_slow_scale (N Z : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hZ1 : ∀ k, 1 ≤ Z k) (hZ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Z k ≤ N k ^ ε) {S : ℝ}
    (hS : 0 < S) (P : ℝ → ℕ → Prop) (hP : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, P R k) :
    ∃ J : ℕ → ℕ, Tendsto J atTop atTop ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ (1 / ((J k : ℝ) + 2)) ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, P ((J k : ℝ) + 2) k ∧ 400000 * Z k ^ 7 ≤ N k ^ (S / ((J k : ℝ) + 2)) := by
  let Q : ℕ → ℕ → Prop := fun j k =>
    P ((j : ℝ) + 2) k ∧ 400000 * Z k ^ 7 ≤ N k ^ (S / ((j : ℝ) + 2))
  have hQ : ∀ j, ∀ᶠ k in atTop, Q j k := by
    intro j
    have h1 := hP ((j : ℝ) + 2) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    have h2 := eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hZ1 hZ 400000 7
      (by positivity : 0 < S / ((j : ℝ) + 2))
    filter_upwards [h1, h2] with k hk1 hk2
    exact ⟨hk1, hk2⟩
  obtain ⟨J, hJm, hJt, hJn, hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal Q hQ
  refine ⟨J, hJt, ?_, ?_⟩
  · intro ε hε
    have hM : Tendsto (fun k => J k + 2) atTop atTop := (tendsto_add_atTop_nat 2).comp hJt
    have := eventually_scale_rounding_loss_le N (fun k => J k + 2) (fun k => by linarith [hN k])
      hM hε
    filter_upwards [this] with k hk
    simpa using hk
  · filter_upwards [hdiag] with k hk
    exact hk (J k) le_rfl

/-- Fine-state palette domination in one world, at any velocity scale with a joint cap. -/
lemma world_palette {ρ : Measure Inc} {π : Measure ℝ} {E₀ E : Set Inc}
    {G' : (Fin 3 → ℤ) → ℝ × ℝ} {N H₀ K d L b' w : ℝ} {B : ℕ} (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K) (hN : 2 ≤ N)
    (hSC : StageConcl ρ E₀ E G' N H₀ d L b' B)
    (hjoint : ∀ (f : Fin 3 → ℤ) (c : ℤ), ρ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f ∩
      {p | ⌊p.1.2 1 / w⌋ = c}) ≤ ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * π {v | ⌊v / w⌋ = c})
    (f : Fin 3 → ℤ) (c : ℤ) :
    ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f ∩ {p | ⌊p.1.2 1 / w⌋ = c}) ≤
      ENNReal.ofReal (200 * K * H₀ ^ 2) * ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f) *
        π {v | ⌊v / w⌋ = c} := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  apply palette_of_heavy (hjoint f c) (hSC.2.2.2.2 f)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : 200 * K * H₀ ^ 2 * (N ^ (-(2 + d) * B) / (200 * H₀ ^ 2)) = K * N ^ (-(2 + d) * B) := by
    field_simp
  rw [this]

/-- **Coarse row lists in one world, at the stage parameters.** -/
lemma world_rows {ρ : Measure Inc} [IsFiniteMeasure ρ] {π : Measure ℝ} [IsProbabilityMeasure π]
    {E₀ E : Set Inc} {G' : (Fin 3 → ℤ) → ℝ × ℝ} {N H₀ K d S L b' U r r' : ℝ} {B : ℕ}
    (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K) (hb' : 0 < b') (hE₀m : MeasurableSet E₀)
    (hSC : StageConcl ρ E₀ E G' N H₀ d L b' B)
    (hE₀H : ∀ p ∈ E₀, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H₀)
    (hjoint : ∀ (f : Fin 3 → ℤ) (c : ℤ), ρ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f ∩
      {p | ⌊p.1.2 1 / N ^ (-r')⌋ = c}) ≤
        ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * π {v | ⌊v / N ^ (-r')⌋ = c})
    (hπcap : ∀ c : ℤ, π {v | ⌊v / N ^ (-b')⌋ = c} ≤ ENNReal.ofReal (K * N ^ (-S * b')))
    (hlist : ∀ (q' : Fin 3 → ℤ) (c : ℤ), ({β : Fin 5 → ℤ | ρ.restrict E₀
      {p | cellIdx (N ^ (-r')) (physOf p) = q' ∧ ⌊p.1.2 1 / N ^ (-r')⌋ = c ∧
        cbin (N ^ (-r')) p = β} ≠ 0}.ncard : ℝ) ≤ H₀)
    (hUH : H₀ ≤ U) (hUK : K ≤ U) (hUY : N ^ b' ≤ U)
    (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr'r : N ^ (r' - r) ≤ H₀) (hr'B : r' ≤ B) (hrL : r ≤ L)
    (hwin9 : 9 * N ^ b' ≤ N ^ r)
    (hX : 400000 * K ^ 3 * H₀ ^ 4 ≤ N ^ (S * b'))
    (Q : Fin 3 → ℤ) :
    ({v : ℤ × ℤ | ρ.restrict E {p | cellIdx (N ^ (-r)) (physOf p) = Q ∧
        rowPair (N ^ (-r)) (G' (cellIdx (N ^ (-(B : ℝ))) (physOf p))) = v} ≠ 0}.ncard : ℝ) ≤
      10 ^ 17 * U ^ 25 := by
  classical
  have hSC' := hSC
  obtain ⟨hEm, hEsub, -, hbd, hheavy⟩ := hSC
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH0 : 0 ≤ H₀ := by linarith
  have hK0 : 0 ≤ K := by linarith
  set w' : ℝ := N ^ (-r') with hw'
  set W : ℝ := N ^ (-b') with hW
  have hw'0 : 0 < w' := Real.rpow_pos_of_pos hN0 _
  have hW0 : 0 < W := Real.rpow_pos_of_pos hN0 _
  have hw'1 : w' ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  set m : ℕ := ⌈W / w'⌉₊ + 3 with hm
  have hm3 : 3 ≤ m := by rw [hm]; omega
  have hGb0 : 0 ≤ graphBd H₀ N b' := by unfold graphBd; positivity
  -- the window bound
  have h9 : 9 * w' ≤ W := by
    have e1 : w' ≤ N ^ (-r) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have e2 : 9 * N ^ (-r) ≤ W := by
      have hb'r : N ^ b' * N ^ (-b') = 1 := by rw [← Real.rpow_add hN0]; simp
      have hrr' : N ^ r * N ^ (-r) = 1 := by rw [← Real.rpow_add hN0]; simp
      have hpos : 0 ≤ N ^ (-r) := (Real.rpow_pos_of_pos hN0 _).le
      have := mul_le_mul_of_nonneg_right hwin9 (mul_nonneg hpos hW0.le)
      nlinarith
    linarith
  have hwin : ∀ c : ℤ, ∑ c' ∈ Finset.Icc (c - m) (c + m), (π {v : ℝ | ⌊v / w'⌋ = c'}).toReal ≤
      (200 * K * H₀ ^ 2)⁻¹ ^ 2 / 2 := by
    intro c
    rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top _ _)]
    have hlen : (2 * (m : ℝ) + 1) * w' ≤ 3 * W := by
      have hc := Nat.ceil_lt_add_one (div_nonneg hW0.le hw'0.le : 0 ≤ W / w')
      have hmr : (m : ℝ) < W / w' + 4 := by rw [hm]; push_cast; linarith
      have : (m : ℝ) * w' < W + 4 * w' := by
        have := mul_lt_mul_of_pos_right hmr hw'0
        rwa [add_mul, div_mul_cancel₀ _ hw'0.ne'] at this
      linarith
    have hcap0 : 0 ≤ K * N ^ (-S * b') := by positivity
    have h1 := sum_bins_le_Ico π hw'0 c m
    have h2 := measure_Ico_le_bins π (a := ((c : ℝ) - m) * w') (ℓ := (2 * (m : ℝ) + 1) * w') hW0
      (by positivity) hπcap hcap0
    have h3 : ((2 * (m : ℝ) + 1) * w' / W + 2) * (K * N ^ (-S * b')) ≤
        (200 * K * H₀ ^ 2)⁻¹ ^ 2 / 2 := by
      have hq : (2 * (m : ℝ) + 1) * w' / W ≤ 3 := by rw [div_le_iff₀ hW0]; linarith
      have hSb : N ^ (-S * b') = (N ^ (S * b'))⁻¹ := by rw [neg_mul, Real.rpow_neg hN0.le]
      have hXpos : 0 < N ^ (S * b') := Real.rpow_pos_of_pos hN0 _
      rw [hSb]
      calc ((2 * (m : ℝ) + 1) * w' / W + 2) * (K * (N ^ (S * b'))⁻¹)
          ≤ 5 * (K * (N ^ (S * b'))⁻¹) := by gcongr; linarith
        _ = 5 * K / N ^ (S * b') := by ring
        _ ≤ (200 * K * H₀ ^ 2)⁻¹ ^ 2 / 2 := by
            rw [div_le_iff₀ hXpos]
            have e : (200 * K * H₀ ^ 2)⁻¹ ^ 2 / 2 * N ^ (S * b') =
                N ^ (S * b') / (80000 * K ^ 2 * H₀ ^ 4) := by field_simp; ring
            rw [e, le_div_iff₀ (by positivity)]
            nlinarith
    have h4 : ∑ c' ∈ Finset.Icc (c - m) (c + m), π {v : ℝ | ⌊v / w'⌋ = c'} ≤
        ENNReal.ofReal ((200 * K * H₀ ^ 2)⁻¹ ^ 2 / 2) := by
      calc _ ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ _ := ENNReal.ofReal_le_ofReal h3
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h4
  -- the coefficient lists
  have hlist' : ∀ (q' : Fin 3 → ℤ) (c : ℤ), ∃ Lf : Finset (Fin 5 → ℤ), (Lf.card : ℝ) ≤ H₀ ∧
      ∀ β, ρ.restrict E {p | cellIdx w' (physOf p) = q' ∧ ⌊p.1.2 1 / w'⌋ = c ∧ cbin w' p = β} ≠ 0 →
        β ∈ Lf := by
    intro q' c
    set S₀ : Set (Fin 5 → ℤ) := {β | ρ.restrict E₀
      {p | cellIdx w' (physOf p) = q' ∧ ⌊p.1.2 1 / w'⌋ = c ∧ cbin w' p = β} ≠ 0} with hS₀
    have hfin : S₀.Finite := by
      apply (Fintype.piFinset (fun _ : Fin 5 => Finset.Icc ⌊-H₀ / w'⌋ ⌊H₀ / w'⌋)).finite_toSet.subset
      intro β hβ
      obtain ⟨p, ⟨-, -, hpβ⟩, hpE⟩ := exists_mem_of_restrict_ne_zero hE₀m hβ
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro e
      rw [← hpβ]
      exact floor_mem_bins hw'0 ((hE₀H p hpE).2 e)
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card _ hfin]; exact hlist q' c
    · intro β hβ
      rw [Set.Finite.mem_toFinset, hS₀, Set.mem_ofPred_eq]
      intro h0
      apply hβ
      have := (Measure.restrict_mono hEsub (le_refl ρ))
        {p | cellIdx w' (physOf p) = q' ∧ ⌊p.1.2 1 / w'⌋ = c ∧ cbin w' p = β}
      rw [h0] at this
      exact nonpos_iff_eq_zero.mp this
  -- apply the one-world row count
  have hE : ∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ (∀ e, |p.1.2 e| ≤ H₀) ∧
      |(G' (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1| ≤ graphBd H₀ N b' ∧
      |(G' (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2| ≤ graphBd H₀ N b' ∧
      |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (G' (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1 -
        (G' (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2 * p.1.2 1| ≤
        N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b' := by
    intro p hp
    obtain ⟨h1, h2⟩ := hE₀H p (hEsub hp)
    obtain ⟨h3, h4, h5⟩ := hbd p hp
    exact ⟨h1, h2, h3, h4, h5⟩
  have hpal := world_palette hH₀ hK hN hSC' (w := w') hjoint
  have hres0 : 0 ≤ N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b' := by positivity
  calc _ ≤ rowBound (N ^ (-(B : ℝ))) (N ^ (-r)) w' H₀ (N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b')
        (graphBd H₀ N b') (200 * K * H₀ ^ 2) H₀ m :=
        coarse_rows_card_le ρ hEm π (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hN0 _)
          hw'0 hw'1 (by positivity) hH0 hres0 hGb0 hH0 G' hE hpal hm3 hwin hlist' Q
    _ ≤ 10 ^ 17 * U ^ 25 :=
        rowBound_le hN hH₀ hK hUH hUK hUY hr0 hrr hr'r hr'B hrL rfl

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
