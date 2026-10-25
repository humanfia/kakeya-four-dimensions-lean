import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphAsymp
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.RepairedCut

/-!
# The repaired velocity-graph stage of o092

`repaired_velocity_graph : RepairedVelocityGraph` (the graph child of the repaired cut in
`RepairedCut.lean`): for every requested precision `L`, the prepared incidences carry a fine-cell
velocity graph `x' = G₀ + G₁ V` with residual `H N^-L`, bounded rows, few row bins in every coarse
cell, and fine-state palette domination, on a retained set of mass `≥ 1/H`, `H` subpower.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Filter Submission.Lib.K4ContinuousKakeya
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The frozen joint cap at equal spatial scales, on fine cells. -/
lemma joint_cap_mine {ρ : Measure Inc} {π : Measure ℝ} {w wb capv : ℝ}
    (h : ∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ {p : Inc | (fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1] :
      Fin 2 → ℝ) e / w⌋) = q ∧ ⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / w⌋ = a ∧
        ⌊p.1.2 1 / wb⌋ = c} ≤ ENNReal.ofReal capv * π {v | ⌊v / wb⌋ = c})
    (f : Fin 3 → ℤ) (c : ℤ) :
    ρ (physOf ⁻¹' cellSet w f ∩ {p | ⌊p.1.2 1 / wb⌋ = c}) ≤
      ENNReal.ofReal capv * π {v | ⌊v / wb⌋ = c} := by
  have : physOf ⁻¹' cellSet w f ∩ {p | ⌊p.1.2 1 / wb⌋ = c} =
      {p : Inc | (fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1] : Fin 2 → ℝ) e / w⌋) = ![f 0, f 1] ∧
        ⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / w⌋ = f 2 ∧ ⌊p.1.2 1 / wb⌋ = c} := by
    rw [preimage_cellSet_eq_frozen]; ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [this]
  exact h _ _ _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- **The repaired velocity-graph stage of o092.** -/
theorem repaired_velocity_graph : RepairedVelocityGraph := by
  unfold RepairedVelocityGraph
  intro hMK N K hN hNt hK d κ S hd hd1 hκ hκ1 hS W ω ν ρ π T n γ j A u v F
  intro hstruct hcaps hpackets H₀ θ E₀ hprep L hL
  beta_reduce at hstruct hcaps hprep ⊢
  obtain ⟨C, hC0, hC⟩ := hMK 3 (by norm_num) (by norm_num)
  clear hMK hpackets
  obtain ⟨⟨hH₀1, hH₀sub⟩, M, hM, hprepR⟩ := hprep
  obtain ⟨hK1, hKsub⟩ := hK
  -- the fine exponent
  set B : ℕ := ⌈4 * L / (1 - d)⌉₊ + ⌈L⌉₊ + 12 with hBdef
  have hB3 : 3 ≤ B := by rw [hBdef]; omega
  have hBL : L + 10 ≤ (B : ℝ) := by
    rw [hBdef]; push_cast
    have := Nat.le_ceil L
    have : (0 : ℝ) ≤ ⌈4 * L / (1 - d)⌉₊ := Nat.cast_nonneg _
    linarith
  have hBgap : 2 * L < (1 - d) * ((B : ℝ) - 1) / 2 := by
    rw [hBdef]; push_cast
    have h1 := Nat.le_ceil (4 * L / (1 - d))
    have h2 := Nat.le_ceil L
    have hd' : 0 < 1 - d := by linarith
    have : 4 * L ≤ (1 - d) * (⌈4 * L / (1 - d)⌉₊ : ℝ) := by
      rw [div_le_iff₀ hd'] at h1; linarith
    nlinarith
  -- subpower sequences
  set Z : ℕ → ℝ := fun k => max (H₀ k) (K k) with hZdef
  have hZ1 : ∀ k, 1 ≤ Z k := fun k => le_max_of_le_left (hH₀1 k)
  have hZsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Z k ≤ N k ^ ε := fun ε hε =>
    ((hH₀sub ε hε).and (hKsub ε hε)).mono fun k hk => max_le hk.1 hk.2
  obtain ⟨J, hJt, hYsub, hdiag⟩ := exists_slow_scale N Z hN hNt hZ1 hZsub hS _ hcaps
  set b' : ℕ → ℝ := fun k => 1 / ((J k : ℝ) + 2) with hb'def
  have hb'pos : ∀ k, 0 < b' k := fun k => by simp only [hb'def]; positivity
  set Y : ℕ → ℝ := fun k => N k ^ b' k with hYdef
  set U : ℕ → ℝ := fun k => max (Z k) (Y k) with hUdef
  have hU1 : ∀ k, 1 ≤ U k := fun k => le_max_of_le_left (hZ1 k)
  have hUsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, U k ≤ N k ^ ε := fun ε hε =>
    ((hZsub ε hε).and (hYsub ε hε)).mono fun k hk => max_le hk.1 (by simpa [hYdef, hb'def] using hk.2)
  -- the worlds
  have key : ∀ k (g : Fin (W k)), ∃ (E : Set Inc) (G : (Fin 3 → ℤ) → ℝ × ℝ),
      StageHyp C (θ k g) (ρ k g) (π k g) (E₀ k g) (N k) (H₀ k) (K k) d S L (b' k) B →
        StageConcl (ρ k g) (E₀ k g) E G (N k) (H₀ k) d L (b' k) B := by
    intro k g
    by_cases h : StageHyp C (θ k g) (ρ k g) (π k g) (E₀ k g) (N k) (H₀ k) (K k) d S L (b' k) B
    · obtain ⟨E, G, hEG⟩ := graph_stage hC0.le hC (hN k) (hH₀1 k) (hK1 k) hd hB3 hL (hb'pos k) h
      exact ⟨E, G, fun _ => hEG⟩
    · exact ⟨∅, fun _ => 0, fun h' => absurd h' h⟩
  choose E' G' hEG using key
  refine ⟨fun k => 10 ^ 17 * U k ^ 25, (B : ℝ), fun k g q => ![(G' k g q).1, (G' k g q).2], E',
    ⟨fun k => ?_, fun ε hε => ?_⟩, hBL, ?_⟩
  · have := one_le_pow₀ (n := 25) (hU1 k)
    nlinarith
  · exact eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hU1 hUsub _ 25 hε
  intro R hR
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set R' : ℝ := R + B + L + 2 with hR'def
  have hR'1 : 1 < R' := by rw [hR'def]; linarith
  have hR'0 : 0 < R' := by linarith
  have hRR' : R ≤ R' := by rw [hR'def]; linarith
  have hBR' : (B : ℝ) ≤ R' := by rw [hR'def]; linarith
  have hLR' : L + 1 ≤ R' := by rw [hR'def]; linarith
  have hR'inv1 : R'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR'1.le
  have hR'B : R'⁻¹ ≤ (B : ℝ) := le_trans hR'inv1 (by
    have : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    linarith)
  have hRinv : R'⁻¹ ≤ R⁻¹ := inv_anti₀ (by linarith) hRR'
  set r₀ : ℝ := ((B : ℝ) + 1) / 2 with hr₀def
  have hr₀R' : r₀ ≤ R' := by rw [hr₀def]; linarith
  have hr₀1 : R'⁻¹ ≤ r₀ := le_trans hR'inv1 (by
    rw [hr₀def]; have : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    linarith)
  -- eventual facts
  have e4 : ∀ᶠ k in atTop, H₀ k ≤ N k :=
    (hH₀sub 1 one_pos).mono fun k hk => by simpa using hk
  have hB3' : (3 : ℝ) ≤ B := by exact_mod_cast hB3
  have hdB : (1 - d) * ((B : ℝ) - 1) ≤ (B : ℝ) - 1 := by nlinarith
  have e5 := eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hZ1 hZsub 144 1
    (by linarith [hBgap] : (0 : ℝ) < ((B : ℝ) + 1) / 2 - 2 * L)
  have e6 := eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hU1 hUsub 170 3 hL
  have e8 := eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hZ1 hZsub
    (10 ^ 25 * (C ^ 2 + 1)) 21 (by linarith [hBgap] :
      (0 : ℝ) < (1 - d) * ((B : ℝ) - 1) / 2 - 2 * L)
  have e9 := eventually_const_mul_pow_le hNt (fun k => by linarith [hN k]) hU1 hUsub 9 1
    (inv_pos.mpr (by linarith : (0 : ℝ) < R))
  have e12 : ∀ᶠ k in atTop, (B : ℝ) ≤ (J k : ℝ) + 2 := by
    have := (tendsto_natCast_atTop_atTop.comp hJt).eventually_ge_atTop (B : ℝ)
    filter_upwards [this] with k hk
    simp only [Function.comp] at hk
    linarith
  filter_upwards [hprepR R' hR'1, hcaps R' hR'1, hdiag, e4, e5, e6, e8, e9, e12] with
    k hk1 hk2 hk3 hk4 hk5 hk6 hk8 hk9 hk12
  obtain ⟨hmass₀, hworld⟩ := hk1
  obtain ⟨hcapJ, hXJ⟩ := hk3
  obtain ⟨hω0, hω1, hstr, -⟩ := hstruct k
  have hNk : 2 ≤ N k := hN k
  have hN0 : 0 < N k := by linarith
  have hN1 : 1 ≤ N k := by linarith
  have hJ2 : (0 : ℝ) < (J k : ℝ) + 2 := by positivity
  have hb'k : b' k = ((J k : ℝ) + 2)⁻¹ := by simp only [hb'def, one_div]
  have hb'range : ((J k : ℝ) + 2)⁻¹ ≤ b' k ∧ b' k ≤ (J k : ℝ) + 2 := by
    rw [hb'k]; refine ⟨le_rfl, ?_⟩
    have : ((J k : ℝ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hBJ : ((J k : ℝ) + 2)⁻¹ ≤ (B : ℝ) := le_trans (inv_le_one_of_one_le₀ (by linarith)) (by
    have : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    linarith)
  -- the frozen cells as preimages
  have hset : ∀ (w : ℝ) (q : Fin 3 → ℤ), {p : Inc | (fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1,
      p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4] : Fin 3 → ℝ) e / w⌋) = q} =
      physOf ⁻¹' cellSet w q := by
    intro w q; ext p
    simp only [Set.mem_preimage, cellSet, Set.mem_ofPred_eq, cellIdx_physOf]
  -- the stage hypotheses in every world
  have hSH : ∀ g, StageHyp C (θ k g) (ρ k g) (π k g) (E₀ k g) (N k) (H₀ k) (K k) d S L (b' k) B := by
    intro g
    obtain ⟨hθν, hθ1, hE₀m, hE₀H, hθae, hge, hle, hgrid, hfixed⟩ := hworld g
    obtain ⟨hνp, hπp, hνae, hρdom, hρsupp⟩ := hstr g
    have hMk : (1 : ℝ) ≤ M k := by exact_mod_cast (hM k).1
    have hBgrid : ∃ m : ℕ, (B : ℝ) = (m : ℝ) / (M k : ℝ) :=
      ⟨B * M k, by push_cast; field_simp⟩
    obtain ⟨hOccFin, hOccCard, -⟩ := hgrid (B : ℝ) hR'B hBR' hBgrid
    simp only [hset] at hOccFin hOccCard
    refine ⟨isFiniteMeasure_of_le (ν k g) hθν, hθ1, isFiniteMeasure_of_dom hρdom hρsupp, hE₀m,
      hle, hge, hE₀H, hOccFin, hOccCard, ?_, ?_, ?_, hk4, ?_, ?_, ?_, ?_⟩
    · -- coarse caps
      intro q
      obtain ⟨-, hρcap, -⟩ := hk2 g r₀ r₀ 1 hr₀1 hr₀R' hr₀1 hr₀R' hR'inv1 hR'1.le
      rw [preimage_cellSet_eq_frozen]
      calc _ ≤ ENNReal.ofReal (K k * N k ^ (-2 * r₀ - d * r₀)) := hρcap ![q 0, q 1] (q 2)
        _ = _ := by congr 3; ring
    · -- joint caps at the slow scale
      intro f c
      obtain ⟨-, -, hjcap⟩ := hcapJ g B B (b' k) hBJ hk12 hBJ hk12 hb'range.1 hb'range.2
      have : physOf ⁻¹' cellSet (N k ^ (-(B : ℝ))) f ∩ {p | ⌊p.1.2 1 / N k ^ (-b' k)⌋ = c} =
          {p : Inc | (fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1] : Fin 2 → ℝ) e /
            N k ^ (-(B : ℝ))⌋) = ![f 0, f 1] ∧
            ⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-(B : ℝ))⌋ = f 2 ∧
            ⌊p.1.2 1 / N k ^ (-b' k)⌋ = c} := by
        rw [preimage_cellSet_eq_frozen]; ext p
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
      rw [this]
      calc _ ≤ ENNReal.ofReal (K k * N k ^ (-2 * (B : ℝ) - d * B)) *
            π k g {v | ⌊v / N k ^ (-b' k)⌋ = c} := hjcap ![f 0, f 1] (f 2) c
        _ = _ := by congr 4; ring
    · -- palette caps at the slow scale
      intro c
      obtain ⟨hπcap, -, -⟩ := hcapJ g B B (b' k) hBJ hk12 hBJ hk12 hb'range.1 hb'range.2
      exact hπcap c
    · -- n2
      have hHZ : H₀ k ≤ Z k := le_max_left _ _
      have e : N k ^ (((B : ℝ) + 1) / 2 - 2 * L) * N k ^ (-(((B : ℝ) + 1) / 2)) =
          N k ^ (-2 * L) := by rw [← Real.rpow_add hN0]; ring_nf
      calc 144 * H₀ k * N k ^ (-(((B : ℝ) + 1) / 2))
          ≤ 144 * Z k ^ 1 * N k ^ (-(((B : ℝ) + 1) / 2)) := by rw [pow_one]; gcongr
        _ ≤ N k ^ (((B : ℝ) + 1) / 2 - 2 * L) * N k ^ (-(((B : ℝ) + 1) / 2)) := by gcongr
        _ = N k ^ (-2 * L) := e
    · -- n3
      have hHU : H₀ k ≤ U k := le_trans (le_max_left _ _) (le_max_left _ _)
      have hYU : N k ^ b' k ≤ U k := le_max_right _ _
      have hU1k := hU1 k
      have hY0 : 0 ≤ N k ^ b' k := Real.rpow_nonneg hN0.le _
      have f1 : 1 + 4 * H₀ k ≤ 5 * U k := by linarith
      have f2 : 1 + 4 * (3 * H₀ k + 1) * N k ^ b' k ≤ 17 * U k ^ 2 := by
        have : (3 * H₀ k + 1) * N k ^ b' k ≤ (4 * U k) * U k :=
          mul_le_mul (by linarith) hYU hY0 (by linarith)
        nlinarith
      have hNL : N k ^ (-L) * N k ^ L = 1 := by rw [← Real.rpow_add hN0]; simp
      have hNL0 : 0 < N k ^ (-L) := Real.rpow_pos_of_pos hN0 _
      calc N k ^ (-L) * (1 + 4 * H₀ k) * (1 + 4 * (3 * H₀ k + 1) * N k ^ b' k)
          ≤ N k ^ (-L) * (5 * U k) * (17 * U k ^ 2) := by
            gcongr
            · have : 0 ≤ H₀ k := by linarith [hH₀1 k]
              positivity
        _ = N k ^ (-L) * (170 * U k ^ 3) / 2 := by ring
        _ ≤ N k ^ (-L) * N k ^ L / 2 := by gcongr
        _ = 1 / 2 := by rw [hNL]
    · -- n4
      have hKZ : K k ≤ Z k := le_max_right _ _
      have hHZ : H₀ k ≤ Z k := le_max_left _ _
      have hZ1k := hZ1 k
      have hSb : S * b' k = S / ((J k : ℝ) + 2) := by rw [hb'k]; ring
      rw [hSb]
      have h1 : K k ^ 2 * H₀ k ^ 2 ≤ Z k ^ 2 * Z k ^ 2 := by
        have hK0 : 0 ≤ K k := by linarith [hK1 k]
        have hH0 : 0 ≤ H₀ k := by linarith [hH₀1 k]
        gcongr
      have h2 : Z k ^ 2 * Z k ^ 2 ≤ Z k ^ 7 := by
        rw [← pow_add]; exact pow_le_pow_right₀ hZ1k (by norm_num)
      have h3 : (0 : ℝ) ≤ Z k ^ 7 := by positivity
      linarith
    · -- n5
      have hKZ : K k ≤ Z k := le_max_right _ _
      have hHZ : H₀ k ≤ Z k := le_max_left _ _
      have h1 : K k * H₀ k ^ 20 ≤ Z k * Z k ^ 20 := by
        have hK0 : 0 ≤ K k := by linarith [hK1 k]
        have hH0 : 0 ≤ H₀ k := by linarith [hH₀1 k]
        gcongr
      have h2 : Z k * Z k ^ 20 = Z k ^ 21 := by ring
      have hC2 : 0 ≤ C ^ 2 + 1 := by positivity
      calc 10 ^ 25 * K k * (C ^ 2 + 1) * H₀ k ^ 20 = 10 ^ 25 * (C ^ 2 + 1) * (K k * H₀ k ^ 20) := by
            ring
        _ ≤ 10 ^ 25 * (C ^ 2 + 1) * Z k ^ 21 := by rw [← h2]; gcongr
        _ ≤ _ := hk8
  have hSC : ∀ g, StageConcl (ρ k g) (E₀ k g) (E' k g) (G' k g) (N k) (H₀ k) d L (b' k) B :=
    fun g => hEG k g (hSH g)
  have hρfin : ∀ g, IsFiniteMeasure (ρ k g) := fun g => (hSH g).2.2.1
  -- sizes
  have hU1k := hU1 k
  have hHU : H₀ k ≤ U k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKU : K k ≤ U k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hYU : N k ^ b' k ≤ U k := le_max_right _ _
  have hH₀1k := hH₀1 k
  have hU25 : U k ≤ U k ^ 25 := le_self_pow₀ hU1k (by norm_num)
  have hU3 : U k ^ 3 ≤ U k ^ 25 := pow_le_pow_right₀ hU1k (by norm_num)
  have hU4 : U k ^ 4 ≤ U k ^ 25 := pow_le_pow_right₀ hU1k (by norm_num)
  have hGbU : graphBd (H₀ k) (N k) (b' k) ≤ 104 * U k ^ 3 := graphBd_le hNk hH₀1k hHU hYU
  have hGb0 : 0 ≤ graphBd (H₀ k) (N k) (b' k) := by unfold graphBd; positivity
  have hHout1 : graphBd (H₀ k) (N k) (b' k) ≤ 10 ^ 17 * U k ^ 25 := by nlinarith
  have hHout2 : (1 + 4 * H₀ k) * graphBd (H₀ k) (N k) (b' k) ≤ 10 ^ 17 * U k ^ 25 := by
    have : (1 + 4 * H₀ k) * graphBd (H₀ k) (N k) (b' k) ≤ (5 * U k) * (104 * U k ^ 3) :=
      mul_le_mul (by linarith) hGbU hGb0 (by positivity)
    nlinarith
  have hHout3 : 200 * K k * H₀ k ^ 2 ≤ 10 ^ 17 * U k ^ 25 := by
    have : K k * H₀ k ^ 2 ≤ U k * U k ^ 2 := by
      have hK0 : 0 ≤ K k := by linarith [hK1 k]
      have hH0 : 0 ≤ H₀ k := by linarith
      gcongr
    have e : U k * U k ^ 2 = U k ^ 3 := by ring
    nlinarith
  refine ⟨?_, fun g => ?_⟩
  · -- the retained mass
    have hHpos : 0 < H₀ k := by linarith
    have hterm : ∀ (g : Fin (W k)) (F : Set Inc), ENNReal.ofReal (ω k g) * (ρ k g).restrict F Set.univ =
        ENNReal.ofReal (ω k g * ((ρ k g).restrict F Set.univ).toReal) := by
      intro g F
      haveI := hρfin g
      rw [ENNReal.ofReal_mul (hω0 g), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hsum : ∀ F : Fin (W k) → Set Inc, ∑ g, ENNReal.ofReal (ω k g) * (ρ k g).restrict (F g) Set.univ =
        ENNReal.ofReal (∑ g, ω k g * ((ρ k g).restrict (F g) Set.univ).toReal) := by
      intro F
      rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => mul_nonneg (hω0 g) ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun g _ => hterm g (F g)
    rw [hsum (E₀ k)] at hmass₀
    rw [hsum (E' k)]
    have h0 : (H₀ k)⁻¹ ≤ ∑ g, ω k g * ((ρ k g).restrict (E₀ k g) Set.univ).toReal :=
      (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun g _ =>
        mul_nonneg (hω0 g) ENNReal.toReal_nonneg)).mp hmass₀
    have h1 : ∑ g, ω k g * ((ρ k g).restrict (E₀ k g) Set.univ).toReal ≤
        ∑ g, ω k g * (2 * ((ρ k g).restrict (E' k g) Set.univ).toReal +
          1 / (100 * H₀ k) + 1 / (4 * H₀ k)) :=
      Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hSC g).2.2.1 (hω0 g)
    have h2 : ∑ g, ω k g * (2 * ((ρ k g).restrict (E' k g) Set.univ).toReal +
          1 / (100 * H₀ k) + 1 / (4 * H₀ k)) =
        2 * ∑ g, ω k g * ((ρ k g).restrict (E' k g) Set.univ).toReal +
          (1 / (100 * H₀ k) + 1 / (4 * H₀ k)) * ∑ g, ω k g := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [hω1, mul_one] at h2
    apply ENNReal.ofReal_le_ofReal
    have h3 : (10 ^ 17 * U k ^ 25)⁻¹ ≤ (3 * H₀ k)⁻¹ := by
      apply inv_anti₀ (by positivity); nlinarith
    have h4 : (3 * H₀ k)⁻¹ = (H₀ k)⁻¹ / 3 := by field_simp
    have h5 : 1 / (100 * H₀ k) + 1 / (4 * H₀ k) = (H₀ k)⁻¹ * (26 / 100) := by field_simp; ring
    rw [h5] at h2
    have h6 : 0 ≤ (H₀ k)⁻¹ := inv_nonneg.mpr hHpos.le
    show (10 ^ 17 * U k ^ 25)⁻¹ ≤ _
    linarith
  · -- the world `g`
    obtain ⟨hθν, hθ1, hE₀m, hE₀H, hθae, hge, hle, hgrid, hfixed⟩ := hworld g
    obtain ⟨hνp, hπp, hνae, hρdom, hρsupp⟩ := hstr g
    haveI := hρfin g
    have hSCg := hSC g
    obtain ⟨hEm, hEsub, -, hbd, hheavy⟩ := hSC g
    simp only [← cellIdx_physOf]
    refine ⟨hEm, hEsub, ?_, ?_, ?_⟩
    · -- graph bounds and residual
      intro p hp
      obtain ⟨b1, b2, b3⟩ := hbd p hp
      refine ⟨fun e => ?_, ?_⟩
      · fin_cases e
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith
      · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        have e : p.1.2 3 + 2 * p.2 * p.1.2 4 = p.1.2 3 + 2 * p.1.2 4 * p.2 := by ring
        rw [e]
        have hNL : 0 ≤ N k ^ (-L) := (Real.rpow_pos_of_pos hN0 _).le
        calc _ ≤ N k ^ (-L) * (1 + 4 * H₀ k) * graphBd (H₀ k) (N k) (b' k) := b3
          _ = N k ^ (-L) * ((1 + 4 * H₀ k) * graphBd (H₀ k) (N k) (b' k)) := by ring
          _ ≤ N k ^ (-L) * (10 ^ 17 * U k ^ 25) := by gcongr
          _ = 10 ^ 17 * U k ^ 25 * N k ^ (-L) := by ring
    · -- coarse row lists
      intro r hr1 hr2 hrL q
      have hRpos : 0 < R := by linarith
      have hr0 : 0 < r := lt_of_lt_of_le (inv_pos.mpr hRpos) hr1
      have hMk : (1 : ℝ) ≤ M k := by exact_mod_cast (hM k).1
      have hMpos : (0 : ℝ) < M k := by linarith
      set r' : ℝ := (⌈r * M k⌉₊ : ℝ) / M k with hr'def
      have hrr' : r ≤ r' := by rw [hr'def, le_div_iff₀ hMpos]; exact Nat.le_ceil _
      have hr'lt : r' < r + 1 / M k := by
        rw [hr'def, div_lt_iff₀ hMpos]
        have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ r * M k)
        calc (⌈r * M k⌉₊ : ℝ) < r * M k + 1 := this
          _ = (r + 1 / M k) * M k := by field_simp
      have hr'grid : ∃ m : ℕ, r' = (m : ℝ) / (M k : ℝ) := ⟨⌈r * M k⌉₊, rfl⟩
      have h1M : 1 / (M k : ℝ) ≤ 1 := by rw [div_le_one hMpos]; exact hMk
      have hr'R' : r' ≤ R' := by linarith
      have hr'R'' : R'⁻¹ ≤ r' := le_trans (le_trans hRinv hr1) hrr'
      have hr'B : r' ≤ (B : ℝ) := by linarith
      have hr'r : N k ^ (r' - r) ≤ H₀ k :=
        le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (hM k).2
      obtain ⟨-, -, hjcap⟩ := hk2 g B B r' hR'B hBR' hR'B hBR' hr'R'' hr'R'
      have e0 : -2 * (B : ℝ) - d * B = -(2 + d) * B := by ring
      rw [e0] at hjcap
      have hjoint' := joint_cap_mine hjcap
      obtain ⟨hπcap, -, -⟩ := hcapJ g B B (b' k) hBJ hk12 hBJ hk12 hb'range.1 hb'range.2
      obtain ⟨-, -, -, -, hlist⟩ := hgrid r' hr'R'' hr'R' hr'grid
      have hlist' : ∀ (q' : Fin 3 → ℤ) (c : ℤ), ({β : Fin 5 → ℤ | (ρ k g).restrict (E₀ k g)
          {p | cellIdx (N k ^ (-r')) (physOf p) = q' ∧ ⌊p.1.2 1 / N k ^ (-r')⌋ = c ∧
            cbin (N k ^ (-r')) p = β} ≠ 0}.ncard : ℝ) ≤ H₀ k := by
        intro q' c
        have := hlist q' c
        simp only [← cellIdx_physOf] at this
        exact this
      have hwin9 : 9 * N k ^ b' k ≤ N k ^ r := by
        have h1 : 9 * U k ^ 1 ≤ N k ^ R⁻¹ := hk9
        have h2 : N k ^ R⁻¹ ≤ N k ^ r := Real.rpow_le_rpow_of_exponent_le hN1 hr1
        rw [pow_one] at h1
        linarith
      have hX : 400000 * K k ^ 3 * H₀ k ^ 4 ≤ N k ^ (S * b' k) := by
        have hSb : S * b' k = S / ((J k : ℝ) + 2) := by rw [hb'k]; ring
        rw [hSb]
        have hKZ : K k ≤ Z k := le_max_right _ _
        have hHZ : H₀ k ≤ Z k := le_max_left _ _
        have h1 : K k ^ 3 * H₀ k ^ 4 ≤ Z k ^ 3 * Z k ^ 4 := by
          have hK0 : 0 ≤ K k := by linarith [hK1 k]
          have hH0 : 0 ≤ H₀ k := by linarith
          gcongr
        have h2 : Z k ^ 3 * Z k ^ 4 = Z k ^ 7 := by ring
        linarith
      have hrows := world_rows hNk hH₀1k (hK1 k) (hb'pos k) hE₀m hSCg hE₀H hjoint' hπcap hlist'
        hHU hKU hYU hr0.le hrr' hr'r hr'B hrL hwin9 hX q
      -- the frozen row bins
      set ψ : (Fin 2 → ℤ) → ℤ × ℤ := fun v => (v 0, v 1) with hψ
      have hψinj : Function.Injective ψ := by
        intro v w h
        simp only [hψ, Prod.mk.injEq] at h
        funext e; fin_cases e
        · exact h.1
        · exact h.2
      have hiff : ∀ (x : ℝ × ℝ) (v : Fin 2 → ℤ),
          ((fun e => ⌊(![x.1, x.2] : Fin 2 → ℝ) e / N k ^ (-r)⌋) = v) ↔
            rowPair (N k ^ (-r)) x = ψ v := by
        intro x v
        simp only [funext_iff, Fin.forall_fin_two, rowPair, hψ, Prod.mk.injEq,
          Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      simp only [hiff]
      calc _ = ({x : ℤ × ℤ | (ρ k g).restrict (E' k g) {p | cellIdx (N k ^ (-r)) (physOf p) = q ∧
            rowPair (N k ^ (-r)) (G' k g (cellIdx (N k ^ (-(B : ℝ))) (physOf p))) = x} ≠ 0}.ncard :
              ℝ) := by
            congr 1
            exact Set.ncard_preimage_of_injective_subset_range (f := ψ)
              (s := {x : ℤ × ℤ | (ρ k g).restrict (E' k g) {p | cellIdx (N k ^ (-r)) (physOf p) = q ∧
                rowPair (N k ^ (-r)) (G' k g (cellIdx (N k ^ (-(B : ℝ))) (physOf p))) = x} ≠ 0})
              hψinj (by
                rintro x -
                exact ⟨![x.1, x.2], by simp [hψ]⟩)
        _ ≤ _ := hrows
    · -- fine-state palette
      intro r hr1 hr2 q c
      have hrR'1 : R'⁻¹ ≤ r := le_trans hRinv hr1
      have hrR'2 : r ≤ R' := le_trans hr2 hRR'
      obtain ⟨-, -, hjcap⟩ := hk2 g B B r hR'B hBR' hR'B hBR' hrR'1 hrR'2
      have e0 : -2 * (B : ℝ) - d * B = -(2 + d) * B := by ring
      rw [e0] at hjcap
      have hpal := world_palette hH₀1k (hK1 k) hNk hSCg (w := N k ^ (-r))
        (joint_cap_mine hjcap) q c
      have hH' : ENNReal.ofReal (200 * K k * H₀ k ^ 2) ≤ ENNReal.ofReal (10 ^ 17 * U k ^ 25) :=
        ENNReal.ofReal_le_ofReal hHout3
      calc _ ≤ _ := hpal
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH' zero_le) zero_le

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
