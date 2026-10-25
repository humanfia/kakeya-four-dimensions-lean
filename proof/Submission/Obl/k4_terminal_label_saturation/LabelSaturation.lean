-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/LabelSaturation.lean
import Submission.Obl.k4_terminal_label_saturation.SatNumerics
import Submission.Obl.k4_terminal_label_saturation.SplitInterfaces
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

/-!
# Terminal label saturation for the frozen problem sequence

`label_saturation`: for every problem satisfying `prob`, every true terminal
system at horizon `h` (fixed format, slack `N^o(1)`, frequently) is, after
saturation and pruning, a *known* true system: the same horizon, true floors,
terminal-observation lists of size at most the slack knowing every selected
incidence, coverage, and fixed-format measurable list membership.  This is the
statement `known` of the proposed `k4_terminal_label_saturation` child of o156
(x0575, commit 401a7a3), with paper Lemma 2.8 as proof.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set Filter
open scoped ENNReal

/-- A known true terminal system (x0575's `known`). -/
noncomputable def knownTrue : (ℕ → ℝ) → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) →
    ((k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) →
    ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) →
    (ℝ → ℝ) → ℝ → ℝ → Prop :=
  fun N W ω ν E B f L h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧
    κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T))
      (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ)))
      (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')),
      N k ^ (h - ε) ≤ (2 : ℝ) ^ T ∧ (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b)
        (R b) (A b) (F b)
        (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤
          ((ν k (γ b)).prod MeasureTheory.volume) (F b) ∧
          ∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) *
        ((ν k (γ b)).prod MeasureTheory.volume) (F b) ∧
      (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ) ∧
      (∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) p)} ∧
        ∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ | b ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L)
          ((i, fun z : Fin 6 => r z.castSucc), r 6))})

/-- The format budget of saturation is polynomial. -/
theorem sat_format_budget {Nk L B : ℝ} {M Mp C' : ℕ} (hNk : 2 ≤ Nk) (hL : 0 ≤ L)
    (hB0 : 0 < B) (hB : B ≤ Nk ^ Mp) (hC' : (C' : ℝ) ≤ Nk ^ M) :
    Nk ^ M + (2 + ((binCount (2 * Nk ^ M) B (δ Nk L) + 1 : ℕ) +
      (binCount (2 * Nk ^ M) B (δ Nk L) * (C' * 6) : ℕ) : ℝ)) ≤
      Nk ^ (2 * M + Mp + ⌈L⌉₊ + 6) := by
  have hNk1 : 1 ≤ Nk := by linarith
  have hNk0 : 0 < Nk := by linarith
  have hδ : Nk ^ (-L) ≤ δ Nk L := delta_ge_rpow (by linarith) hL
  have hδ0 : 0 < δ Nk L := by unfold δ; positivity
  set X : ℝ := Nk ^ (M + Mp + ⌈L⌉₊) with hX
  have hX1 : 1 ≤ X := one_le_pow₀ hNk1
  have hLc : Nk ^ L ≤ Nk ^ (⌈L⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hNk1 (Nat.le_ceil L)
  have hinvδ : (δ Nk L)⁻¹ ≤ Nk ^ (⌈L⌉₊) := by
    calc (δ Nk L)⁻¹ ≤ (Nk ^ (-L))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hNk0 _) hδ
      _ = Nk ^ L := by rw [Real.rpow_neg hNk0.le, inv_inv]
      _ ≤ Nk ^ (⌈L⌉₊ : ℝ) := hLc
      _ = Nk ^ (⌈L⌉₊) := Real.rpow_natCast _ _
  have hratio : 2 * Nk ^ M * B / δ Nk L ≤ 2 * X := by
    rw [div_eq_mul_inv, hX, pow_add, pow_add]
    have h1 : 0 ≤ 2 * Nk ^ M := by positivity
    calc 2 * Nk ^ M * B * (δ Nk L)⁻¹ ≤ 2 * Nk ^ M * Nk ^ Mp * Nk ^ (⌈L⌉₊) := by
          gcongr
      _ = 2 * (Nk ^ M * Nk ^ Mp * Nk ^ (⌈L⌉₊)) := by ring
  have hbin : (binCount (2 * Nk ^ M) B (δ Nk L) : ℝ) ≤ 7 * X := by
    unfold binCount
    push_cast
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (2 * Nk ^ M * B / δ Nk L) by positivity)
    nlinarith
  have hCX : (C' : ℝ) ≤ X := by
    refine hC'.trans ?_
    rw [hX]
    exact pow_le_pow_right₀ hNk1 (by omega)
  have hMX : Nk ^ M ≤ X := by rw [hX]; exact pow_le_pow_right₀ hNk1 (by omega)
  have h64 : (64 : ℝ) ≤ Nk ^ 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Nk ^ 6 := pow_le_pow_left₀ (by norm_num) hNk 6
  have htarget : Nk ^ (2 * M + Mp + ⌈L⌉₊ + 6) = X * Nk ^ M * Nk ^ 6 := by
    rw [hX, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [htarget]
  push_cast
  have hb0 : (0 : ℝ) ≤ binCount (2 * Nk ^ M) B (δ Nk L) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C' := Nat.cast_nonneg _
  have hNM1 : 1 ≤ Nk ^ M := one_le_pow₀ hNk1
  have hstep : (binCount (2 * Nk ^ M) B (δ Nk L) : ℝ) * (C' * 6) ≤ 7 * X * (Nk ^ M * 6) := by
    apply mul_le_mul hbin (by nlinarith) (by positivity) (by positivity)
  nlinarith [mul_le_mul hMX hNM1 (by positivity) (by positivity)]

/-- **Terminal label saturation** (paper Lemma 2.8 for the frozen problem sequence). -/
theorem label_saturation : ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G → ∀ h : ℝ, trueSys N W ω ν E B f L h →
      knownTrue N W ω ν E B f L h := by
  intro N K L d S η W ω ν E P B f g G hprob h htrue
  obtain ⟨hN, hNt, _, hL, _, _, _, _, htemp, hdens, _, _, htypical, _, _⟩ := hprob
  obtain ⟨Mp, Dp, htemp⟩ := htemp
  obtain ⟨M, D, hT⟩ := htrue
  refine ⟨2 * M + Mp + ⌈L⌉₊ + 6, max D 4, fun ε hε => ?_⟩
  set M' := 2 * M + Mp + ⌈L⌉₊ + 6 with hM'
  set τ : ℝ := ε / 20 with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨c, hc, hcev⟩ := htypical L τ hL.le le_rfl hτ0
  set ε₁ : ℝ := min (ε / 20) (c / 4) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁a : ε₁ ≤ ε / 20 := min_le_left _ _
  have hε₁c : ε₁ ≤ c / 4 := min_le_right _ _
  -- eventual numerical conditions
  have hev1 : ∀ᶠ k in atTop, 8 ≤ N k ^ (c - ε₁) :=
    Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow hNt (by linarith) 8
  have hev2 : ∀ᶠ k in atTop, 3200 ≤ N k ^ (ε - 6 * ε₁ - τ) :=
    Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow hNt (by rw [hτ]; linarith) 3200
  refine ((hT ε₁ hε₁0).and_eventually ((hcev.and hev1).and hev2)).mono ?_
  rintro k ⟨⟨κ₀, hκ₀1, hκ₀N, T, C', γ, j, cc, uu, Q, R, A, F, hT1, hT2, hC', hdisj, hchart, hcov⟩,
    ⟨htypk, h8⟩, h3200⟩
  -- notation at sample k
  have hNk2 : 2 ≤ N k := hN k
  have hNk1 : 1 ≤ N k := by linarith
  have hNk0 : 0 < N k := by linarith
  have hω : ∀ γ₁, 0 ≤ ω k γ₁ := (htemp k).2.1
  have hω1 : ∑ γ₁, ω k γ₁ = 1 := (htemp k).2.2.1
  have hνB := (htemp k).2.2.2.1
  haveI : ∀ γ₁, IsProbabilityMeasure (ν k γ₁) := fun γ₁ => (hνB γ₁).1
  have hBpos : ∀ γ₁, 0 < B k γ₁ := fun γ₁ => (hνB γ₁).2.1
  have hBle : ∀ γ₁, B k γ₁ ≤ N k ^ Mp := fun γ₁ => (hνB γ₁).2.2.1
  set κ' : ℝ := 3200 * κ₀ ^ 6 * N k ^ τ with hκ'
  have hτ1 : 1 ≤ N k ^ τ := Real.one_le_rpow hNk1 hτ0.le
  have hκ₀κ' : κ₀ ≤ κ' := by
    have h6 : κ₀ ≤ κ₀ ^ 6 := by
      calc κ₀ = κ₀ ^ 1 := (pow_one κ₀).symm
        _ ≤ κ₀ ^ 6 := pow_le_pow_right₀ hκ₀1 (by norm_num)
    calc κ₀ ≤ 3200 * κ₀ ^ 6 * 1 := by nlinarith
      _ ≤ κ' := by rw [hκ']; exact mul_le_mul_of_nonneg_left hτ1 (by positivity)
  have hκ'pos : 0 < κ' := by positivity
  -- the typical cap at this sample
  have htyp : ∑ γ₁, ENNReal.ofReal (ω k γ₁) * (((ν k γ₁).prod volume).restrict (E k γ₁))
      {p | ENNReal.ofReal (N k ^ (-f L + τ)) < g k γ₁ L (obs (B k γ₁) (δ (N k) L) p)} ≤
      ENNReal.ofReal (N k ^ (-c)) := by
    refine le_trans ?_ htypk
    apply Finset.sum_le_sum
    intro γ₁ _
    apply mul_le_mul' le_rfl
    apply measure_mono
    intro p hp
    exact Or.inr hp
  -- the budget conditions
  have h8κ : 8 * κ₀ ≤ N k ^ c := by
    calc 8 * κ₀ ≤ N k ^ (c - ε₁) * N k ^ ε₁ := mul_le_mul h8 hκ₀N (by linarith) (by positivity)
      _ = N k ^ c := by rw [← Real.rpow_add hNk0]; ring_nf
  have hnum := sat_budget (F := f L) hNk1 hκ₀1 hτ0.le h8κ
  have hbud : ∀ γ₀ : Fin (W k), N k ^ M + (2 + ((binCount (2 * N k ^ M) (B k γ₀) (δ (N k) L) + 1) +
      binCount (2 * N k ^ M) (B k γ₀) (δ (N k) L) * (C' * 6))) ≤ N k ^ M' := by
    intro γ₀
    have := sat_format_budget (M := M) (Mp := Mp) (C' := C') hNk2 hL.le (hBpos γ₀) (hBle γ₀) hC'
    exact_mod_cast this
  obtain ⟨C'', e, lst, hC'', he, hcharts, hfloor, hknow, hcov', hcard, hlstm, _⟩ :=
    saturate_prune_sample (M' := M') (D' := max D 4) (N k) L (ω k) (ν k) (E k) (B k)
      (fun γ₁ => g k γ₁ L) (κ₀ := κ₀) (κ' := κ') (n₀ := N k ^ (-f L))
      (cap := N k ^ (-f L + τ)) (H := κ') γ j cc uu Q R A F hNk1 hω hω1 hBpos hκ₀1 hκ₀κ'
      (Real.rpow_pos_of_pos hNk0 _) (Real.rpow_pos_of_pos hNk0 _).le hκ'pos le_rfl
      (fun γ₁ => (hdens k γ₁ L hL.le le_rfl).1) (fun γ₁ => (hdens k γ₁ L hL.le le_rfl).2)
      hdisj hchart hcov (ENNReal.ofReal (N k ^ (-c))) ENNReal.ofReal_ne_top htyp
      (by omega) le_rfl hbud hnum
  -- package the known sample
  refine ⟨κ', by linarith, ?_, T, C'', fun i => γ (e i), fun i => j (e i), fun i => cc (e i),
    fun i => uu (e i), fun i => Q (e i), fun i => R (e i), fun i => A (e i),
    fun i => satSel γ j κ₀ (δ (N k) L) (B k) cc uu Q R κ' F (e i), lst, ?_, ?_, ?_, ?_, ?_, hcov',
    hcard, ?_⟩
  · -- slack
    calc κ' = 3200 * κ₀ ^ 6 * N k ^ τ := rfl
      _ ≤ 3200 * (N k ^ ε₁) ^ 6 * N k ^ τ := by gcongr
      _ = 3200 * N k ^ (6 * ε₁ + τ) := by
          rw [← Real.rpow_natCast (N k ^ ε₁) 6, ← Real.rpow_mul hNk0.le, mul_assoc,
            ← Real.rpow_add hNk0]
          push_cast
          ring_nf
      _ ≤ N k ^ (ε - 6 * ε₁ - τ) * N k ^ (6 * ε₁ + τ) :=
          mul_le_mul_of_nonneg_right h3200 (by positivity)
      _ = N k ^ ε := by rw [← Real.rpow_add hNk0]; ring_nf
  · calc N k ^ (h - ε) ≤ N k ^ (h - ε₁) :=
          Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith)
      _ ≤ (2 : ℝ) ^ T := hT1
  · calc (2 : ℝ) ^ T ≤ N k ^ (h + ε₁) := hT2
      _ ≤ N k ^ (h + ε) := Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith)
  · calc (C'' : ℝ) ≤ C' := by exact_mod_cast hC''
      _ ≤ N k ^ M := hC'
      _ ≤ N k ^ M' := pow_le_pow_right₀ hNk1 (by omega)
  · intro i i' hii' hγ hj
    exact hdisj (e i) (e i') (fun h' => hii' (he h')) hγ hj
  · intro i
    exact chart_mono hNk1 le_rfl le_rfl hκ'pos le_rfl (hBpos _).le (hcharts i)
      (fun _ => ⟨hfloor i, hknow i⟩)
  · intro γ₀ i
    refine ⟨(hlstm γ₀ i).1, fun i' => ?_⟩
    refine Submission.Lib.K4RepresentativeAssembly.fmt_mono ((hlstm γ₀ i).2 i') ?_ (le_max_right D 4)
    have hb := hbud γ₀
    have hNM : (0 : ℝ) ≤ N k ^ M := by positivity
    have : (((binCount (2 * N k ^ M) (B k γ₀) (δ (N k) L) + 1 : ℕ) : ℝ) +
        ((binCount (2 * N k ^ M) (B k γ₀) (δ (N k) L) * (C' * 6) : ℕ) : ℝ)) ≤ N k ^ M' := by
      push_cast at hb ⊢
      linarith
    exact_mod_cast this

end Submission.Obl.k4_terminal_label_saturation
