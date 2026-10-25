-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneyReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneySum
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneyArith

/-!
# The Whitney reduction of the broad near-tangent rich bound (x0284)

`whitney_reduction`: a localized bipartite rich-area estimate (`BipartiteAreaBound`, a guess of
the analytic child of x0293's split, at exponent `ε / 8`) implies the frozen statement of o117
at `ε`.  Only the rich condition `λ ≤ M(p)` and the diagonal of the close-pair count are used.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset MeasureTheory

noncomputable section

/-- Localized bipartite rich-area estimate at a fixed exponent `τ` with constants `C, a`. -/
def BipartiteAreaBound (τ C a : ℝ) : Prop :=
  ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ) (A B : Finset (Fin n))
    (δ D K μ : ℝ), 0 < δ → δ ≤ 1 / 100 → δ ≤ D → D ≤ 20 → 1 ≤ K → 1 ≤ μ →
    (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) →
    (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) →
    (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
    (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D →
      (Set.ncard {i | i ∈ A ∪ B ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K * (r / δ)) →
    (∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100) →
    (∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D / 100) →
    (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D) →
    MeasureTheory.volume {p : ℝ × ℝ |
      ENNReal.ofReal μ ≤ Finset.sum A (fun i => Set.indicator
        {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧
      ENNReal.ofReal μ ≤ Finset.sum B (fun i => Set.indicator
        {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p)}
      ≤ ENNReal.ofReal (C * δ ^ (-τ) * K ^ a * δ * ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ)))

/-- The multiplicity is at most the close-pair count (its diagonal). -/
lemma mult_le_closePairs {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (d : Fin n → Fin n → ℝ) {R : ℝ}
    (hR : 0 < R) (hd : ∀ i, d i i = 0) (p : ℝ × ℝ) :
    ∑ i, (S i).indicator (fun _ => (1 : ENNReal)) p ≤
      ∑ i, ∑ j, (if d i j < R then (S i ∩ S j).indicator (fun _ => (1 : ENNReal)) p else 0) := by
  apply Finset.sum_le_sum
  intro i _
  have h : (S i).indicator (fun _ => (1 : ENNReal)) p =
      (if d i i < R then (S i ∩ S i).indicator (fun _ => (1 : ENNReal)) p else 0) := by
    rw [hd i, if_pos hR, Set.inter_self]
  rw [h]
  exact Finset.single_le_sum (f := fun j => if d i j < R then
    (S i ∩ S j).indicator (fun _ => (1 : ENNReal)) p else 0) (fun _ _ => zero_le)
    (Finset.mem_univ i)

/-- Final real arithmetic of the reduction. -/
lemma reduction_arith {C a ε δ lam L nn : ℝ} (hC : 0 < C) (ha : 0 < a) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 2 ≤ lam) (hL1 : 1 ≤ L)
    (hL : L ≤ (3 * 20 ^ (ε / 10) / (ε / 10) + 3) * δ ^ (-(ε / 10)))
    (hn0 : 0 ≤ nn) (hn : nn ≤ 41 ^ 3 * δ ^ (-(ε / (8 * (a + 1)))) / δ)
    (hC5 : C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
      (3 * 20 ^ (ε / 10) / (ε / 10) + 3) ^ (5 / 2 : ℝ) ≤ δ ^ (-(ε / 2))) :
    C * δ ^ (-(ε / 8)) * (41 ^ 3 * δ ^ (-(ε / (8 * (a + 1))))) ^ a * δ *
      ((lam - 1) / (4 * 801 ^ 3 * L)) ^ (-(3 / 2 : ℝ)) * (L * (2 * 801 ^ 3 * nn)) ≤
      δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)) := by
  set η := ε / (8 * (a + 1)) with hη
  set C3 := 3 * 20 ^ (ε / 10) / (ε / 10) + 3 with hC3
  have hC3pos : 0 < C3 := by rw [hC3]; positivity
  have hLpos : 0 < L := by linarith
  have hlampos : 0 < lam := by linarith
  -- K^a
  have hK : (41 ^ 3 * δ ^ (-η)) ^ a = (41 ^ 3) ^ a * δ ^ (-η * a) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
  -- μ^(-3/2)
  set μ := (lam - 1) / (4 * 801 ^ 3 * L) with hμ
  have hμlow : lam / (8 * 801 ^ 3 * L) ≤ μ := by
    rw [hμ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hμ32 : μ ^ (-(3 / 2 : ℝ)) ≤ (lam / (8 * 801 ^ 3 * L)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hμlow (by norm_num)
  have hsplit : (lam / (8 * 801 ^ 3 * L)) ^ (-(3 / 2 : ℝ)) =
      (8 * 801 ^ 3) ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) * lam ^ (-(3 / 2 : ℝ)) := by
    rw [Real.div_rpow hlampos.le (by positivity)]
    rw [Real.rpow_neg hlampos.le, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 8 * 801 ^ 3 * L),
      Real.mul_rpow (by norm_num) hLpos.le]
    field_simp
  -- L^(5/2)
  have hL52 : L * L ^ (3 / 2 : ℝ) ≤ C3 ^ (5 / 2 : ℝ) * δ ^ (-(ε / 4)) := by
    have h1 : L * L ^ (3 / 2 : ℝ) = L ^ (5 / 2 : ℝ) := by
      rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
    rw [h1]
    calc L ^ (5 / 2 : ℝ) ≤ (C3 * δ ^ (-(ε / 10))) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow hLpos.le hL (by norm_num)
      _ = C3 ^ (5 / 2 : ℝ) * δ ^ (-(ε / 4)) := by
          rw [Real.mul_rpow hC3pos.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
          congr 2
          ring
  -- exponents
  have hexp : δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ * (δ ^ (-η) / δ) * δ ^ (-(ε / 4)) =
      δ ^ (-(ε / 2)) := by
    have hδne : δ ≠ 0 := hδ.ne'
    have e1 : δ ^ (-η) / δ = δ ^ (-η - 1) := by rw [Real.rpow_sub_one hδne]
    rw [e1, show δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ = δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ ^ (1 : ℝ)
      by rw [Real.rpow_one]]
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    rw [hη]
    field_simp
    ring
  have hnn : L * (2 * 801 ^ 3 * nn) ≤ L * (2 * 801 ^ 3 * (41 ^ 3 * δ ^ (-η) / δ)) := by
    apply mul_le_mul_of_nonneg_left _ hLpos.le
    apply mul_le_mul_of_nonneg_left hn (by norm_num)
  have hpos1 : 0 ≤ C * δ ^ (-(ε / 8)) * ((41 ^ 3) ^ a * δ ^ (-η * a)) * δ := by positivity
  calc C * δ ^ (-(ε / 8)) * (41 ^ 3 * δ ^ (-η)) ^ a * δ * μ ^ (-(3 / 2 : ℝ)) *
        (L * (2 * 801 ^ 3 * nn))
      = C * δ ^ (-(ε / 8)) * ((41 ^ 3) ^ a * δ ^ (-η * a)) * δ * μ ^ (-(3 / 2 : ℝ)) *
        (L * (2 * 801 ^ 3 * nn)) := by rw [hK]
    _ ≤ C * δ ^ (-(ε / 8)) * ((41 ^ 3) ^ a * δ ^ (-η * a)) * δ *
        ((8 * 801 ^ 3) ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) * lam ^ (-(3 / 2 : ℝ))) *
        (L * (2 * 801 ^ 3 * (41 ^ 3 * δ ^ (-η) / δ))) := by
        rw [← hsplit]
        apply mul_le_mul (mul_le_mul_of_nonneg_left hμ32 hpos1) hnn (by positivity)
        positivity
    _ = (C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ)) *
        (L * L ^ (3 / 2 : ℝ)) *
        (δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ * (δ ^ (-η) / δ)) * lam ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ (C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ)) *
        (C3 ^ (5 / 2 : ℝ) * δ ^ (-(ε / 4))) *
        (δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ * (δ ^ (-η) / δ)) * lam ^ (-(3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hL52 (by positivity)
    _ = (C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
        C3 ^ (5 / 2 : ℝ)) *
        (δ ^ (-(ε / 8)) * δ ^ (-η * a) * δ * (δ ^ (-η) / δ) * δ ^ (-(ε / 4))) *
        lam ^ (-(3 / 2 : ℝ)) := by ring
    _ = (C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
        C3 ^ (5 / 2 : ℝ)) * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by rw [hexp]
    _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hC5 (by positivity)
    _ = δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hδ]
        congr 2
        ring

/-- Every member of an occupied cube pair yields a witness pair, so `D ≤ 20`. -/
lemma whitneyScale_le_twenty {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)}
    (hq : ∀ i, ‖q i‖ ≤ 10) {D : ℝ} {kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)}
    (hkk : kk ∈ whitneyPairs q D) : D ≤ 20 := by
  have h := mem_whitneyPairs.mp hkk
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h.1.1
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h.1.2
  have := (h.2 i (mem_cubeSet.mpr hi) j (mem_cubeSet.mpr hj)).1
  linarith [dist_le_twenty hq i j]

/-- **The Whitney reduction.**  The localized bipartite estimate at exponent `ε / 8` implies the
frozen statement of o117 at `ε`. -/
theorem whitney_reduction (ε : ℝ) (hε : 0 < ε)
    (hA : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ BipartiteAreaBound (ε / 8) C a) :
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → ∀ lam : ℝ, 1 ≤ lam → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < δ * lam * δ ^ (-ε) then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (ε / 2) * lam ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2)} ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3/2 : ℝ))) := by
  obtain ⟨C, a, hC, ha, hbd⟩ := hA
  set t : ℝ := ε / 10 with ht
  set C3 : ℝ := 3 * 20 ^ t / t + 3 with hC3
  set C4 : ℝ := 1 + 8 * 801 ^ 3 * C3 with hC4
  set C5 : ℝ := C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
    C3 ^ (5 / 2 : ℝ) with hC5
  have htpos : 0 < t := by rw [ht]; positivity
  have hC3pos : 0 < C3 := by rw [hC3]; positivity
  have hC4pos : 0 < C4 := by rw [hC4]; positivity
  have hC5pos : 0 < C5 := by rw [hC5]; positivity
  set η : ℝ := ε / (8 * (a + 1)) with hη
  refine ⟨η, by positivity, min (C4 ^ (-1 / (3 * ε / 20))) (C5 ^ (-1 / (ε / 2))),
    lt_min (by positivity) (by positivity), ?_⟩
  intro δ hδ hδd0 hδ100 n q g hq hg hjet hsep hKT lam hlam
  have hδ1 : δ ≤ 1 := by linarith
  have hc4 : C4 ≤ δ ^ (-(3 * ε / 20)) :=
    le_rpow_neg_of_le hC4pos (by positivity) hδ (hδd0.trans (min_le_left _ _))
  have hc5 : C5 ≤ δ ^ (-(ε / 2)) :=
    le_rpow_neg_of_le hC5pos (by positivity) hδ (hδd0.trans (min_le_right _ _))
  set S : Fin n → Set (ℝ × ℝ) :=
    fun i => {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} with hS
  by_cases hsmall : lam ≤ δ ^ (-(ε / 4))
  · -- the set is empty: the diagonal of the close-pair count is the multiplicity
    refine le_trans (measure_mono (t := (∅ : Set (ℝ × ℝ))) ?_) (by rw [measure_empty]; exact zero_le)
    intro p hp
    exfalso
    obtain ⟨h1, h2, -⟩ := hp
    have hR : 0 < δ * lam * δ ^ (-ε) := by
      have : 0 < lam := by linarith
      positivity
    have hle := mult_le_closePairs S (fun i j => dist (q i) (q j)) hR (fun i => dist_self _) p
    have hlt : ENNReal.ofReal lam < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) :=
      lt_of_le_of_lt (h1.trans hle) h2
    have hθ : 0 < δ ^ (ε / 4) * lam ^ 2 := by
      have : 0 < lam := by linarith
      positivity
    rw [ENNReal.ofReal_lt_ofReal_iff hθ] at hlt
    have hlam0 : 0 < lam := by linarith
    have h3 : 1 < δ ^ (ε / 4) * lam := by nlinarith
    have h4 : δ ^ (ε / 4) * δ ^ (-(ε / 4)) = 1 := by
      rw [← Real.rpow_add hδ]; simp
    have h5 : δ ^ (ε / 4) * lam ≤ δ ^ (ε / 4) * δ ^ (-(ε / 4)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    linarith
  · push Not at hsmall
    set L : ℕ := numScales δ with hLdef
    have hLspec : 20 < δ * (3 / 2 : ℝ) ^ (L - 1) := numScales_spec hδ hδ1
    have hLle : (L : ℝ) ≤ C3 * δ ^ (-t) := numScales_le hδ hδ1 htpos
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast one_le_numScales δ
    have hδt : 1 ≤ δ ^ (-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    -- lam is large compared with the number of scales
    have hbig : 1 + 8 * 801 ^ 3 * (L : ℝ) ≤ δ ^ (-(ε / 4)) := by
      have e : δ ^ (-(3 * ε / 20)) * δ ^ (-t) = δ ^ (-(ε / 4)) := by
        rw [← Real.rpow_add hδ, ht]; congr 1; ring
      calc 1 + 8 * 801 ^ 3 * (L : ℝ) ≤ 1 + 8 * 801 ^ 3 * (C3 * δ ^ (-t)) := by linarith
        _ ≤ δ ^ (-t) + 8 * 801 ^ 3 * (C3 * δ ^ (-t)) := by linarith
        _ = C4 * δ ^ (-t) := by rw [hC4]; ring
        _ ≤ δ ^ (-(3 * ε / 20)) * δ ^ (-t) :=
            mul_le_mul_of_nonneg_right hc4 (by positivity)
        _ = δ ^ (-(ε / 4)) := e
    have hlam2 : 2 ≤ lam := by nlinarith
    have hlam1 : 1 < lam := by linarith
    set μ : ℝ := (lam - 1) / (4 * 801 ^ 3 * L) with hμ
    have hμ2 : 2 < μ := by
      rw [hμ, lt_div_iff₀ (by positivity)]
      nlinarith
    set K : ℝ := 41 ^ 3 * δ ^ (-η) with hK
    have hK1 : 1 ≤ K := by
      have : 1 ≤ δ ^ (-η) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by rw [hη]; have := ha; simp only [neg_nonpos]; positivity)
      rw [hK]; nlinarith
    -- the o117 set is inside the rich set
    have hT : {p : ℝ × ℝ | ENNReal.ofReal lam ≤ Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < δ * lam * δ ^ (-ε) then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (ε / 2) * lam ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2)} ⊆
        {p | ENNReal.ofReal lam ≤ multOn S univ p} := fun p hp => hp.1
    have hvol := volume_rich_le_sum_whitney q S hδ hδ1 hsep hq hLspec hlam1 _ hT
    refine hvol.trans ?_
    -- bound every bi-rich set
    set Y0 : ℝ := C * δ ^ (-(ε / 8)) * K ^ a * δ * μ ^ (-(3 / 2 : ℝ)) with hY0
    have hY0nn : 0 ≤ Y0 := by
      have : 0 < μ := by linarith
      rw [hY0]; positivity
    have hterm : ∀ m ∈ range L, ∀ kk ∈ whitneyPairs q (whitneyScale δ m),
        volume (biRichSet q S (whitneyScale δ m) μ kk) ≤
          ENNReal.ofReal (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card)) := by
      intro m _ kk hkk
      set D := whitneyScale δ m with hD
      have hDpos : 0 < D := whitneyScale_pos hδ m
      by_cases hDs : D ≤ 100 * δ
      · rw [biRichSet_eq_empty q S hDpos hDs hsep (by linarith) kk, measure_empty]
        exact zero_le
      · push Not at hDs
        have hb := hbd n q g (cubeSet q (D / 200) kk.1) (cubeSet q (D / 200) kk.2) δ D K μ hδ
          hδ100 (by linarith) (whitneyScale_le_twenty hq hkk) hK1 (by linarith) hq hg hjet hsep
          (fun q0 r hr _ => ncard_ball_le_of_katzTao q hq hδ hδ1 hKT
            (fun i => i ∈ cubeSet q (D / 200) kk.1 ∪ cubeSet q (D / 200) kk.2) q0 hr)
          (fun i hi j hj => (dist_lt_of_mem_cubeSet hDpos hi hj).le)
          (fun i hi j hj => (dist_lt_of_mem_cubeSet hDpos hi hj).le)
          (fun i hi j hj => cross_dist_of_mem_whitneyPairs hkk hi hj)
        refine le_trans (le_of_eq ?_) (hb.trans (le_of_eq ?_))
        · rfl
        · congr 1
          rw [hY0]
          ring
    calc ∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
          volume (biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk)
        ≤ ∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
          ENNReal.ofReal (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card)) := by
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro kk hkk
          exact hterm m hm kk hkk
      _ = ENNReal.ofReal (∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
          (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro m _
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro kk _
            positivity
          · intro m _
            apply Finset.sum_nonneg
            intro kk _
            positivity
      _ ≤ ENNReal.ofReal (Y0 * ((L : ℝ) * (2 * 801 ^ 3 * (n : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          simp_rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_sum_whitney_card_le q hδ L) hY0nn
      _ ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hn := card_le_of_katzTao q hq hδ hδ1 hKT
          have := reduction_arith (C := C) (a := a) (ε := ε) (δ := δ) (lam := lam) (L := L)
            (nn := n) hC ha hε hδ hδ1 hlam2 hL1 hLle (Nat.cast_nonneg _) hn hc5
          rw [hY0, hK, hμ]
          exact this

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
