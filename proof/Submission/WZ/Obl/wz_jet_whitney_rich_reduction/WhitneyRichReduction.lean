-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneyRichReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneyFar

/-!
# Proof of the reduction child `wz_jet_whitney_rich_reduction` (x0284)

The frozen type below is the one x0293 sent on 2026-10-12T10:16Z for the reduction child of
their split of o117.  Here it is proved as `whitney_rich_reduction_proof` in this obligation's
namespace, ready to be moved to the child's module once the split is accepted.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset MeasureTheory


open Classical in
lemma card_incident_ge {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (p : ℝ × ℝ) {lam : ℝ}
    (h1 : ENNReal.ofReal lam ≤ multOn S univ p) :
    lam ≤ ((univ.filter (fun i => p ∈ S i)).card : ℝ) := by
  rw [multOn_eq_card, ← ENNReal.ofReal_natCast] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp h1

open Classical in
/-- Few close pairs: at least half of the ordered incident pairs are far. -/
lemma far_half {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (d : Fin n → Fin n → ℝ) {R θ lam : ℝ}
    (p : ℝ × ℝ) (hθ : θ ≤ lam ^ 2 / 2) (hθ0 : 0 < θ) (hlam0 : 0 ≤ lam)
    (h1 : ENNReal.ofReal lam ≤ multOn S univ p)
    (h2 : (∑ i, ∑ j, (if d i j < R then (S i ∩ S j).indicator (fun _ => (1 : ENNReal)) p
      else 0)) < ENNReal.ofReal θ) :
    ((univ.filter (fun i => p ∈ S i)).card : ℝ) ^ 2 / 2 ≤
      ((((univ.filter (fun i => p ∈ S i)) ×ˢ (univ.filter (fun i => p ∈ S i))).filter
        (fun ij => R ≤ d ij.1 ij.2)).card : ℝ) := by
  set F := univ.filter (fun i => p ∈ S i) with hF
  have hcardF : lam ≤ (F.card : ℝ) := card_incident_ge S p h1
  have hclose : ((((F ×ˢ F).filter (fun ij => d ij.1 ij.2 < R)).card : ℝ)) < θ := by
    rw [closeCount_eq_card, ← ENNReal.ofReal_natCast] at h2
    exact (ENNReal.ofReal_lt_ofReal_iff hθ0).mp h2
  have hsplit := Finset.card_filter_add_card_filter_not (s := F ×ˢ F)
    (fun ij : Fin n × Fin n => R ≤ d ij.1 ij.2)
  have hneg : (F ×ˢ F).filter (fun ij => ¬ R ≤ d ij.1 ij.2) =
      (F ×ˢ F).filter (fun ij => d ij.1 ij.2 < R) := by
    apply Finset.filter_congr
    intro ij _
    exact not_le
  rw [hneg, Finset.card_product] at hsplit
  have hs : ((((F ×ˢ F).filter (fun ij => R ≤ d ij.1 ij.2)).card : ℝ)) +
      (((F ×ˢ F).filter (fun ij => d ij.1 ij.2 < R)).card : ℝ) =
      (F.card : ℝ) * F.card := by exact_mod_cast hsplit
  have hl2 : lam ^ 2 ≤ (F.card : ℝ) ^ 2 := pow_le_pow_left₀ hlam0 hcardF 2
  have hsq : (F.card : ℝ) ^ 2 = (F.card : ℝ) * F.card := by ring
  linarith

theorem whitney_rich_reduction_proof : ∀ ε : ℝ, 0 < ε → (∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → ∀ (A B : Finset (Fin n)) (D K mu : ℝ), δ ≤ D → D ≤ 20 → 1 ≤ K → (∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100) → (∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D / 100) → (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D → (Set.ncard {i : Fin n | i ∈ (A ∪ B) ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K * (r / δ)) → 1 ≤ mu → δ * mu * δ ^ (-8 * (ε / 8)) ≤ D → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal mu ≤ Finset.sum A (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ ENNReal.ofReal mu ≤ Finset.sum B (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum A (fun i => Finset.sum B (fun j => Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (4 * (ε / 8)) * mu ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (mu ^ 2 / 100)} ≤ ENNReal.ofReal (C * δ ^ (-(ε / 8)) * K ^ a * δ * ((A.card : ℝ) + (B.card : ℝ)) * mu ^ (-(3/2 : ℝ)))) → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → ∀ lam : ℝ, 1 ≤ lam → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < δ * lam * δ ^ (-ε) then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (ε / 2) * lam ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2)} ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3/2 : ℝ))) := by
  intro ε hε hA
  obtain ⟨a, ha, C, hC, hbd⟩ := hA
  set t : ℝ := ε / 10 with ht
  set C3 : ℝ := 3 * 20 ^ t / t + 3 with hC3
  set C4 : ℝ := 1 + 8 * 801 ^ 3 * C3 with hC4
  set C5 : ℝ := C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
    C3 ^ (5 / 2 : ℝ) with hC5
  set C6 : ℝ := 6400 * 801 ^ 6 * C3 ^ 2 with hC6
  have htpos : 0 < t := by rw [ht]; positivity
  have hC3pos : 0 < C3 := by rw [hC3]; positivity
  have hC4pos : 0 < C4 := by rw [hC4]; positivity
  have hC5pos : 0 < C5 := by rw [hC5]; positivity
  have hC6pos : 0 < C6 := by rw [hC6]; positivity
  set η : ℝ := ε / (8 * (a + 1)) with hη
  refine ⟨η, by positivity, min (min (C4 ^ (-1 / (3 * ε / 20))) (C5 ^ (-1 / (ε / 2))))
    (C6 ^ (-1 / (ε / 20))), lt_min (lt_min (by positivity) (by positivity)) (by positivity), ?_⟩
  intro δ hδ hδd0 hδ100 n q g hq hg hjet hsep hKT lam hlam
  have hδ1 : δ ≤ 1 := by linarith
  have hc4 : C4 ≤ δ ^ (-(3 * ε / 20)) :=
    le_rpow_neg_of_le hC4pos (by positivity) hδ
      ((hδd0.trans (min_le_left _ _)).trans (min_le_left _ _))
  have hc5 : C5 ≤ δ ^ (-(ε / 2)) :=
    le_rpow_neg_of_le hC5pos (by positivity) hδ
      ((hδd0.trans (min_le_left _ _)).trans (min_le_right _ _))
  have hc6 : C6 ≤ δ ^ (-(ε / 20)) :=
    le_rpow_neg_of_le hC6pos (by positivity) hδ (hδd0.trans (min_le_right _ _))
  set S : Fin n → Set (ℝ × ℝ) :=
    fun i => {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} with hS
  by_cases hsmall : lam ≤ δ ^ (-(ε / 4))
  · -- the set is empty: the diagonal of the close-pair count is the multiplicity
    refine le_trans (measure_mono (t := (∅ : Set (ℝ × ℝ))) ?_)
      (by rw [measure_empty]; exact zero_le)
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
    have h3 : 1 < δ ^ (ε / 4) * lam := by
      have e : δ ^ (ε / 4) * lam ^ 2 = (δ ^ (ε / 4) * lam) * lam := by ring
      rw [e] at hlt
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hlam0.le
      linarith
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
    have hbig : 1 + 8 * 801 ^ 3 * (L : ℝ) ≤ δ ^ (-(ε / 4)) := by
      have e : δ ^ (-(3 * ε / 20)) * δ ^ (-t) = δ ^ (-(ε / 4)) := by
        rw [← Real.rpow_add hδ, ht]; congr 1; ring
      calc 1 + 8 * 801 ^ 3 * (L : ℝ) ≤ 1 + 8 * 801 ^ 3 * (C3 * δ ^ (-t)) := by linarith
        _ ≤ δ ^ (-t) + 8 * 801 ^ 3 * (C3 * δ ^ (-t)) := by linarith
        _ = C4 * δ ^ (-t) := by rw [hC4]; ring
        _ ≤ δ ^ (-(3 * ε / 20)) * δ ^ (-t) :=
            mul_le_mul_of_nonneg_right hc4 (by positivity)
        _ = δ ^ (-(ε / 4)) := e
    -- the close/transverse thresholds are small
    have hsmallθ : δ ^ (ε / 4) * (8 * 801 ^ 3 * (L : ℝ)) ^ 2 ≤ 1 / 100 := by
      have e1 : δ ^ (ε / 4) * δ ^ (-(ε / 20)) * δ ^ (-t) * δ ^ (-t) = 1 := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ht]
        have : ε / 4 + -(ε / 20) + -(ε / 10) + -(ε / 10) = 0 := by ring
        rw [this, Real.rpow_zero]
      have hL2 : (8 * 801 ^ 3 * (L : ℝ)) ^ 2 ≤ 64 * 801 ^ 6 * (C3 ^ 2 * (δ ^ (-t) * δ ^ (-t))) := by
        have h0 : (0 : ℝ) ≤ L := by linarith
        have : (L : ℝ) ^ 2 ≤ (C3 * δ ^ (-t)) ^ 2 := pow_le_pow_left₀ h0 hLle 2
        nlinarith
      have hpos : 0 ≤ δ ^ (ε / 4) := by positivity
      calc δ ^ (ε / 4) * (8 * 801 ^ 3 * (L : ℝ)) ^ 2
          ≤ δ ^ (ε / 4) * (64 * 801 ^ 6 * (C3 ^ 2 * (δ ^ (-t) * δ ^ (-t)))) :=
            mul_le_mul_of_nonneg_left hL2 hpos
        _ = (C6 / 100) * (δ ^ (ε / 4) * δ ^ (-t) * δ ^ (-t)) := by rw [hC6]; ring
        _ ≤ (δ ^ (-(ε / 20)) / 100) * (δ ^ (ε / 4) * δ ^ (-t) * δ ^ (-t)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith
        _ = 1 / 100 := by
            have : δ ^ (-(ε / 20)) / 100 * (δ ^ (ε / 4) * δ ^ (-t) * δ ^ (-t)) =
                (δ ^ (ε / 4) * δ ^ (-(ε / 20)) * δ ^ (-t) * δ ^ (-t)) / 100 := by ring
            rw [this, e1]
    have hlam2 : 2 ≤ lam := by linarith
    have hlam1 : 1 < lam := by linarith
    have hlam0 : 0 < lam := by linarith
    set μ : ℝ := (lam - 1) / (4 * 801 ^ 3 * L) with hμ
    have hμ2 : 2 < μ := by
      rw [hμ, lt_div_iff₀ (by positivity)]
      linarith
    have hμ0 : 0 < μ := by linarith
    have hμlam : μ ≤ lam / 1.98 := by
      rw [hμ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : lam * 2 ≤ lam * (4 * 801 ^ 3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0.le
      linarith
    have hlamμ : lam ≤ 8 * 801 ^ 3 * (L : ℝ) * μ := by
      have e : 8 * 801 ^ 3 * (L : ℝ) * μ = 2 * (lam - 1) := by
        rw [hμ]; field_simp; ring
      rw [e]; linarith
    have hθμ : δ ^ (ε / 4) * lam ^ 2 ≤ μ ^ 2 / 100 := by
      have h1 : lam ^ 2 ≤ (8 * 801 ^ 3 * (L : ℝ)) ^ 2 * μ ^ 2 := by
        have := pow_le_pow_left₀ hlam0.le hlamμ 2
        nlinarith
      have hpos : 0 ≤ δ ^ (ε / 4) := by positivity
      calc δ ^ (ε / 4) * lam ^ 2 ≤ δ ^ (ε / 4) * ((8 * 801 ^ 3 * (L : ℝ)) ^ 2 * μ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hpos
        _ = (δ ^ (ε / 4) * (8 * 801 ^ 3 * (L : ℝ)) ^ 2) * μ ^ 2 := by ring
        _ ≤ 1 / 100 * μ ^ 2 := mul_le_mul_of_nonneg_right hsmallθ (by positivity)
        _ = μ ^ 2 / 100 := by ring
    have hθhalf : δ ^ (ε / 4) * lam ^ 2 ≤ lam ^ 2 / 2 := by
      have h1 : δ ^ (ε / 4) ≤ 1 / 100 := by
        have h2 : (1 : ℝ) ≤ (8 * 801 ^ 3 * (L : ℝ)) ^ 2 :=
          one_le_pow₀ (by linarith)
        have hpos : 0 ≤ δ ^ (ε / 4) := by positivity
        have h3 : δ ^ (ε / 4) * 1 ≤ δ ^ (ε / 4) * (8 * 801 ^ 3 * (L : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hpos
        linarith
      have hl : 0 ≤ lam ^ 2 := by positivity
      have h4 : δ ^ (ε / 4) * lam ^ 2 ≤ 1 / 100 * lam ^ 2 := mul_le_mul_of_nonneg_right h1 hl
      linarith
    set K : ℝ := 41 ^ 3 * δ ^ (-η) with hK
    have hK1 : 1 ≤ K := by
      have : 1 ≤ δ ^ (-η) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by rw [hη]; simp only [neg_nonpos]; positivity)
      rw [hK]; exact one_le_mul_of_one_le_of_one_le (by norm_num) this
    set R : ℝ := δ * lam * δ ^ (-ε) with hRdef
    have hδε : 1 ≤ δ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hR2 : 2 * δ ≤ R := by
      have h1 : δ * 2 * 1 ≤ δ * lam * δ ^ (-ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlam2 hδ.le) hδε zero_le_one (by positivity)
      rw [hRdef]; linarith
    -- index set of far scales
    set Mfar := (range L).filter (fun m => R ≤ 1.98 * whitneyScale δ m) with hMfar
    set E : ℕ → ((Fin 3 → ℤ) × (Fin 3 → ℤ)) → Set (ℝ × ℝ) := fun m kk =>
      {p : ℝ × ℝ | ENNReal.ofReal μ ≤ Finset.sum (cubeSet q (whitneyScale δ m / 200) kk.1) (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ ENNReal.ofReal μ ≤ Finset.sum (cubeSet q (whitneyScale δ m / 200) kk.2) (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum (cubeSet q (whitneyScale δ m / 200) kk.1) (fun i => Finset.sum (cubeSet q (whitneyScale δ m / 200) kk.2) (fun j => Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (4 * (ε / 8)) * μ ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (μ ^ 2 / 100)} with hE
    -- the o117 set is covered
    have hcover : {p : ℝ × ℝ | ENNReal.ofReal lam ≤ Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < δ * lam * δ ^ (-ε) then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) ∧ Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (ε / 2) * lam ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2)} ⊆
        ⋃ m ∈ Mfar, ⋃ kk ∈ whitneyPairs q (whitneyScale δ m), E m kk := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hp
      have hθ0 : 0 < δ ^ (ε / 4) * lam ^ 2 := by positivity
      have hfar := far_half (fun i => {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ})
        (fun i j => dist (q i) (q j)) (R := R) p hθhalf hθ0 hlam0.le h1 h2
      obtain ⟨m, hm, hRD, kk, hkk, hpk⟩ := rich_point_whitney_far q
        (fun i => {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ}) hδ hq hδ1 hLspec hlam1
        (by linarith) (p := p) h1 hfar
      simp only [Set.mem_iUnion]
      refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hRD⟩, kk, hkk, hpk.1, hpk.2, ?_⟩
      -- transverse transfer
      set D := whitneyScale δ m with hD
      have hDpos : 0 < D := whitneyScale_pos hδ m
      have hAB : ∀ i ∈ cubeSet q (D / 200) kk.1, ∀ j ∈ cubeSet q (D / 200) kk.2, i ≠ j := by
        intro i hi j hj hij
        subst hij
        have := (cross_dist_of_mem_whitneyPairs hkk hi hj).1
        rw [dist_self] at this
        linarith
      have hκ : δ ^ (ε / 2) * lam ^ (-(1/2 : ℝ)) ≤ δ ^ (4 * (ε / 8)) * μ ^ (-(1/2 : ℝ)) := by
        have e : (4 * (ε / 8)) = ε / 2 := by ring
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hμle : μ ≤ lam := hμlam.trans (div_le_self hlam0.le (by norm_num))
        exact Real.rpow_le_rpow_of_nonpos hμ0 hμle (by norm_num)
      have htr := transverseAB_le (fun i => {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ})
        (fun i j => dist (q i) (q j)) (fun i j => dist_nonneg)
        (fun i j p => |deriv (g i) p.2 - deriv (g j) p.2|) hκ
        (cubeSet q (D / 200) kk.1) (cubeSet q (D / 200) kk.2) hAB p
      calc _ ≤ _ := htr
        _ < ENNReal.ofReal (δ ^ (ε / 4) * lam ^ 2) := h3
        _ ≤ ENNReal.ofReal (μ ^ 2 / 100) := ENNReal.ofReal_le_ofReal hθμ
    -- bound every piece
    set Y0 : ℝ := C * δ ^ (-(ε / 8)) * K ^ a * δ * μ ^ (-(3 / 2 : ℝ)) with hY0
    have hY0nn : 0 ≤ Y0 := by rw [hY0]; positivity
    have hterm : ∀ m ∈ Mfar, ∀ kk ∈ whitneyPairs q (whitneyScale δ m),
        volume (E m kk) ≤
          ENNReal.ofReal (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card)) := by
      intro m hm kk hkk
      have hRD := (Finset.mem_filter.mp hm).2
      set D := whitneyScale δ m with hD
      have hDpos : 0 < D := whitneyScale_pos hδ m
      have hδD : δ ≤ D := by
        have h198 : (1.98 : ℝ) = 99 / 50 := by norm_num
        rw [h198] at hRD
        linarith
      have hfarD : δ * μ * δ ^ (-8 * (ε / 8)) ≤ D := by
        have e : (-8 * (ε / 8)) = -ε := by ring
        rw [e]
        have h1 : δ * μ * δ ^ (-ε) ≤ δ * (lam / 1.98) * δ ^ (-ε) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hμlam hδ.le
        have h2 : δ * (lam / 1.98) * δ ^ (-ε) = R / 1.98 := by rw [hRdef]; ring
        have h3 : R / 1.98 ≤ D := by
          rw [div_le_iff₀ (by norm_num)]
          have h198 : (1.98 : ℝ) = 99 / 50 := by norm_num
          rw [h198] at hRD ⊢
          linarith
        linarith
      have hb := hbd δ hδ hδ100 n q g hq hg hjet hsep (cubeSet q (D / 200) kk.1)
        (cubeSet q (D / 200) kk.2) D K μ hδD (whitneyScale_le_twenty hq hkk) hK1
        (fun i hi j hj => (dist_lt_of_mem_cubeSet hDpos hi hj).le)
        (fun i hi j hj => (dist_lt_of_mem_cubeSet hDpos hi hj).le)
        (fun i hi j hj => cross_dist_of_mem_whitneyPairs hkk hi hj)
        (fun q0 r hr _ => ncard_ball_le_of_katzTao q hq hδ hδ1 hKT
          (fun i => i ∈ cubeSet q (D / 200) kk.1 ∪ cubeSet q (D / 200) kk.2) q0 hr)
        (by linarith) hfarD
      refine le_trans (le_of_eq ?_) (hb.trans (le_of_eq ?_))
      · rfl
      · congr 1
        rw [hY0]
        ring
    calc volume _ ≤ volume (⋃ m ∈ Mfar, ⋃ kk ∈ whitneyPairs q (whitneyScale δ m), E m kk) :=
          measure_mono hcover
      _ ≤ ∑ m ∈ Mfar, volume (⋃ kk ∈ whitneyPairs q (whitneyScale δ m), E m kk) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Mfar, ∑ kk ∈ whitneyPairs q (whitneyScale δ m), volume (E m kk) := by
          apply Finset.sum_le_sum
          intro m _
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Mfar, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
          ENNReal.ofReal (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card)) := by
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro kk hkk
          exact hterm m hm kk hkk
      _ = ENNReal.ofReal (∑ m ∈ Mfar, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
          (Y0 * (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
            (cubeSet q (whitneyScale δ m / 200) kk.2).card))) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => Finset.sum_nonneg
            (fun kk _ => mul_nonneg hY0nn (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))]
          apply Finset.sum_congr rfl
          intro m _
          rw [ENNReal.ofReal_sum_of_nonneg (fun kk _ => mul_nonneg hY0nn
            (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))]
      _ ≤ ENNReal.ofReal (Y0 * ((L : ℝ) * (2 * 801 ^ 3 * (n : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          simp_rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ hY0nn
          refine le_trans ?_ (sum_sum_whitney_card_le q hδ L)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m _ _
          apply Finset.sum_nonneg
          intro kk _
          exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hn := card_le_of_katzTao q hq hδ hδ1 hKT
          have hn' : (n : ℝ) ≤ 41 ^ 3 * δ ^ (-(ε / (8 * (a + 1)))) / δ := by
            rw [hη] at hn; exact hn
          have hLle' : (L : ℝ) ≤ (3 * 20 ^ (ε / 10) / (ε / 10) + 3) * δ ^ (-(ε / 10)) := by
            rw [hC3, ht] at hLle; exact hLle
          have hc5' : C * (41 ^ 3) ^ a * 41 ^ 3 * 2 * 801 ^ 3 * (8 * 801 ^ 3) ^ (3 / 2 : ℝ) *
              (3 * 20 ^ (ε / 10) / (ε / 10) + 3) ^ (5 / 2 : ℝ) ≤ δ ^ (-(ε / 2)) := by
            rw [hC5, hC3, ht] at hc5; exact hc5
          have := reduction_arith hC ha hε hδ hδ1 hlam2 hL1 hLle' (Nat.cast_nonneg _) hn' hc5'
          rw [hY0, hK, hμ]
          exact this

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction

