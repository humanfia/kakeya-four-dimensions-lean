-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_separated_cover_refinement

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

set_option maxHeartbeats 1000000

/-- Simultaneously refine finitely many covers while retaining the prescribed density. -/
theorem finite_refinement {n L : ℕ} {η ε δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hD : Dense η δ n x v Y)
    (ρ : Fin L → ℝ) (k : Fin L → ℕ)
    (z w : (l : Fin L) → Fin (k l) → Space)
    (hρ : ∀ l, 0 < ρ l ∧ ρ l ≤ 1)
    (hcov : ∀ l, CoverAt δ (δ ^ (-η)) (ρ l) x v (z l) (w l))
    (hcoefficient : δ ^ (-η) ≤ δ ^ (-ε) * δ ^ (2 * η))
    (hbudget : δ ^ ε * (n : ℝ) * δ ^ 2 ≤
      (δ ^ η * (n : ℝ) * δ ^ 2) / ((conflictBound + 1 : ℕ) : ℝ) ^ L -
        (384 * δ ^ 2) * δ ^ (2 * η) * ((L : ℝ) * n)) :
    ∃ Q : Finset (Fin n), Q.Nonempty ∧
      Dense ε δ Q.card (fun i => x (enumerate Q i))
        (fun i => v (enumerate Q i)) (fun i => Y (enumerate Q i)) ∧
      ∀ l, ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
        CoverAt δ (δ ^ (-ε)) (ρ l) (fun i => x (enumerate Q i))
          (fun i => v (enumerate Q i)) z' w' ∧
        SeparatedAt δ (ρ l) (fun i => x (enumerate Q i)) (fun i => v (enumerate Q i)) z' w' := by
  classical
  obtain ⟨hn, hv, hball, hsep, hmeas, hY, hmass⟩ := hD
  have hassign : ∀ l, ∃ f : Fin n → Fin (k l), ∀ i j,
      Tube δ (x i) (v i) ⊆ Tube (ρ l) (z l j) (w l j) ↔ f i = j := by
    intro l
    have huniq := (hcov l).2.2.1
    choose f hf using (fun i => (huniq i).exists)
    refine ⟨f, ?_⟩
    intro i j
    constructor
    · intro hij
      exact (huniq i).unique (hf i) hij
    · intro hij
      rw [← hij]
      exact hf i
  choose f hf using hassign
  have hcolors : ∀ l, ∃ c : Fin (k l) → Fin (conflictBound + 1),
      ∀ j j', j ≠ j' → Conflict δ (ρ l) x v (z l) (w l) j j' → c j ≠ c j' := by
    intro l
    apply color_relation (Nat.succ_pos _) (Conflict δ (ρ l) x v (z l) (w l))
    · rintro j j' ⟨i, hi, hi'⟩
      exact ⟨i, hi', hi⟩
    · intro j
      exact Nat.lt_succ_of_le (conflict_card_le hδ (hρ l).1 (hρ l).2 x v (z l) (w l) hv
        (hcov l).1 (hcov l).2.1 j)
  choose c hc using hcolors
  have hvol : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
    intro i
    exact (measure_mono (hY i)).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 (x i) (v i) (hv i))
  have hfin : ∀ i, volume (Y i) ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvol i)
  have hreal : δ ^ η * (n : ℝ) * δ ^ 2 ≤ ∑ i, (volume (Y i)).toReal := by
    have h := ENNReal.toReal_mono (by simp [hfin]) hmass
    rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_sum (fun i _ => hfin i)] at h
  obtain ⟨Q, hQfib, hQcolor, hQmass⟩ := select_regular (fun l => Fin (k l)) f
    (Nat.succ_pos conflictBound) c (fun i => (volume (Y i)).toReal)
    (show 0 < 384 * δ ^ 2 by positivity) (Real.rpow_pos_of_pos hδ (2 * η))
    (fun i => ENNReal.toReal_le_of_le_ofReal (by positivity) (hvol i))
  simp only [Fintype.card_fin] at hQmass
  have htotal : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ ∑ i ∈ Q, (volume (Y i)).toReal := by
    refine hbudget.trans ((sub_le_sub_right ?_ _).trans hQmass)
    exact div_le_div_of_nonneg_right hreal (by positivity)
  have hQ : Q.Nonempty := by
    by_contra hnot
    have hQE : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hQE, Finset.sum_empty] at htotal
    have hpos : 0 < δ ^ ε * (n : ℝ) * δ ^ 2 := by positivity
    linarith
  have hcard : (Q.card : ℝ) ≤ n := by
    exact_mod_cast (show Q.card ≤ n from (Finset.card_le_card (Finset.subset_univ Q)).trans_eq (by simp))
  have hout : ENNReal.ofReal (δ ^ ε * (Q.card : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y (enumerate Q i)) := by
    rw [enumerate_sum Q (fun i => volume (Y i))]
    have he : ENNReal.ofReal (∑ i ∈ Q, (volume (Y i)).toReal) = ∑ i ∈ Q, volume (Y i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_toReal (hfin i))
    rw [← he]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard
      (Real.rpow_nonneg hδ.le _)) (sq_nonneg _)).trans htotal
  refine ⟨Q, hQ, ?_, ?_⟩
  · exact ⟨Finset.card_pos.mpr hQ, (fun i => hv _), (fun i => hball _),
      (fun i j hij => hsep _ _ ((enumerate_injective Q).ne hij)),
      (fun i => hmeas _), (fun i => hY _), hout⟩
  · intro l
    exact restrict_cover x v (z l) (w l) (hcov l) (f l) (hf l) Q hQ (hQfib l)
      (Real.rpow_nonneg hδ.le _) hcoefficient (c l) (hc l) (hQcolor l)

/-- Finite selection, pruning, and interpolation produce separated all-scale covers. -/
theorem refinement : ∀ ε : ℝ, 0 < ε → ∃ η d1 : ℝ, 0 < η ∧ 0 < d1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y → Weak η δ n x v →
      ∃ (m : ℕ) (a : Fin m → Fin n), Function.Injective a ∧
        Dense ε δ m (fun i => x (a i)) (fun i => v (a i)) (fun i => Y (a i)) ∧
        Strong ε δ m (fun i => x (a i)) (fun i => v (a i)) := by
  intro ε hε
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN, hgap⟩ := exists_net_size hη
  let C : ℝ := ((conflictBound + 1 : ℕ) : ℝ) ^ (N + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ N + 1)
  obtain ⟨d1, hd1, hcut⟩ := exists_rpow_cutoff hη
    (show 0 < 1 / (1000 * C * (N + 1 : ℕ)) by positivity)
  refine ⟨η, d1, hη, hd1, ?_⟩
  intro δ hδ hδd hδmax n x v Y hD hA
  have hδ1 : δ ≤ 1 := by linarith
  have hsmall := hcut δ hδ hδd
  have hbud := weight_budget (Real.rpow_pos_of_pos hδ η)
    (Real.rpow_le_one hδ.le hδ1 hη.le) hC hL hsmall
  have heps : δ ^ ε = (δ ^ η) ^ (4 : ℕ) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    dsimp [η]
    ring
  have htwice : δ ^ (2 * η) = (δ ^ η) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  have hbudget : δ ^ ε * (n : ℝ) * δ ^ 2 ≤
      (δ ^ η * (n : ℝ) * δ ^ 2) / ((conflictBound + 1 : ℕ) : ℝ) ^ (N + 1) -
        (384 * δ ^ 2) * δ ^ (2 * η) * (((N + 1 : ℕ) : ℝ) * n) := by
    rw [heps, htwice]
    have h := mul_le_mul_of_nonneg_right hbud (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)
    dsimp [C] at h
    convert h using 1 <;> ring
  have hcoefficient : δ ^ (-η) ≤ δ ^ (-ε) * δ ^ (2 * η) := by
    rw [← Real.rpow_add hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    dsimp [η]
    linarith
  obtain ⟨s, hs, hnet⟩ := power_net hδ hδ1 hN hgap
  have hscales : ∀ l, ∃ ρ : ℝ, s l ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * s l ∧
      ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space, CoverAt δ (δ ^ (-η)) ρ x v z w :=
    fun l => hA (s l) (hs l).1 (hs l).2
  choose ρ hsr hρ1 hρs k hk z w hcov using hscales
  have hρ : ∀ l, 0 < ρ l ∧ ρ l ≤ 1 := fun l =>
    ⟨hδ.trans_le ((hs l).1.trans (hsr l)), hρ1 l⟩
  obtain ⟨Q, hQ, hDQ, hSQ⟩ := finite_refinement hδ hδ1 x v Y hD ρ k z w hρ hcov
    hcoefficient hbudget
  refine ⟨Q.card, enumerate Q, enumerate_injective Q, hDQ, ?_⟩
  intro r hr hr1
  obtain ⟨l, hrl, hlr⟩ := hnet r hr hr1
  refine ⟨ρ l, hrl.trans (hsr l), hρ1 l, ?_, hSQ l⟩
  calc ρ l ≤ δ ^ (-η) * s l := hρs l
    _ ≤ δ ^ (-η) * (δ ^ (-η) * r) :=
      mul_le_mul_of_nonneg_left hlr (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-(2 * η)) * r := by rw [← mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
    _ ≤ δ ^ (-ε) * r := by
      apply mul_le_mul_of_nonneg_right _ (hδ.le.trans hr)
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      dsimp [η]
      linarith

end WangZahlLot.Obl.wz_separated_cover_refinement
