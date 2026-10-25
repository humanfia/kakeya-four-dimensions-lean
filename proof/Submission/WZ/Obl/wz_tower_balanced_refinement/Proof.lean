-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Proof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Arithmetic
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex
import Submission.WZ.Obl.wz_tower_balanced_refinement.Tower

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- A sufficiently massive subfamily remains admissible with the relaxed density exponent. -/
theorem admissible_selection {d θ ε M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθε : θ ≤ ε / 2)
    (hA : Admissible d θ M L n x v Y) (S : Finset (Fin n))
    (hmass : ENNReal.ofReal (d ^ (ε / 2)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i)) :
    ∃ M' L' : ℝ,
      Admissible d ε M' L' S.card (x ∘ enumerate S) (v ∘ enumerate S) (Y ∘ enumerate S) := by
  classical
  obtain ⟨hn, hfamily, hdist, hden, hK, hF⟩ := hA
  have hmasspos : 0 < ∑ i ∈ S, volume (Y i) := by
    apply lt_of_lt_of_le _ hmass
    apply pos_iff_ne_zero.mpr
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)).ne'
    · apply ne_of_gt
      apply lt_of_lt_of_le _ hden
      apply ENNReal.ofReal_pos.mpr
      exact mul_pos (mul_pos (Real.rpow_pos_of_pos hd _) (by exact_mod_cast hn)) (sq_pos_of_pos hd)
  have hm : 0 < S.card := by
    by_contra h
    have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
    simpa [he] using hmasspos
  have hmn : (S.card : ℝ) ≤ n := by
    exact_mod_cast (show S.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ S)
  have hdenreal : d ^ ε * S.card * d ^ 2 ≤ d ^ (ε / 2) * (d ^ θ * n * d ^ 2) := by
    calc
      d ^ ε * S.card * d ^ 2 ≤ d ^ ε * n * d ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmn (Real.rpow_nonneg hd.le _)) (sq_nonneg d)
      _ ≤ d ^ (ε / 2 + θ) * n * d ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg d)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
        exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      _ = d ^ (ε / 2) * (d ^ θ * n * d ^ 2) := by rw [Real.rpow_add hd]; ring
  obtain ⟨M', L', hK', hF'⟩ := finite_constants hd (x ∘ enumerate S) (v ∘ enumerate S)
  refine ⟨M', L', hm, (fun i => hfamily (enumerate S i)), ?_, ?_, hK', hF'⟩
  · intro i j hij
    exact hdist _ _ ((enumerate_injective S).ne hij)
  · rw [show (∑ i, volume ((Y ∘ enumerate S) i)) = ∑ i ∈ S, volume (Y i) from
      sum_enumerate S (fun i => volume (Y i))]
    calc
      ENNReal.ofReal (d ^ ε * S.card * d ^ 2) ≤
          ENNReal.ofReal (d ^ (ε / 2) * (d ^ θ * n * d ^ 2)) := ENNReal.ofReal_le_ofReal hdenreal
      _ = ENNReal.ofReal (d ^ (ε / 2)) * ENNReal.ofReal (d ^ θ * n * d ^ 2) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)
      _ ≤ ENNReal.ofReal (d ^ (ε / 2)) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hden
      _ ≤ ∑ i ∈ S, volume (Y i) := hmass

/-- The balanced refinement theorem in concrete notation. -/
theorem balanced_refinement (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ ε / 2 ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → d ≤ d₀ →
    ∀ g : ℝ, 0 < g → g ≤ ε / 2 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (M L : ℝ),
    Admissible d θ M L n x v Y → GlobalTower d (d ^ (-θ)) g B n x v →
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M' L' : ℝ),
      Admissible d ε M' L' m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (d ^ (ε / 2)) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      ∀ ρ₀ : ℝ, d ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < d ^ (-ε) * ρ₀ ∧
      ∃ (N : ℕ) (y w : Fin N → Space) (f : Fin m → Fin N),
        (∀ k, ‖w k‖ = 1) ∧ (∀ j, Tube d (x' j) (v' j) ⊆ Tube ρ (y (f j)) (w (f j))) ∧
        (∀ k k', (Set.ncard {j | f j = k} : ℝ) ≤ d ^ (-ε) * Set.ncard {j | f j = k'}) ∧
        ConvexCount ρ (d ^ (-ε)) N y w := by
  classical
  let C : ℝ := (volume (ball (0 : Space) 1)).toReal
  obtain ⟨θ, q, d₀, hθ, hθε, hθ1, hq, hqε, hd₀, hsmall⟩ :=
    choose_parameters B ε C hε ENNReal.toReal_nonneg
  refine ⟨θ, hθ, hθε, d₀, hd₀, ?_⟩
  intro d hd hd100 hdd g hg hgε n x v Y M L hA hH
  have hd1 : d < 1 := by linarith
  obtain ⟨hCd, hloss⟩ := hsmall d hd hdd
  obtain ⟨J, hJ1, hJB, r, N, y, w, f, hr0, hrJ, hN0, ⟨u, hu⟩, hunit, hedge, hglobal⟩ := hH
  have hx : y J ∘ u = x := funext fun i => (hu i).1
  have hv : w J ∘ u = v := funext fun i => (hu i).2
  have hbottom : ConvexCount d (d ^ (-θ)) n x v := by
    simpa only [hrJ, hx, hv] using convexCount_restrict u u.injective (hglobal J le_rfl)
  have hncount : (n : ℝ) * d ^ 2 ≤ d ^ (-θ) * C :=
    WangZahlLot.Obl.wz_direction_density_transfer.global_count (Real.rpow_nonneg hd.le _)
      hbottom (fun i => (hA.2.1 i).2.1)
  have hnq : (n : ℝ) < (d ^ (-ε)) ^ q :=
    cardinal_lt_power hd hd1.le hθ1 ENNReal.toReal_nonneg hCd hqε hncount
  have hR : 1 < d ^ (-ε) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_gt hd hd1 (show -ε < (0 : ℝ) by linarith)
  obtain ⟨color, hcolor⟩ := exists_size_color n q (d ^ (-ε)) hq hR hnq
  let p : ∀ j, Fin n → Fin (N (min j J)) := fun j i =>
    ancestor f (Nat.min_le_right j J) (u i)
  have hnest : ∀ j k, j ≤ k → k < J + 1 → ∀ i i', p k i = p k i' → p j i = p j i' := by
    intro j k hjk hk i i' hii'
    have hjk' : min j J ≤ min k J := min_le_min_right J hjk
    exact (ancestor_comp f hjk' (Nat.min_le_right k J) (u i)).symm.trans
      ((congrArg (ancestor f hjk') hii').trans
        (ancestor_comp f hjk' (Nat.min_le_right k J) (u i')))
  obtain ⟨S, hS, hSmass, hSbal⟩ := regularize_nested p (J + 1) q n hq (d ^ (-ε))
    color hcolor hnest Finset.univ (by simp) (fun i => volume (Y i))
  have hretain : ENNReal.ofReal (d ^ (ε / 2)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i) :=
    retained_mass hd hq hJB hloss hSmass
  obtain ⟨M', L', hA'⟩ := admissible_selection hd hd1.le hθε hA S hretain
  refine ⟨S.card, x ∘ enumerate S, v ∘ enumerate S, Y ∘ enumerate S, M', L', hA', ?_, ?_, ?_⟩
  · exact iUnion_subset fun i => subset_iUnion Y (enumerate S i)
  · change ENNReal.ofReal (d ^ (ε / 2)) * (∑ i, volume (Y i)) ≤
      ∑ i : Fin S.card, volume (Y (enumerate S i))
    rw [sum_enumerate S (fun i => volume (Y i))]
    exact hretain
  · intro ρ₀ hρd hρ1
    obtain ⟨j, hjJ, hρj, hjρ⟩ := select_radius r J d g ε ρ₀ hd hd1 hg.le (by linarith)
      hr0 hrJ (fun j hj => (hedge j hj).2.2.1) hρd hρ1
    obtain ⟨K, e, a, heinj, hea, hbalance⟩ :=
      reindex_balanced S (p j) (d ^ (-ε)) (hSbal j (by omega))
    refine ⟨r (min j J), ?_, ?_, K, y (min j J) ∘ e, w (min j J) ∘ e, a,
      ?_, ?_, hbalance, ?_⟩
    · simpa only [Nat.min_eq_left hjJ] using hρj
    · simpa only [Nat.min_eq_left hjJ] using hjρ
    · intro k
      exact hunit (min j J) (Nat.min_le_right j J) (e k)
    · intro i
      simp only [Function.comp_apply, hea]
      have h := ancestor_containment f (fun j k => Tube (r j) (y j k) (w j k)) J
        (fun j hj => (hedge j hj).2.2.2) (Nat.min_le_right j J) le_rfl (u (enumerate S i))
      simpa only [hrJ, (hu (enumerate S i)).1, (hu (enumerate S i)).2, p] using h
    · apply convexCount_mono (convexCount_restrict e heinj (hglobal (min j J) (Nat.min_le_right j J)))
      exact Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith)

end WangZahlLot.Obl.wz_tower_balanced_refinement
