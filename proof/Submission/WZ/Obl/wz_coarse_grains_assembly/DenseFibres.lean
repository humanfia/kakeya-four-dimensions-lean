-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.DenseFibres.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.DenseWeights

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- A cover with positive total density has a family of dense nonempty
fibres retaining half its shading mass. -/
theorem dense_cover_fibres {δ θ ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hn : 0 < n)
    (hsmall : 2 * δ ^ (4 * θ) ≤ δ ^ (2 * θ))
    (hfinite : ∀ i, μ (Z i) ≠ ⊤)
    (hmassY : O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ θ n x v Y S Z ρ N y w f b) :
    ∃ B : Finset (Fin N), B.Nonempty ∧
      (∑ i ∈ S, μ (Z i)) ≤ 2 * ∑ k ∈ B, ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) ∧
      ∀ k ∈ B, (S.filter (fun i => f i = k)).Nonempty ∧
        O (δ ^ (4 * θ) * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
          ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
  classical
  let weight (k : Fin N) := ∑ i ∈ S.filter (fun i => f i = k), μ (Z i)
  let size (k : Fin N) : ℝ := (S.filter (fun i => f i = k)).card
  have hsum : (∑ k, weight k) = ∑ i ∈ S, μ (Z i) :=
    Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (f i)) _
  have hcards : (∑ k, size k) = (S.card : ℝ) := by
    dsimp only [size]
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (f i))).symm
  have hmass : O (δ ^ (2 * θ) * n * δ ^ 2) ≤ ∑ i ∈ S, μ (Z i) := by
    calc
      _ = O (δ ^ θ) * O (δ ^ θ * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le θ)]
        congr 1
        rw [show 2 * θ = θ + θ by ring, Real.rpow_add hδ]
        ring
      _ ≤ O (δ ^ θ) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hmassY
      _ ≤ _ := hC.2.1
  have hpos : 0 < ∑ k, weight k := by
    rw [hsum]
    refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ?_) hmass
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  have hbudget : O (2 * (δ ^ (4 * θ) * δ ^ 2) * ∑ k, size k) ≤ ∑ k, weight k := by
    rw [hsum]
    apply le_trans (ENNReal.ofReal_le_ofReal _) hmass
    rw [hcards]
    calc
      _ = (2 * δ ^ (4 * θ)) * S.card * δ ^ 2 := by ring
      _ ≤ δ ^ (2 * θ) * S.card * δ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)) (sq_nonneg δ)
      _ ≤ δ ^ (2 * θ) * n * δ ^ 2 := by
        gcongr
        exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
  obtain ⟨B, _, hret, hdense⟩ := select_dense_weights Finset.univ weight size
    (by positivity : 0 ≤ δ ^ (4 * θ) * δ ^ 2) (fun k _ => Nat.cast_nonneg _)
    (fun k _ => ENNReal.sum_ne_top.mpr (fun i _ => hfinite i)) hbudget
  have hB : B.Nonempty := by
    by_contra hh
    have he := Finset.not_nonempty_iff_eq_empty.mp hh
    rw [he, Finset.sum_empty, mul_zero] at hret
    exact (not_le_of_gt hpos) hret
  refine ⟨B, hB, by simpa only [hsum] using hret, ?_⟩
  intro k hk
  have hne : (S.filter (fun i => f i = k)).Nonempty := by
    by_contra hh
    have he := Finset.not_nonempty_iff_eq_empty.mp hh
    have hp := (hdense k hk).1
    dsimp only [weight] at hp
    rw [he, Finset.sum_empty] at hp
    exact (lt_irrefl _) hp
  refine ⟨hne, ?_⟩
  calc
    _ = O ((δ ^ (4 * θ) * δ ^ 2) * size k) := by congr 1; dsimp [size]; ring
    _ ≤ weight k := (hdense k hk).2

end WangZahlLot.Obl.wz_coarse_grains_assembly
