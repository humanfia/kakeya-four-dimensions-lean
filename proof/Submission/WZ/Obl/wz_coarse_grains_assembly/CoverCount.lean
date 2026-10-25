-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.CoverCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.BroadCount
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- A balanced retained cover has a nonempty fibre with average shading
at least `δ^(3η)`. The loss includes original density, cover retention and
comparison with the average fibre size. -/
theorem exists_dense_cover_fibre {δ η ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hn : 0 < n)
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ η n x v Y S Z ρ N y w f b) :
    ∃ k : Fin N, (S.filter (fun i => f i = k)).Nonempty ∧
      (N : ℝ) * (S.filter (fun i => f i = k)).card ≤ δ ^ (-η) * n ∧
      O (δ ^ (3 * η) * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
        ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
  classical
  have hN : 0 < N := Nat.zero_lt_of_lt (f ⟨0, hn⟩).isLt
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmass : O (δ ^ (2 * η) * n * δ ^ 2) ≤ ∑ i ∈ S, μ (Z i) := by
    calc
      O (δ ^ (2 * η) * n * δ ^ 2) = O (δ ^ η) * O (δ ^ η * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        rw [show 2 * η = η + η by ring, Real.rpow_add hδ]
        ring
      _ ≤ O (δ ^ η) * ∑ i, μ (Y i) := by
        gcongr
      _ ≤ _ := hC.2.1
  obtain ⟨k, hk⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color hN S f
    (fun i => μ (Z i))
  have hq (k : Fin N) : q n {i | i ∈ S ∧ f i = k} =
      ((S.filter (fun i => f i = k)).card : ℝ) := by
    have he : {i | i ∈ S ∧ f i = k} = (↑(S.filter (fun i => f i = k)) : Set (Fin n)) := by
      ext i
      simp
    change (({i | i ∈ S ∧ f i = k} : Set (Fin n)).ncard : ℝ) = _
    rw [he, Set.ncard_coe_finset]
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-η) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    simpa only [hq] using hC.2.2.2.2.2.2.1 k k'
  have hsum : ∑ k : Fin N, ((S.filter (fun i => f i = k)).card : ℝ) = S.card := by
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (f i))).symm
  have hsize : (N : ℝ) * (S.filter (fun i => f i = k)).card ≤ δ ^ (-η) * n := by
    calc
      (N : ℝ) * (S.filter (fun i => f i = k)).card =
          ∑ _k' : Fin N, ((S.filter (fun i => f i = k)).card : ℝ) := by simp
      _ ≤ ∑ k' : Fin N, δ ^ (-η) * (S.filter (fun i => f i = k')).card :=
        Finset.sum_le_sum fun k' _ => hbal k k'
      _ = δ ^ (-η) * S.card := by rw [← Finset.mul_sum, hsum]
      _ ≤ δ ^ (-η) * n := by
        gcongr
        exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
  have hne : (S.filter (fun i => f i = k)).Nonempty := by
    by_contra he
    have he' := Finset.not_nonempty_iff_eq_empty.mp he
    rw [he', Finset.sum_empty, mul_zero] at hk
    have hz := hmass.trans hk
    have hp : 0 < O (δ ^ (2 * η) * n * δ ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
    exact (not_le_of_gt hp) hz
  refine ⟨k, hne, hsize, ?_⟩
  have hscalar : (N : ℝ) * (δ ^ (3 * η) * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
      δ ^ (2 * η) * n * δ ^ 2 := by
    have he : δ ^ (3 * η) * δ ^ (-η) = δ ^ (2 * η) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      (N : ℝ) * (δ ^ (3 * η) * (S.filter (fun i => f i = k)).card * δ ^ 2) =
          (δ ^ (3 * η) * δ ^ 2) * (N * (S.filter (fun i => f i = k)).card) := by ring
      _ ≤ (δ ^ (3 * η) * δ ^ 2) * (δ ^ (-η) * n) := by gcongr
      _ = δ ^ (2 * η) * n * δ ^ 2 := by rw [mul_mul_mul_comm, he]; ring
  have ht : (N : ENNReal) * O (δ ^ (3 * η) * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
      (N : ENNReal) * ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
    calc
      _ = O ((N : ℝ) * (δ ^ (3 * η) * (S.filter (fun i => f i = k)).card * δ ^ 2)) := by
        simp only [O, ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      _ ≤ O (δ ^ (2 * η) * n * δ ^ 2) := ENNReal.ofReal_le_ofReal hscalar
      _ ≤ _ := hmass.trans hk
  exact (ENNReal.mul_le_mul_iff_right (a := (N : ENNReal))
    (by exact_mod_cast hN.ne') (by simp)).mp ht

/-- Broadness prevents a balanced retained cover from having too many coarse
tubes compared with the original family. -/
theorem broad_cover_count {δ η ρ β : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη : 0 < η) (hβ : 0 < β) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ η n x v Y S Z ρ N y w f b)
    (hbr : ∀ k p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) :
    δ ^ (4 * η + 6 * η / β) * ρ * N ≤ 4096 * n * δ := by
  classical
  obtain ⟨k, hk, hsize, hmass⟩ := exists_dense_cover_fibre hδ hn hmassY hC
  have hvF : ∀ i ∈ S.filter (fun i => f i = k), ‖v i‖ = 1 := fun i _ => hv i
  have hZ : ∀ i ∈ S.filter (fun i => f i = k), Z i ⊆ T δ (x i) (v i) :=
    fun i _ => (hC.1 i).2.1.trans (hY i)
  have hbr' : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S.filter (fun i => f i = k) ∧ p ∈ Z i ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-(3 * η)) * (r / ρ) ^ β *
          q n {i | i ∈ S.filter (fun i => f i = k) ∧ p ∈ Z i} := by
    intro p u r hu hdr hrρ
    simp only [Finset.mem_filter, and_assoc]
    calc
      _ ≤ δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} :=
        hbr k p u r hu hdr hrρ
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _)
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
  have hc := card_lower_power_broad hδ hδ1 hρ hρ1 hβ (by positivity : 0 < 3 * η)
    hk hvF hZ hmass hbr'
  have he : δ ^ (4 * η + 6 * η / β) = δ ^ η * δ ^ (3 * η + 2 * (3 * η) / β) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have he' : δ ^ η * δ ^ (-η) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  calc
    δ ^ (4 * η + 6 * η / β) * ρ * N =
        δ ^ η * (δ ^ (3 * η + 2 * (3 * η) / β) * ρ) * N := by rw [he]; ring
    _ ≤ δ ^ η * (4096 * (S.filter (fun i => f i = k)).card * δ) * N := by gcongr
    _ = (4096 * δ) * (δ ^ η * (N * (S.filter (fun i => f i = k)).card)) := by ring
    _ ≤ (4096 * δ) * (δ ^ η * (δ ^ (-η) * n)) := by gcongr
    _ = 4096 * n * δ := by rw [← mul_assoc (δ ^ η), he']; ring

/-- The length requested by the grains assembly is at most one quarter.
This conclusion uses the original cover and does not presuppose a new grain
decomposition. -/
theorem broad_cover_length_le_quarter {δ η ρ β ε : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη : 0 < η) (hβ : 0 < β)
    (hbudget : 4 * η + 6 * η / β ≤ ε / 2) (hsmall : 16384 * δ ^ (ε / 2) ≤ 1)
    (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ η n x v Y S Z ρ N y w f b)
    (hbr : ∀ k p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) :
    δ ^ ε * (ρ / δ) * N / n ≤ 1 / 4 := by
  have hc := broad_cover_count hδ hδ1 hρ hρ1 hη hβ hn hv hY hmassY hC hbr
  have he : δ ^ ε = δ ^ (4 * η + 6 * η / β) * δ ^ (ε - (4 * η + 6 * η / β)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hr : δ ^ (ε - (4 * η + 6 * η / β)) ≤ δ ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
  have hd : 16384 * δ ^ ε ≤ δ ^ (4 * η + 6 * η / β) := by
    rw [he]
    nlinarith [Real.rpow_pos_of_pos hδ (4 * η + 6 * η / β)]
  have hg : 16384 * δ ^ ε * ρ * N ≤ 4096 * n * δ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hρ.le) (Nat.cast_nonneg N)).trans hc
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn']
  have h' : δ ^ ε * ρ * N / δ ≤ (1 / 4 : ℝ) * n := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  convert h' using 1
  ring

end WangZahlLot.Obl.wz_coarse_grains_assembly
