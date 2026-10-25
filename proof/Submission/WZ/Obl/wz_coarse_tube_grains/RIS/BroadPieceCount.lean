-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BroadPieceCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BroadPieceEnergy

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

private theorem ncard_fin_eq_sum {n : ℕ} (P : Fin n → Prop) :
    ({i | P i}.ncard : ℝ) = ∑ i : Fin n, if P i then (1 : ℝ) else 0 := by
  have he : {i | P i} = (Finset.univ.filter P : Set (Fin n)) := by ext i; simp
  rw [he, ncard_coe_finset, ← Finset.sum_filter]
  simp

/-- The two orders of counting a finite tube-piece incidence relation agree. -/
theorem piece_incidence_sum {n N : ℕ} (R : Fin N → Fin n → Prop) :
    (∑ j : Fin N, ({i | R j i}.ncard : ℝ)) =
      ∑ i : Fin n, ({j | R j i}.ncard : ℝ) := by
  simp_rw [ncard_fin_eq_sum]
  rw [Finset.sum_comm]

/-- Double-counting a finite incidence relation selects a piece with few tubes. -/
theorem exists_piece_small_degree {n N : ℕ} (hN : 0 < N)
    (R : Fin N → Fin n → Prop) {L : ℝ}
    (hcross : ∀ i, ({j | R j i}.ncard : ℝ) ≤ L) :
    ∃ j, ({i | R j i}.ncard : ℝ) ≤ (n : ℝ) * L / N := by
  let degree := fun j => ({i | R j i}.ncard : ℝ)
  have hsum : (∑ j, degree j) = ∑ i : Fin n, ({j | R j i}.ncard : ℝ) := by
    dsimp [degree]
    simp_rw [ncard_fin_eq_sum]
    rw [Finset.sum_comm]
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ degree
    (show (Finset.univ : Finset (Fin N)).Nonempty from ⟨⟨0, hN⟩, Finset.mem_univ _⟩)
  have hsmall : (N : ℝ) * degree j ≤ (n : ℝ) * L := by
    calc
      _ = ∑ _k : Fin N, degree j := by simp
      _ ≤ ∑ k, degree k := Finset.sum_le_sum fun k _ => hj k (Finset.mem_univ _)
      _ = ∑ i : Fin n, ({k | R k i}.ncard : ℝ) := hsum
      _ ≤ ∑ _i : Fin n, L := Finset.sum_le_sum fun i _ => hcross i
      _ = _ := by simp
  refine ⟨j, (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr ?_⟩
  simpa only [mul_comm] using hsmall

/-- The scalar part of the balanced-piece count, with the cube root explicit. -/
theorem balanced_piece_scalar {n N δ b M lam K : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hδ : 0 < δ) (hb : 0 < b)
    (hM : 0 < M) (hlam : 0 < lam)
    (henergy : M * (lam * n * δ ^ 2 / N) ≤
      (8192 * δ ^ 3 / b) * (n * (K * N ^ (1 / 3 : ℝ)) / N) ^ 2) :
    N ^ (1 / 3 : ℝ) ≤ 8192 * K ^ 2 * δ * n / (b * M * lam) := by
  let q := N ^ (1 / 3 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos hN _
  have hqcube : q ^ 3 = N := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hh : M * (lam * n * δ ^ 2 / q ^ 3) ≤
      (8192 * δ ^ 3 / b) * (n * (K * q) / q ^ 3) ^ 2 := by
    simpa only [hqcube] using henergy
  change q ≤ _
  apply (mul_le_mul_iff_right₀
    (by positivity : 0 < M * lam * n * δ ^ 2 / q ^ 4)).mp
  calc
    _ = M * (lam * n * δ ^ 2 / q ^ 3) := by field_simp
    _ ≤ (8192 * δ ^ 3 / b) * (n * (K * q) / q ^ 3) ^ 2 := hh
    _ = (M * lam * n * δ ^ 2 / q ^ 4) *
        (8192 * K ^ 2 * δ * n / (b * M * lam)) := by field_simp

/-- The incidence estimate at the end of Appendix A.5: balanced broad pieces
with a cube-root crossing bound cannot be too numerous. No geometric partition
is assumed beyond these explicit properties of its pieces. -/
theorem broad_balanced_piece_count {δ b M lam K : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 < M)
    (hlam : 0 < lam) {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (x v : Fin n → Space) (Y : Fin N → Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ j i, MeasurableSet (Y j i))
    (hYT : ∀ j i, Y j i ⊆ Tube δ (x i) (v i))
    (hfin : ∀ j i, volume (Y j i) ≠ ⊤)
    (hlower : ∀ j p, p ∈ ⋃ i, Y j i → M ≤ incidence (Y j) p)
    (hbroad : ∀ j p u, ‖u‖ = 1 →
      ({i | p ∈ Y j i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y j i}.ncard : ℝ))
    (hmass : ∀ j, lam * (n : ℝ) * δ ^ 2 / N ≤ shadingMass (Y j))
    (hcross : ∀ i, ({j | (Y j i).Nonempty}.ncard : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ)) :
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ 8192 * K ^ 2 * δ * n / (b * M * lam) := by
  obtain ⟨j, hj⟩ := exists_piece_small_degree hN (fun j i => (Y j i).Nonempty) hcross
  have henergy := broad_piece_mass_bound hδ hb hb1 x v (Y j) hv (hY j) (hYT j)
    (hfin j) (hlower j) (hbroad j)
  apply balanced_piece_scalar (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hN) hδ hb hM hlam
  calc
    _ ≤ M * shadingMass (Y j) := mul_le_mul_of_nonneg_left (hmass j) hM.le
    _ ≤ (8192 * δ ^ 3 / b) * ({i | (Y j i).Nonempty}.ncard : ℝ) ^ 2 := henergy
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hj 2)
      (by positivity)

/-- The same estimate for common spatial restrictions of one broad family.
Pointwise broadness and the multiplicity lower bound pass to each piece. -/
theorem broad_spatial_piece_count {δ b M lam K : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 < M) (hlam : 0 < lam)
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (E : Fin N → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hE : ∀ j, MeasurableSet (E j))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hlower : ∀ p ∈ ⋃ i, Y i, M ≤ incidence Y p)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ))
    (hmass : ∀ j, lam * (n : ℝ) * δ ^ 2 / N ≤ shadingMass (fun i => Y i ∩ E j))
    (hcross : ∀ i, ({j | (Y i ∩ E j).Nonempty}.ncard : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ)) :
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ 8192 * K ^ 2 * δ * n / (b * M * lam) := by
  apply broad_balanced_piece_count hδ hb hb1 hM hlam hn hN x v
    (fun j i => Y i ∩ E j) hv (fun j i => (hY i).inter (hE j))
    (fun _ i => inter_subset_left.trans (hYT i))
    (fun _ i => ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left)) ?_ ?_ hmass hcross
  · intro j p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have he : {k | p ∈ Y k ∩ E j} = {k | p ∈ Y k} := by
      ext k
      simp only [mem_setOf_eq, mem_inter_iff, hi.2, and_true]
    rw [incidence_eq_ncard, he, ← incidence_eq_ncard]
    exact hlower p (mem_iUnion.mpr ⟨i, hi.1⟩)
  · intro j p u hu
    by_cases hp : p ∈ E j
    · simpa only [mem_inter_iff, hp, and_true] using hbroad p u hu
    · simp only [mem_inter_iff, hp, and_false, false_and, setOf_false, ncard_empty,
        Nat.cast_zero, mul_zero, le_refl]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
