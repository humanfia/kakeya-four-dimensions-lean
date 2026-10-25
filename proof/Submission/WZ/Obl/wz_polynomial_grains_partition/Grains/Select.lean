-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Select.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Rec

/-!
# Selecting the grains of one level

Among finitely many disjoint pieces of `E` with masses at most `M`, at most `Nc` of positive
mass, carrying a `1/N` share of `E`: the pieces lighter than `M / 2^k₀` carry at most half of
the share (`2 Nc M N ≤ 2^k₀ |E|`), and a dyadic class `(m, 2m]` of the others carries a
`1/(2 k₀)` part of it (`select`). Its number `L` of pieces satisfies `L ≤ Nc`, `L m ≤ |E|` and
`|E| ≤ 4 k₀ N L m`; `finish` turns this into the frozen clauses of the grains decomposition.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Grains

open MeasureTheory

namespace SelectAux

/-- Selection of a dyadic mass class among the pieces of positive mass, and enumeration. -/
theorem select {ι : Type*} [Fintype ι] (P : ι → Set Space) (c : ι → Space)
    (Qp : ι → MvPolynomial (Fin 3) ℝ) {E : Set Space} {δ r M Nt Kd Nc : ℝ} {k₀ N : ℕ}
    (hmeas : ∀ i, MeasurableSet (P i)) (hsubE : ∀ i, P i ⊆ E)
    (hball : ∀ i, P i ⊆ Metric.closedBall (c i) r)
    (hpoly : ∀ i, Qp i ≠ 0 ∧ ((Qp i).totalDegree : ℝ) ≤ Kd ∧
      P i ⊆ Metric.thickening (100 * δ) {p : Space | MvPolynomial.eval (fun i => p i) (Qp i) = 0})
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hmax : ∀ i, volume (P i) ≤ ENNReal.ofReal M)
    (hcount : ((Finset.univ.filter fun i => volume (P i) ≠ 0).card : ℝ) ≤ Nc)
    (htube : ∀ x v : Space, ‖v‖ ≤ 1 →
      ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P i).Nonempty}.ncard : ℝ) ≤ Nt)
    (hEfin : volume E ≠ ⊤) (hE0 : volume E ≠ 0)
    (hmass : volume E ≤ (N : ENNReal) * ∑ i, volume (P i))
    (hk₀ : 2 * Nc * M * N ≤ 2 ^ k₀ * (volume E).toReal) (hk1 : 1 ≤ k₀) :
    ∃ (L : ℕ) (Q : Fin L → MvPolynomial (Fin 3) ℝ) (z : Fin L → Space)
      (G : Fin L → Set Space) (m : ℝ),
      0 < m ∧ (L : ℝ) ≤ Nc ∧ (L : ℝ) * m ≤ (volume E).toReal ∧
      (volume E).toReal ≤ 4 * k₀ * N * L * m ∧ m ≤ M ∧
      (∀ j, Q j ≠ 0 ∧ ((Q j).totalDegree : ℝ) ≤ Kd ∧ MeasurableSet (G j) ∧ G j ⊆ E ∧
        G j ⊆ Metric.thickening (100 * δ)
          {p : Space | MvPolynomial.eval (fun i => p i) (Q j) = 0} ∧
        G j ⊆ Metric.closedBall (z j) r) ∧
      (∀ j j', j ≠ j' → Disjoint (G j) (G j')) ∧
      (∀ j, ENNReal.ofReal m ≤ volume (G j) ∧ volume (G j) ≤ ENNReal.ofReal (2 * m)) ∧
      ENNReal.ofReal (1 / (2 * k₀ * N)) * volume E ≤ ∑ j, volume (G j) ∧
      ∀ x v : Space, ‖v‖ ≤ 1 →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ G j).Nonempty}.ncard : ℝ) ≤ Nt := by
  classical
  -- real weights
  have hfin : ∀ i, volume (P i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hEfin (measure_mono (hsubE i))
  set w : ι → ℝ := fun i => (volume (P i)).toReal with hw_def
  have hw : ∀ i, volume (P i) = ENNReal.ofReal (w i) := fun i =>
    (ENNReal.ofReal_toReal (hfin i)).symm
  have hw0 : ∀ i, 0 ≤ w i := fun i => ENNReal.toReal_nonneg
  set F : ℝ := ∑ i, w i with hF_def
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => hw0 i
  have hsumP : ∀ S : Finset ι, ∑ i ∈ S, volume (P i) = ENNReal.ofReal (∑ i ∈ S, w i) := by
    intro S
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i)]
    exact Finset.sum_congr rfl fun i _ => hw i
  set e : ℝ := (volume E).toReal with he_def
  have he0 : 0 < e := ENNReal.toReal_pos hE0 hEfin
  -- `F ≤ |E| ≤ N F`
  have hFE : F ≤ e := by
    have h1 : ∑ i, volume (P i) ≤ volume E := by
      have hU := measure_iUnion (μ := volume) hdisj hmeas
      rw [tsum_fintype] at hU
      rw [← hU]
      exact measure_mono (Set.iUnion_subset hsubE)
    rw [hsumP Finset.univ] at h1
    have := ENNReal.toReal_mono hEfin h1
    rwa [ENNReal.toReal_ofReal hF0] at this
  have heNF : e ≤ N * F := by
    have h1 := hmass
    rw [hsumP Finset.univ, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hN : (1 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul] at heNF
      linarith
    · exact_mod_cast hpos
  have hFpos : 0 < F := by
    by_contra h
    push Not at h
    have : (N : ℝ) * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  obtain ⟨i1, -, hi1⟩ : ∃ i ∈ Finset.univ, 0 < w i := by
    by_contra h
    push Not at h
    have : F ≤ 0 := Finset.sum_nonpos fun i hi => h i hi
    linarith
  have hM0 : 0 < M := by
    have h1 := hmax i1
    rw [hw] at h1
    have h2 : 0 < ENNReal.ofReal M := lt_of_lt_of_le (ENNReal.ofReal_pos.2 hi1) h1
    exact ENNReal.ofReal_pos.1 h2
  have hwM : ∀ i, w i ≤ M := by
    intro i
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmax i)
    rwa [ENNReal.toReal_ofReal hM0.le] at this
  -- the big pieces carry at least half of the mass
  set Sb := Finset.univ.filter fun i => M / 2 ^ k₀ < w i with hSb_def
  have hSb : F / 2 ≤ ∑ i ∈ Sb, w i := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => M / 2 ^ k₀ < w i) w
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ M / 2 ^ k₀ < w i), w i ≤ Nc * (M / 2 ^ k₀) := by
      calc _ ≤ ∑ i ∈ (Finset.univ.filter fun i => volume (P i) ≠ 0), M / 2 ^ k₀ := by
            rw [← Finset.sum_filter_add_sum_filter_not
              (Finset.univ.filter (fun i => ¬ M / 2 ^ k₀ < w i)) (fun i => volume (P i) ≠ 0)]
            have hz : ∑ i ∈ (Finset.univ.filter (fun i => ¬ M / 2 ^ k₀ < w i)).filter
                (fun i => ¬ volume (P i) ≠ 0), w i = 0 := by
              refine Finset.sum_eq_zero fun i hi => ?_
              rw [Finset.mem_filter, not_not] at hi
              rw [hw_def]
              simp [hi.2]
            rw [hz, add_zero]
            calc _ ≤ ∑ i ∈ (Finset.univ.filter (fun i => ¬ M / 2 ^ k₀ < w i)).filter
                  (fun i => volume (P i) ≠ 0), M / 2 ^ k₀ :=
                  Finset.sum_le_sum fun i hi =>
                    not_lt.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
              _ ≤ _ := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro i hi
                    rw [Finset.mem_filter] at hi ⊢
                    exact ⟨Finset.mem_univ _, hi.2⟩
                  · intro i _ _
                    positivity
        _ = ((Finset.univ.filter fun i => volume (P i) ≠ 0).card : ℝ) * (M / 2 ^ k₀) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Nc * (M / 2 ^ k₀) := mul_le_mul_of_nonneg_right hcount (by positivity)
    have h3 : Nc * (M / 2 ^ k₀) ≤ F / 2 := by
      have h5 : (0 : ℝ) < 2 ^ k₀ := by positivity
      rw [mul_div_assoc', div_le_div_iff₀ h5 (by norm_num)]
      have h6 : 2 * Nc * M * N ≤ 2 ^ k₀ * (N * F) :=
        hk₀.trans (mul_le_mul_of_nonneg_left heNF h5.le)
      have h7 : Nc * M * 2 * N ≤ F * 2 ^ k₀ * N := by linarith
      by_contra hcon
      push Not at hcon
      have := mul_lt_mul_of_pos_right hcon (by linarith : (0 : ℝ) < N)
      linarith
    linarith
  -- dyadic classes of the big pieces
  have hbig : ∀ i ∈ Sb, M / 2 ^ (k₀ - 1 + 1) < w i := by
    intro i hi
    rw [Nat.sub_add_cancel hk1]
    exact (Finset.mem_filter.1 hi).2
  let cls : ι → ℕ := fun i => if h : ∃ k : ℕ, M / 2 ^ (k + 1) < w i then Nat.find h else 0
  have hcls : ∀ i ∈ Sb, cls i < k₀ ∧ M / 2 ^ (cls i + 1) < w i ∧ w i ≤ M / 2 ^ cls i := by
    intro i hi
    have h : ∃ k : ℕ, M / 2 ^ (k + 1) < w i := ⟨k₀ - 1, hbig i hi⟩
    have hc : cls i = Nat.find h := dite_eq_left h
    rw [hc]
    refine ⟨?_, Nat.find_spec h, ?_⟩
    · have := Nat.find_min' h (hbig i hi)
      omega
    · rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · rw [h0, pow_zero, div_one]
        exact hwM i
      · have := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.1 this
  have hk₀R : (0 : ℝ) < k₀ := by exact_mod_cast hk1
  obtain ⟨k, -, hkS⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := Sb) (t := Finset.range k₀) (f := cls) (w := w) (b := F / (2 * k₀))
    (fun i hi => Finset.mem_range.2 (hcls i hi).1) ⟨0, Finset.mem_range.2 hk1⟩
    (by
      rw [Finset.card_range, nsmul_eq_mul]
      calc (k₀ : ℝ) * (F / (2 * k₀)) = F / 2 := by field_simp
        _ ≤ _ := hSb)
  set S := Sb.filter fun i => cls i = k with hS_def
  set m : ℝ := M / 2 ^ (k + 1) with hm_def
  have hSprop : ∀ i ∈ S, m < w i ∧ w i ≤ 2 * m := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨-, h1, h2⟩ := hcls i hi1
    rw [hi2] at h1 h2
    refine ⟨h1, ?_⟩
    calc w i ≤ M / 2 ^ k := h2
      _ = 2 * m := by rw [hm_def, pow_succ]; field_simp
  have hS0 : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg fun i _ => hw0 i
  have hFS : F ≤ 2 * k₀ * ∑ i ∈ S, w i := by
    rw [div_le_iff₀ (by positivity)] at hkS
    linarith
  obtain ⟨i0, hi0⟩ : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hFS
      linarith
    · exact h
  have hm0 : 0 < m := by
    have h1 := (hSprop i0 hi0).1
    have h2 := (hSprop i0 hi0).2
    linarith [hw0 i0]
  have hmM : m ≤ M := by
    rw [hm_def]
    exact div_le_self hM0.le (one_le_pow₀ (by norm_num))
  have hSw : ∀ i ∈ S, volume (P i) ≠ 0 := by
    intro i hi
    have := (hSprop i hi).1
    rw [hw]
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hLc : (S.card : ℝ) ≤ Nc := by
    refine le_trans ?_ hcount
    exact_mod_cast Finset.card_le_card fun i hi => Finset.mem_filter.2
      ⟨Finset.mem_univ _, hSw i hi⟩
  have hLm1 : (S.card : ℝ) * m ≤ ∑ i ∈ S, w i := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => (hSprop i hi).1.le
  have hLm2 : ∑ i ∈ S, w i ≤ (S.card : ℝ) * (2 * m) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => (hSprop i hi).2
  have hSF : ∑ i ∈ S, w i ≤ F :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw0 i)
  refine ⟨S.card, fun j => Qp (S.equivFin.symm j).1, fun j => c (S.equivFin.symm j).1,
    fun j => P (S.equivFin.symm j).1, m, hm0, hLc, ?_, ?_, hmM, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · calc e ≤ N * F := heNF
      _ ≤ N * (2 * k₀ * ∑ i ∈ S, w i) := mul_le_mul_of_nonneg_left hFS (by positivity)
      _ ≤ N * (2 * k₀ * ((S.card : ℝ) * (2 * m))) := by gcongr
      _ = 4 * k₀ * N * S.card * m := by ring
  · intro j
    obtain ⟨h1, h2, h3⟩ := hpoly (S.equivFin.symm j).1
    exact ⟨h1, h2, hmeas _, hsubE _, h3, hball _⟩
  · intro j j' hjj'
    apply hdisj
    intro h
    apply hjj'
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j
    have hj := hSprop _ (S.equivFin.symm j).2
    rw [hw]
    exact ⟨ENNReal.ofReal_le_ofReal hj.1.le, ENNReal.ofReal_le_ofReal hj.2⟩
  · have hsum : ∑ j, volume (P (S.equivFin.symm j).1) = ENNReal.ofReal (∑ i ∈ S, w i) := by
      rw [← hsumP S, Fintype.sum_equiv S.equivFin.symm _ (fun x => volume (P x.1))
        (fun j => rfl)]
      exact Finset.sum_coe_sort S (fun i => volume (P i))
    rw [hsum, ← ENNReal.ofReal_toReal hEfin, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← he_def]
    have h2 : 0 < 2 * (k₀ : ℝ) * N := by positivity
    rw [one_div, inv_mul_le_iff₀ h2]
    calc e ≤ N * F := heNF
      _ ≤ N * (2 * k₀ * ∑ i ∈ S, w i) := mul_le_mul_of_nonneg_left hFS (by positivity)
      _ = 2 * k₀ * N * ∑ i ∈ S, w i := by ring
  · intro x v hv
    refine le_trans ?_ (htube x v hv)
    have := Set.ncard_le_ncard_of_injOn
      (s := {j : Fin S.card | (Metric.thickening δ (segment ℝ x (x + v)) ∩
        P (S.equivFin.symm j).1).Nonempty})
      (t := {i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P i).Nonempty})
      (fun j => (S.equivFin.symm j).1) (fun j hj => hj)
      (fun j _ j' _ h => S.equivFin.symm.injective (Subtype.ext h)) (Set.toFinite _)
    exact_mod_cast this

/-- `a · L^(1/3) ≤ b` from `a^3 L ≤ b^3`. -/
lemma mul_rpow_third_le {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (h : a ^ 3 * L ≤ b ^ 3) : a * L ^ (1 / 3 : ℝ) ≤ b := by
  have hc : (L ^ (1 / 3 : ℝ)) ^ 3 = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  have hpos : 0 ≤ a * L ^ (1 / 3 : ℝ) := mul_nonneg ha (Real.rpow_nonneg hL _)
  refine (pow_le_pow_iff_left₀ hpos hb (by norm_num : (3 : ℕ) ≠ 0)).1 ?_
  rw [mul_pow, hc]
  exact h

/-- The frozen clauses from the selected class. -/
theorem finish {E : Set Space} {K ε δ r M Nt Kd Nc m : ℝ} {k₀ N L : ℕ}
    (Q : Fin L → MvPolynomial (Fin 3) ℝ) (z : Fin L → Space) (G : Fin L → Set Space)
    (hδ : 0 < δ) (hK : 0 < K) (hr : 0 ≤ r) (hKd : Kd ≤ K)
    (hdiam : r ^ 3 * Nc ≤ (K * δ ^ (-ε)) ^ 3)
    (hmassK : 4 * k₀ * N ≤ K * δ ^ (-ε)) (htwo : 2 ≤ K * δ ^ (-ε))
    (htubeK : Nt ^ 3 * (4 * k₀ * N * M) ≤ (K * δ ^ (-ε)) ^ 3 * (volume E).toReal)
    (hk1 : 1 ≤ k₀) (hN : 1 ≤ N) (hEfin : volume E ≠ ⊤) (hE0 : volume E ≠ 0) (hNt : 0 ≤ Nt)
    (hm : 0 < m) (hLc : (L : ℝ) ≤ Nc) (hLm : (L : ℝ) * m ≤ (volume E).toReal)
    (hEL : (volume E).toReal ≤ 4 * k₀ * N * L * m) (hmM : m ≤ M)
    (hG : ∀ j, Q j ≠ 0 ∧ ((Q j).totalDegree : ℝ) ≤ Kd ∧ MeasurableSet (G j) ∧ G j ⊆ E ∧
        G j ⊆ Metric.thickening (100 * δ)
          {p : Space | MvPolynomial.eval (fun i => p i) (Q j) = 0} ∧
        G j ⊆ Metric.closedBall (z j) r)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (G j) (G j'))
    (hmasses : ∀ j, ENNReal.ofReal m ≤ volume (G j) ∧ volume (G j) ≤ ENNReal.ofReal (2 * m))
    (hsum : ENNReal.ofReal (1 / (2 * k₀ * N)) * volume E ≤ ∑ j, volume (G j))
    (htube : ∀ x v : Space, ‖v‖ ≤ 1 →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ G j).Nonempty}.ncard : ℝ) ≤ Nt) :
    (∀ j, Q j ≠ 0 ∧ ((Q j).totalDegree : ℝ) ≤ K ∧ MeasurableSet (G j) ∧ G j ⊆ E ∧
      G j ⊆ Metric.thickening (100 * δ)
        {p : Space | MvPolynomial.eval (fun i => p i) (Q j) = 0} ∧
      G j ⊆ Metric.closedBall (z j) (K * δ ^ (-ε) * (L : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
    (∀ j j', j ≠ j' → Disjoint (G j) (G j')) ∧
    ENNReal.ofReal (K⁻¹ * δ ^ ε) * volume E ≤ ∑ j, volume (G j) ∧
    (∀ j, ENNReal.ofReal (K⁻¹ * δ ^ ε / L) * volume E ≤ volume (G j) ∧
      volume (G j) ≤ ENNReal.ofReal (K * δ ^ (-ε) / L) * volume E) ∧
    ∀ p u : Space, ‖u‖ = 1 →
      (({j | (Metric.thickening δ (segment ℝ p (p + u)) ∩ G j).Nonempty}.ncard : ℝ) ≤
        K * δ ^ (-ε) * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  set X : ℝ := K * δ ^ (-ε) with hX
  set e : ℝ := (volume E).toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hE0 hEfin
  have hX0 : 0 < X := by rw [hX]; positivity
  have hk₀R : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLpos : (0 : ℝ) < L := by
    have : 0 < (L : ℝ) * m := by
      have := hEL
      by_contra h
      push Not at h
      have h1 : 4 * (k₀ : ℝ) * N * L * m = 4 * k₀ * N * (L * m) := by ring
      have h2 : 4 * (k₀ : ℝ) * N * (L * m) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      linarith
    exact pos_of_mul_pos_left this hm.le
  have hδε : δ ^ ε * δ ^ (-ε) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hKinv : K⁻¹ * δ ^ ε = X⁻¹ := by
    rw [hX, mul_inv, Real.rpow_neg hδ.le, inv_inv]
  have hEeq : volume E = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEfin).symm
  refine ⟨fun j => ?_, hdisj, ?_, fun j => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG j
    refine ⟨h1, h2.trans hKd, h3, h4, h5, h6.trans (Metric.closedBall_subset_closedBall ?_)⟩
    -- `r ≤ X L^(-1/3)`
    have hL3 : (L : ℝ) ^ (-(1 / 3 : ℝ)) = ((L : ℝ) ^ (1 / 3 : ℝ))⁻¹ :=
      Real.rpow_neg hLpos.le _
    rw [hL3, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    refine mul_rpow_third_le hr hX0.le hLpos.le ?_
    calc r ^ 3 * L ≤ r ^ 3 * Nc := mul_le_mul_of_nonneg_left hLc (by positivity)
      _ ≤ X ^ 3 := hdiam
  · rw [hKinv]
    refine le_trans ?_ hsum
    gcongr
    rw [one_div]
    apply inv_anti₀ (by positivity)
    linarith
  · rw [hKinv, hEeq, ← ENNReal.ofReal_mul (by positivity)]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hmasses j).1
    rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
    rw [inv_mul_le_iff₀ hX0]
    calc e ≤ 4 * k₀ * N * L * m := hEL
      _ = (4 * k₀ * N) * (m * L) := by ring
      _ ≤ X * (m * L) := mul_le_mul_of_nonneg_right hmassK (by positivity)
  · rw [hEeq, ← ENNReal.ofReal_mul (by positivity)]
    refine le_trans (hmasses j).2 (ENNReal.ofReal_le_ofReal ?_)
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
    calc 2 * m * L = 2 * (L * m) := by ring
      _ ≤ X * e := mul_le_mul htwo hLm (by positivity) hX0.le
  · intro x u hu
    refine (htube x u hu.le).trans ?_
    -- `Nt ≤ X L^(1/3)` from `Nt^3 ≤ X^3 L`
    have hM0 : 0 < 4 * (k₀ : ℝ) * N * M := by
      have : 0 < M := lt_of_lt_of_le hm hmM
      positivity
    have h1 : Nt ^ 3 ≤ X ^ 3 * L := by
      have h2 : Nt ^ 3 * (4 * k₀ * N * M) ≤ X ^ 3 * L * (4 * k₀ * N * M) := by
        calc Nt ^ 3 * (4 * k₀ * N * M) ≤ X ^ 3 * e := htubeK
          _ ≤ X ^ 3 * (4 * k₀ * N * L * m) := mul_le_mul_of_nonneg_left hEL (by positivity)
          _ ≤ X ^ 3 * (4 * k₀ * N * L * M) := by gcongr
          _ = X ^ 3 * L * (4 * k₀ * N * M) := by ring
      exact le_of_mul_le_mul_right h2 hM0
    have h3 := mul_rpow_third_le (a := 1) (b := X / Nt * Nt) zero_le_one (by positivity)
      hLpos.le
    by_cases hNt0 : Nt = 0
    · rw [hNt0]; positivity
    · have hNtpos : 0 < Nt := lt_of_le_of_ne hNt (Ne.symm hNt0)
      -- `Nt ≤ X L^(1/3)` iff `(Nt / L^(1/3)) ≤ X`
      have hc : ((L : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
        norm_num
      have hpos : 0 ≤ X * (L : ℝ) ^ (1 / 3 : ℝ) := by positivity
      refine (pow_le_pow_iff_left₀ hNt hpos (by norm_num : (3 : ℕ) ≠ 0)).1 ?_
      rw [mul_pow, hc]
      exact h1

end SelectAux
end Grains
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
