-- Adapted from LOT tree g-oai-074, obligation o173, session x0581,
-- commit ac37073d, Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SampleCover.lean.
import Submission.Obl.k4_clean_cover_graph_atlas.SampleInput
import Submission.Obl.k4_clean_cover_graph_atlas.Compatibility

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface

/-- The half-open sub-block. -/
def subIco (T s₀ j₀ jj : ℕ) : Set ℝ :=
  Set.Ico ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀)) (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))

theorem subIco_subset (T s₀ j₀ jj : ℕ) : subIco T s₀ j₀ jj ⊆ subBlock T s₀ j₀ jj :=
  Set.Ico_subset_Icc_self

/-- Half-open dyadic intervals of distinct indices are disjoint. -/
theorem disjoint_Ico_nat {M : ℝ} (hM : 0 < M) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (Set.Ico ((a : ℝ) / M) (((a : ℝ) + 1) / M))
      (Set.Ico ((b : ℝ) / M) (((b : ℝ) + 1) / M)) := by
  rw [Set.disjoint_left]
  rintro t ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
  rw [div_le_iff₀ hM] at ha1 hb1
  rw [lt_div_iff₀ hM] at ha2 hb2
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith

section Cover

variable {n C : ℕ} (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
  (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (j : Fin C → ℕ)
  (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
  (R : Fin C → MvPolynomial (Fin 4) ℝ) (Ti s₀ K : ℕ)
  (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))

/-- The raw covered incidences of an entry. -/
def rawCov (e : Entry n s₀ K) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  V e.1 ∩ {p | p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧
    p.2 ∈ subIco Ti s₀ (j (old e.1)) e.2.1}

theorem measurableSet_memE {H : ℝ} {Dg : ℕ}
    (hA' : ∀ a q, gfmt 6 H Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (e : Entry n s₀ K) : MeasurableSet (memE old R' A' j c u Q R Ti s₀ K e) :=
  measurableSet_of_slices6 fun q => measurableSet_of_gfmt (gfmt_memE hA' hR' hR e q)

theorem measurableSet_rawCov {H : ℝ} {Dg : ℕ}
    (hA' : ∀ a q, gfmt 6 H Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (hV : ∀ a, MeasurableSet (V a)) (e : Entry n s₀ K) :
    MeasurableSet (rawCov old R' A' j c u Q R Ti s₀ K V e) := by
  refine (hV e.1).inter (MeasurableSet.inter ?_ ?_)
  · exact measurable_fst (measurableSet_memE old R' A' j c u Q R Ti s₀ K hA' hR' hR e)
  · exact measurable_snd measurableSet_Ico

theorem rawCov_disjoint
    {W : ℕ} (γ : Fin C → Fin W)
    (hVdisj : ∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a'))
    {e e' : Entry n s₀ K} (hne : e ≠ e') (hγ : γ (old e.1) = γ (old e'.1)) :
    Disjoint (rawCov old R' A' j c u Q R Ti s₀ K V e) (rawCov old R' A' j c u Q R Ti s₀ K V e') := by
  by_cases ha : e.1 = e'.1
  · by_cases hjj : e.2.1 = e'.2.1
    · have hm := memE_disjoint_of_ne old R' A' j c u Q R Ti s₀ K ha hjj hne
      rw [Set.disjoint_left] at hm ⊢
      intro p hp hp'
      exact hm hp.2.1 hp'.2.1
    · have hidx : subIdx s₀ (j (old e.1)) e.2.1 ≠ subIdx s₀ (j (old e'.1)) e'.2.1 := by
        intro h
        exact hjj (Fin.ext (subIdx_inj e.2.1.2 e'.2.1.2 h).2)
      have hd := disjoint_Ico_nat (M := (2 : ℝ) ^ (Ti + s₀)) (by positivity) hidx
      rw [Set.disjoint_left] at hd ⊢
      intro p hp hp'
      exact hd hp.2.2 hp'.2.2
  · exact (hVdisj e.1 e'.1 ha hγ).mono Set.inter_subset_left Set.inter_subset_left

/-- **Witness incidences lie in raw covered sets.** A witness incidence of candidate `a` before the
right end of the old block lies in the raw covered set of the entry of its sub-block, of the box of
its line at the sub-block midpoint and of its two derivative signs there. -/
theorem exists_rawCov_of_witness {κ : ℝ} (hK : κ * (2 : ℝ) ^ s₀ ≤ K) (a : Fin n)
    (hzc : ∀ l ∈ A' a, ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti)
      (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti), ‖zc (Q (old a)) (c (old a)) (u (old a)) l t‖ ≤ κ)
    {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hp : p ∈ V a) (hpA : p.1 ∈ A' a)
    (hpt : p.2 ∈ Set.Ico ((j (old a) : ℝ) / (2 : ℝ) ^ Ti) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti)) :
    ∃ e : Entry n s₀ K, e.1 = a ∧ p ∈ rawCov old R' A' j c u Q R Ti s₀ K V e := by
  set j₀ := j (old a) with hj₀
  have h2T : (0 : ℝ) < (2 : ℝ) ^ Ti := by positivity
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s₀ := by positivity
  have h2Ts : (2 : ℝ) ^ (Ti + s₀) = (2 : ℝ) ^ Ti * (2 : ℝ) ^ s₀ := pow_add _ _ _
  obtain ⟨ht1, ht2⟩ := hpt
  rw [div_le_iff₀ h2T] at ht1
  rw [lt_div_iff₀ h2T] at ht2
  -- the sub-block
  set X : ℝ := p.2 * (2 : ℝ) ^ (Ti + s₀) with hX
  have hX1 : ((j₀ * 2 ^ s₀ : ℕ) : ℝ) ≤ X := by
    rw [hX, h2Ts]; push_cast; nlinarith
  have hX2 : X < (((j₀ + 1) * 2 ^ s₀ : ℕ) : ℝ) := by
    rw [hX, h2Ts]; push_cast; nlinarith
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) hX1
  set N := ⌊X⌋₊ with hN
  have hN1 : j₀ * 2 ^ s₀ ≤ N := Nat.le_floor hX1
  have hN2 : N < (j₀ + 1) * 2 ^ s₀ := by
    have : (N : ℝ) < (((j₀ + 1) * 2 ^ s₀ : ℕ) : ℝ) := lt_of_le_of_lt (Nat.floor_le hX0) hX2
    exact_mod_cast this
  set jj := N - j₀ * 2 ^ s₀ with hjj
  have hjjlt : jj < 2 ^ s₀ := by
    have : (j₀ + 1) * 2 ^ s₀ = j₀ * 2 ^ s₀ + 2 ^ s₀ := by ring
    omega
  have hsub : subIdx s₀ j₀ jj = N := by unfold subIdx; omega
  have hpIco : p.2 ∈ subIco Ti s₀ j₀ jj := by
    unfold subIco
    rw [hsub]
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ (Ti + s₀) := by positivity
    constructor
    · rw [div_le_iff₀ hp2]; exact Nat.floor_le hX0
    · rw [lt_div_iff₀ hp2]; exact Nat.lt_floor_add_one X
  -- the box at the midpoint
  set tm := subMid Ti s₀ j₀ jj with htm
  have htm_mem : tm ∈ Set.Icc ((j₀ : ℝ) / (2 : ℝ) ^ Ti) (((j₀ : ℝ) + 1) / (2 : ℝ) ^ Ti) :=
    subblock_subset hjjlt (subMid_mem Ti s₀ j₀ jj)
  set z := zc (Q (old a)) (c (old a)) (u (old a)) p.1 tm with hz
  have hzκ : ‖z‖ ≤ κ := hzc p.1 hpA tm htm_mem
  have hcoord : ∀ e : Fin 2, -(K : ℤ) ≤ boxIdx s₀ z e ∧ boxIdx s₀ z e ≤ K := by
    intro e
    have hze : |z e| ≤ κ := by
      have := PiLp.norm_apply_le z e
      rw [Real.norm_eq_abs] at this
      exact this.trans hzκ
    have hdiv : z e / side s₀ = z e * (2 : ℝ) ^ s₀ := by
      unfold side; rw [div_inv_eq_mul]
    have hb : |z e * (2 : ℝ) ^ s₀| ≤ K := by
      rw [abs_mul, abs_of_pos h2s]
      exact (mul_le_mul_of_nonneg_right hze h2s.le).trans hK
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    unfold boxIdx
    rw [hdiv]
    constructor
    · have : ((-(K : ℤ) : ℤ) : ℝ) ≤ z e * (2 : ℝ) ^ s₀ := by push_cast; linarith
      exact Int.le_floor.mpr this
    · have : ⌊z e * (2 : ℝ) ^ s₀⌋ ≤ ⌊(K : ℝ)⌋ := Int.floor_mono hb2
      simpa using this
  let k : Fin 2 → Fin (2 * K + 2) := fun e =>
    ⟨(boxIdx s₀ z e + K + 1).toNat, by
      have h := hcoord e
      have : (boxIdx s₀ z e + K + 1).toNat < 2 * K + 2 := by omega
      exact this⟩
  have hk : boxOf K k = boxIdx s₀ z := by
    funext e
    have h := hcoord e
    simp only [boxOf, k, Fin.val_mk]
    omega
  -- the entry
  refine ⟨(a, ⟨jj, hjjlt⟩, k,
    decide (0 ≤ eval (gx p.1 tm) (pderiv 3 (R' a))),
    decide (0 ≤ eval (gx p.1 tm) (pderiv 3 (R (old a))))), rfl, hp, ?_, hpIco⟩
  exact ⟨hpA, hk.symm, rfl, rfl⟩

/-- **The raw covered sets carry each witness set.** -/
theorem measure_witness_le_sum_rawCov {κ : ℝ} (hK : κ * (2 : ℝ) ^ s₀ ≤ K) (a : Fin n)
    (hzc : ∀ l ∈ A' a, ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti)
      (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti), ‖zc (Q (old a)) (c (old a)) (u (old a)) l t‖ ≤ κ)
    (hVsub : V a ⊆ {p | p.1 ∈ A' a ∧
      p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti)})
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hnull : μ {p | p.2 = ((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti} = 0) :
    μ (V a) ≤ ∑ e ∈ Finset.univ.filter (fun e : Entry n s₀ K => e.1 = a),
      μ (rawCov old R' A' j c u Q R Ti s₀ K V e) := by
  classical
  have hcover : V a ⊆ (⋃ e ∈ Finset.univ.filter (fun e : Entry n s₀ K => e.1 = a),
      rawCov old R' A' j c u Q R Ti s₀ K V e) ∪
      {p | p.2 = ((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti} := by
    intro p hp
    obtain ⟨hpA, ht1, ht2⟩ := hVsub hp
    rcases eq_or_lt_of_le ht2 with heq | hlt
    · exact Or.inr heq
    · obtain ⟨e, he, hpe⟩ := exists_rawCov_of_witness old R' A' j c u Q R Ti s₀ K V hK a hzc hp
        hpA ⟨ht1, hlt⟩
      refine Or.inl (Set.mem_biUnion (x := e) ?_ hpe)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  calc μ (V a) ≤ μ ((⋃ e ∈ Finset.univ.filter (fun e : Entry n s₀ K => e.1 = a),
        rawCov old R' A' j c u Q R Ti s₀ K V e) ∪
        {p | p.2 = ((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti}) := measure_mono hcover
    _ ≤ μ (⋃ e ∈ Finset.univ.filter (fun e : Entry n s₀ K => e.1 = a),
        rawCov old R' A' j c u Q R Ti s₀ K V e) +
        μ {p | p.2 = ((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti} := measure_union_le _ _
    _ = μ (⋃ e ∈ Finset.univ.filter (fun e : Entry n s₀ K => e.1 = a),
        rawCov old R' A' j c u Q R Ti s₀ K V e) := by rw [hnull, add_zero]
    _ ≤ _ := measure_biUnion_finset_le _ _

end Cover

end Submission.Obl.k4_clean_cover_graph_atlas
