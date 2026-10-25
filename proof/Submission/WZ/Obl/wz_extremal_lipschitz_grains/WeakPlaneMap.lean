-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.WeakPlaneMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlane
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TrilinearKakeya

/-!
# A weak plane map for families of tubes

`weak_plane_map` is sticky Lemma 4.3 in a form that needs no robust transversality.  The broad
points (more than a hundredth of the ordered triples of directions through the point are
`θ`-transversal) have small volume by `MK.trilinear_kakeya` and Markov's inequality.  On every
other shading atom, `plane_selection_narrow` keeps a quarter of the incidences near one plane:
either half the ordered pairs are `β`-transverse and the normal is a normalized cross product
(precision `θ / β`), or some direction has half the others within `β` and the normal is
orthogonal to it (precision `β`).
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The scalar triple product is the determinant of the coordinate vectors. -/
theorem inner_cross_eq_det3 (u w z : Space) :
    inner ℝ z (cross u w) = MK.det3 (WithLp.ofLp u) (WithLp.ofLp w) (WithLp.ofLp z) := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, MK.det3]
  simp [crossProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- Bessel's inequality for two orthonormal vectors. -/
theorem inner_sq_add_inner_sq_le {u N w : Space} (hu : ‖u‖ = 1) (hN : ‖N‖ = 1)
    (huN : inner ℝ u N = 0) : inner ℝ w u ^ 2 + inner ℝ w N ^ 2 ≤ ‖w‖ ^ 2 := by
  have h := real_inner_self_nonneg (x := w - inner ℝ w u • u - inner ℝ w N • N)
  have huN' : inner ℝ N u = 0 := by rw [real_inner_comm]; exact huN
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, huN, huN', real_inner_comm w u, real_inner_comm w N, norm_smul,
    Real.norm_eq_abs, hu, hN, mul_one, sq_abs] at h
  nlinarith

/-- A unit vector orthogonal to `u` controls inner products by the cross product with `u`. -/
theorem abs_inner_le_norm_cross {u N w : Space} (hu : ‖u‖ = 1) (hN : ‖N‖ = 1)
    (huN : inner ℝ u N = 0) : |inner ℝ w N| ≤ ‖cross u w‖ := by
  have h1 := inner_sq_add_inner_sq_le (w := w) hu hN huN
  have h2 := cross_norm_sq u w
  rw [hu, one_pow, one_mul, real_inner_comm w u] at h2
  apply abs_le_of_sq_le_sq _ (norm_nonneg _)
  nlinarith

/-- Every unit vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal {u : Space} (hu : ‖u‖ = 1) :
    ∃ N : Space, ‖N‖ = 1 ∧ inner ℝ u N = 0 := by
  have hsq : ∀ k : Fin 3, ‖cross u (EuclideanSpace.single k 1)‖ ^ 2 = 1 - u k ^ 2 := by
    intro k
    rw [cross_norm_sq, hu, PiLp.norm_single, EuclideanSpace.inner_single_right]
    simp
  have hnorm : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq u
    rw [hu, eq_comm, Real.sqrt_eq_one, Fin.sum_univ_three] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hex : ∃ k : Fin 3, cross u (EuclideanSpace.single k 1) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 := hsq 0; have h1 := hsq 1
    rw [hall 0, norm_zero] at h0; rw [hall 1, norm_zero] at h1
    nlinarith [sq_nonneg (u 2)]
  obtain ⟨k, hk⟩ := hex
  refine ⟨‖cross u (EuclideanSpace.single k 1)‖⁻¹ • cross u (EuclideanSpace.single k 1),
    norm_smul_inv_norm hk, ?_⟩
  rw [inner_smul_right, inner_cross_left, mul_zero]


/-- Number of `θ`-transversal ordered triples of directions from `s`. -/
noncomputable def transCount {ι : Type*} (s : Finset ι) (v : ι → Space) (θ : ℝ) : ℕ := by
  classical exact ((s ×ˢ s ×ˢ s).filter fun t =>
    θ ≤ |inner ℝ (v t.2.2) (cross (v t.1) (v t.2.1))|).card

/-- **Plane selection at a narrow point.**  If at most a hundredth of the ordered triples of the
unit directions in `s` are `θ`-transversal, then a quarter of `s` lies within `max (θ/β) β` of a
plane: either half of the ordered pairs are `β`-transverse (normal = normalized cross product), or
some direction has half of the others within `β` (normal orthogonal to it). -/
theorem plane_selection_narrow {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → Space)
    (hv : ∀ i ∈ s, ‖v i‖ = 1) (hs : s.Nonempty) {θ β : ℝ} (hθ : 0 < θ) (hβ : 0 < β)
    (hnarrow : 100 * transCount s v θ ≤ s.card ^ 3) :
    ∃ (F : Finset ι) (N : Space), F ⊆ s ∧ s.card ≤ 4 * F.card ∧ ‖N‖ = 1 ∧
      ∀ k ∈ F, |inner ℝ (v k) N| ≤ max (θ / β) β := by
  classical
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  by_cases hpairs : (s.card : ℝ) ^ 2 ≤
      2 * (((s.product s).filter fun ij => β ≤ ‖cross (v ij.1) (v ij.2)‖).card : ℝ)
  · -- many transverse pairs
    have htriples : (∑ i ∈ s, ∑ j ∈ s,
        ((s.filter fun k => θ < |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ)) ≤
          (s.card : ℝ) ^ 3 / 4 := by
      have hle : (∑ i ∈ s, ∑ j ∈ s,
          ((s.filter fun k => θ < |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ)) ≤
            (transCount s v θ : ℝ) := by
        have e : (transCount s v θ : ℝ) = ∑ i ∈ s, ∑ j ∈ s,
            ((s.filter fun k => θ ≤ |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ) := by
          unfold transCount
          rw [Finset.card_filter, Finset.sum_product, Nat.cast_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_product, Nat.cast_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter, Nat.cast_sum]
        rw [e]
        gcongr with i _ j _ k
        exact fun hk => le_of_lt hk
      have h100 : (100 : ℝ) * transCount s v θ ≤ (s.card : ℝ) ^ 3 := by exact_mod_cast hnarrow
      have h0 : (0 : ℝ) ≤ transCount s v θ := Nat.cast_nonneg _
      nlinarith [pow_pos hn 3]
    obtain ⟨F, N, hF, hcard, hN, hin⟩ := narrow_plane_selection s v hs hβ hpairs htriples
    refine ⟨F, N, hF, ?_, hN, fun k hk => (hin k hk).trans (le_max_left _ _)⟩
    have : (s.card : ℝ) ≤ 4 * F.card := by linarith [Nat.cast_nonneg (α := ℝ) F.card]
    exact_mod_cast this
  · -- many nearly parallel pairs
    push Not at hpairs
    have hnear : ((s.product s).filter fun ij => ‖cross (v ij.1) (v ij.2)‖ < β).card * 2 >
        s.card ^ 2 := by
      have hsplit := (s.product s).card_filter_add_card_filter_not
        (fun ij => β ≤ ‖cross (v ij.1) (v ij.2)‖)
      have hcardp : (s.product s).card = s.card * s.card := by
        rw [Finset.product_eq_sprod, Finset.card_product]
      rw [hcardp] at hsplit
      simp only [not_le] at hsplit
      have : (((s.product s).filter fun ij => β ≤ ‖cross (v ij.1) (v ij.2)‖).card : ℝ) * 2 <
          s.card ^ 2 := by linarith
      have h' : ((s.product s).filter fun ij => β ≤ ‖cross (v ij.1) (v ij.2)‖).card * 2 <
          s.card ^ 2 := by exact_mod_cast this
      nlinarith
    -- pigeonhole a row
    have hrow : ∃ i ∈ s, s.card < 2 * (s.filter fun j => ‖cross (v i) (v j)‖ < β).card := by
      by_contra hcon
      push Not at hcon
      have hsum : ((s.product s).filter fun ij => ‖cross (v ij.1) (v ij.2)‖ < β).card =
          ∑ i ∈ s, (s.filter fun j => ‖cross (v i) (v j)‖ < β).card := by
        rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.card_filter]
      have hbound : ∑ i ∈ s, 2 * (s.filter fun j => ‖cross (v i) (v j)‖ < β).card ≤
          ∑ _i ∈ s, s.card := Finset.sum_le_sum hcon
      rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, ← hsum] at hbound
      nlinarith
    obtain ⟨i, hi, hcount⟩ := hrow
    obtain ⟨N, hN, hperp⟩ := exists_unit_orthogonal (hv i hi)
    refine ⟨s.filter fun j => ‖cross (v i) (v j)‖ < β, N, Finset.filter_subset _ _, by omega,
      hN, fun k hk => ?_⟩
    have hk' := (Finset.mem_filter.1 hk).2
    exact ((abs_inner_le_norm_cross (hv i hi) hN hperp).trans hk'.le).trans (le_max_right _ _)


/-- The set of tubes whose shading contains `p`. -/
noncomputable def through {n : ℕ} (Y : Fin n → Set Space) (p : Space) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => p ∈ Y i

theorem mem_through {n : ℕ} {Y : Fin n → Set Space} {p : Space} {i : Fin n} :
    i ∈ through Y p ↔ p ∈ Y i := by
  classical
  unfold through
  simp

theorem mem_shadingAtom_through {n : ℕ} {Y : Fin n → Set Space} {p : Space}
    (hp : p ∈ ⋃ i, Y i) : p ∈ shadingAtom Y (through Y p) :=
  ⟨hp, fun i => mem_through.symm⟩

theorem incidence_eq_card_through {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    incidence Y p = ((through Y p).card : ℝ) := by
  rw [incidence_eq_ncard, ← Set.ncard_coe_finset]
  congr 2
  ext i
  simp [mem_through]

/-- **Measurable plane selection at narrow points.**  On every shading atom where at most a
hundredth of the ordered triples of directions are `θ`-transversal, a quarter of the incidences
are kept and a unit normal within `max (θ/β) β` of all kept directions is chosen.  Shadings
shrink and the normal map is measurable. -/
theorem narrow_atom_selection {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i)) {θ β : ℝ} (hθ : 0 < θ) (hβ : 0 < β) :
    ∃ (Z : Fin n → Set Space) (P : Space → Space),
      (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet (Z i)) ∧ Measurable P ∧
      (∀ p ∈ ⋃ i, Z i, ‖P p‖ = 1) ∧
      (∀ i p, p ∈ Z i → |inner ℝ (v i) (P p)| ≤ max (θ / β) β) ∧
      (∀ p, 100 * transCount (through Y p) v θ ≤ (through Y p).card ^ 3 →
        incidence Y p ≤ 4 * incidence Z p) := by
  classical
  have hsel : ∀ s : Finset (Fin n), ∃ (F : Finset (Fin n)) (N : Space),
      F ⊆ s ∧ (¬((shadingAtom Y s).Nonempty ∧ 100 * transCount s v θ ≤ s.card ^ 3) → F = ∅) ∧
      (((shadingAtom Y s).Nonempty ∧ 100 * transCount s v θ ≤ s.card ^ 3) →
        s.card ≤ 4 * F.card ∧ ‖N‖ = 1 ∧ ∀ k ∈ F, |inner ℝ (v k) N| ≤ max (θ / β) β) := by
    intro s
    by_cases hs : (shadingAtom Y s).Nonempty ∧ 100 * transCount s v θ ≤ s.card ^ 3
    · have hsn : s.Nonempty := by
        obtain ⟨p, hp⟩ := hs.1
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1
        exact ⟨i, (hp.2 i).mp hi⟩
      obtain ⟨F, N, hF, hcard, hN, hinner⟩ :=
        plane_selection_narrow s v (fun i _ => hv i) hsn hθ hβ hs.2
      exact ⟨F, N, hF, fun h => (h hs).elim, fun _ => ⟨hcard, hN, hinner⟩⟩
    · exact ⟨∅, 0, Finset.empty_subset _, fun _ => rfl, fun h => (hs h).elim⟩
  choose F N hFs hF0 hprops using hsel
  let Z : Fin n → Set Space := fun i =>
    ⋃ s : Finset (Fin n), if i ∈ F s then shadingAtom Y s else ∅
  let P : Space → Space := fun p =>
    ∑ s : Finset (Fin n), (shadingAtom Y s).indicator (fun _ => N s) p
  have hP : Measurable P := Finset.measurable_sum _ fun s _ =>
    measurable_const.indicator (measurableSet_shadingAtom hY s)
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i p hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    split_ifs at hs with hi
    · exact (hs.2 i).mpr (hFs s hi)
    · exact hs.elim
  have hZm : ∀ i, MeasurableSet (Z i) := by
    intro i
    apply MeasurableSet.iUnion
    intro s
    split_ifs
    · exact measurableSet_shadingAtom hY s
    · exact MeasurableSet.empty
  have hZatom : ∀ {s : Finset (Fin n)} {p : Space}, p ∈ shadingAtom Y s →
      ∀ i, p ∈ Z i ↔ i ∈ F s := by
    intro s p hp i
    constructor
    · intro hpi
      obtain ⟨t, ht⟩ := mem_iUnion.mp hpi
      split_ifs at ht with hit
      · have hts := shadingAtom_eq_of_mem ht hp
        simpa only [hts] using hit
      · exact ht.elim
    · intro hi
      exact mem_iUnion.mpr ⟨s, by simpa only [ite_eq_left hi] using hp⟩
  have hPatom : ∀ {s : Finset (Fin n)} {p : Space}, p ∈ shadingAtom Y s → P p = N s := by
    intro s p hp
    dsimp [P]
    rw [Finset.sum_eq_single s]
    · exact Set.indicator_of_mem hp _
    · intro t _ hts
      apply Set.indicator_of_notMem
      intro ht
      exact hts (shadingAtom_eq_of_mem ht hp)
    · simp
  have hnarrowOf : ∀ {s : Finset (Fin n)} {i : Fin n}, i ∈ F s →
      (shadingAtom Y s).Nonempty ∧ 100 * transCount s v θ ≤ s.card ^ 3 := by
    intro s i hi
    by_contra hcon
    rw [hF0 s hcon] at hi
    exact Finset.notMem_empty i hi
  refine ⟨Z, P, hZY, hZm, hP, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    obtain ⟨s, hs⟩ := exists_shadingAtom Y (mem_iUnion.mpr ⟨i, hZY i hi⟩)
    rw [hPatom hs]
    exact (hprops s (hnarrowOf ((hZatom hs i).mp hi))).2.1
  · intro i p hp
    obtain ⟨s, hs⟩ := exists_shadingAtom Y (mem_iUnion.mpr ⟨i, hZY i hp⟩)
    rw [hPatom hs]
    have hi := (hZatom hs i).mp hp
    exact (hprops s (hnarrowOf hi)).2.2 i hi
  · intro p hnar
    by_cases hp : p ∈ ⋃ i, Y i
    · have hs := mem_shadingAtom_through hp
      have hYcard := incidence_eq_card_through Y p
      have hZcard : incidence Z p = ((F (through Y p)).card : ℝ) := by
        rw [incidence_eq_ncard]
        have he : {i | p ∈ Z i} = (F (through Y p) : Set (Fin n)) := by
          ext i; exact hZatom hs i
        rw [he, Set.ncard_coe_finset]
      have h4 := (hprops (through Y p) ⟨⟨p, hs⟩, hnar⟩).1
      rw [hYcard, hZcard]
      exact_mod_cast h4
    · rw [incidence_eq_zero_of_notMem Y hp]
      exact mul_nonneg (by norm_num) (incidence_nonneg Z p)


/-- The broad points: those whose atom has more than a hundredth of transversal triples. -/
def broadSet {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (θ : ℝ) : Set Space :=
  {p | (through Y p).card ^ 3 < 100 * transCount (through Y p) v θ}

theorem broadSet_eq {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (θ : ℝ) :
    broadSet Y v θ = ⋃ s ∈ (Finset.univ.filter fun s : Finset (Fin n) =>
      s.card ^ 3 < 100 * transCount s v θ), shadingAtom Y s := by
  classical
  ext p
  simp only [broadSet, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion,
    exists_prop]
  constructor
  · intro hp
    have hp' : p ∈ ⋃ i, Y i := by
      by_contra hn
      have h0 : through Y p = ∅ := by
        ext i; simp only [mem_through, Finset.notMem_empty, iff_false]
        exact fun hi => hn (mem_iUnion.2 ⟨i, hi⟩)
      rw [h0] at hp
      simp [transCount] at hp
    exact ⟨through Y p, hp, mem_shadingAtom_through hp'⟩
  · rintro ⟨s, hs, hps⟩
    have : through Y p = s := by
      ext i; rw [mem_through]; exact hps.2 i
    rwa [this]

theorem measurableSet_broadSet {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    (v : Fin n → Space) (θ : ℝ) : MeasurableSet (broadSet Y v θ) := by
  rw [broadSet_eq]
  exact Finset.measurableSet_biUnion _ fun s _ => measurableSet_shadingAtom hY s

theorem broadSet_subset {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (θ : ℝ) :
    broadSet Y v θ ⊆ ⋃ i, Y i := by
  classical
  intro p hp
  rw [broadSet_eq] at hp
  simp only [mem_iUnion, exists_prop] at hp
  obtain ⟨s, _, hps⟩ := hp
  exact hps.1

/-- At a point, the shading-transversal triples are dominated by the tube-transversal triples. -/
theorem transCount_le_tubes {n : ℕ} {Y : Fin n → Set Space} {x v : Fin n → Space} {δ θ : ℝ}
    (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i)) (p : Space) :
    (transCount (through Y p) v θ : ℝ≥0∞) ≤ ∑ i, ∑ j, ∑ k,
      if θ ≤ |MK.det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
        (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
          (tube δ (x k) (v k)).indicator 1 p
      else 0 := by
  classical
  set s := through Y p with hs
  have e : (transCount s v θ : ℝ≥0∞) = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s,
      if θ ≤ |inner ℝ (v k) (cross (v i) (v j))| then (1 : ℝ≥0∞) else 0 := by
    unfold transCount
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [e]
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s,
        (if θ ≤ |inner ℝ (v k) (cross (v i) (v j))| then (1 : ℝ≥0∞) else 0)
      ≤ ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s,
        (if θ ≤ |MK.det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
          (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
            (tube δ (x k) (v k)).indicator 1 p
        else 0) := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun k hk => ?_
        rw [hs, mem_through] at hi hj hk
        rw [inner_cross_eq_det3]
        split_ifs
        · rw [indicator_of_mem (hYT i hi), indicator_of_mem (hYT j hj),
            indicator_of_mem (hYT k hk)]
          simp
        · exact le_rfl
    _ ≤ ∑ i ∈ s, ∑ j, ∑ k,
        (if θ ≤ |MK.det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
          (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
            (tube δ (x k) (v k)).indicator 1 p
        else 0) :=
        Finset.sum_le_sum fun i _ => (Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
            (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)


/-- Volume of the broad set (Markov's inequality with `trilinear_kakeya`). -/
theorem volume_broadSet_le (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ θ δ μlo : ℝ, 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 → 0 < μlo →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) → (⋃ i, Y i) ⊆ ball 0 1 →
      (∀ p ∈ ⋃ i, Y i, μlo ≤ incidence Y p) →
      ENNReal.ofReal (μlo ^ (3/2:ℝ) / 10) * volume (broadSet Y v θ) ≤
        ENNReal.ofReal (C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ)) := by
  obtain ⟨C, hC, hK⟩ := MK.trilinear_kakeya ε hε
  refine ⟨C, hC, ?_⟩
  intro θ δ μlo hθ hθ1 hδ hδ1 hμ n x v Y hv hY hYT hball hlo
  have key := hK θ δ hθ hθ1 hδ hδ1 n x v hv
  set f : Space → ℝ≥0∞ := fun p => (∑ i, ∑ j, ∑ k,
      if θ ≤ |MK.det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
        (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
          (tube δ (x k) (v k)).indicator 1 p
      else 0) ^ (1/2:ℝ) with hf
  have hfm : Measurable f := by
    refine Measurable.pow_const ?_ _
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => ?_
    split_ifs
    · exact ((measurable_one.indicator (isOpen_thickening.measurableSet)).mul
        (measurable_one.indicator (isOpen_thickening.measurableSet))).mul
        (measurable_one.indicator (isOpen_thickening.measurableSet))
    · exact measurable_const
  -- on the broad set the integrand is large
  have hlarge : ∀ p ∈ broadSet Y v θ, ENNReal.ofReal (μlo ^ (3/2:ℝ) / 10) ≤ f p := by
    intro p hp
    have hpY := broadSet_subset Y v θ hp
    have hcard : μlo ≤ ((through Y p).card : ℝ) := by
      rw [← incidence_eq_card_through]; exact hlo p hpY
    have hbr : ((through Y p).card : ℝ) ^ 3 < 100 * transCount (through Y p) v θ := by
      have := hp; simp only [broadSet, mem_ofPred_eq] at this; exact_mod_cast this
    have hdom := transCount_le_tubes (θ := θ) hYT p
    have h1 : μlo ^ 3 / 100 ≤ (transCount (through Y p) v θ : ℝ) := by
      have : μlo ^ 3 ≤ ((through Y p).card : ℝ) ^ 3 := pow_le_pow_left₀ hμ.le hcard 3
      linarith
    rw [hf]
    have e100 : ((100 : ℝ)) ^ (1/2:ℝ) = 10 := by
      rw [show (100 : ℝ) = 10 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have e3 : (μlo ^ 3) ^ (1/2:ℝ) = μlo ^ (3/2:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
      norm_num
    calc ENNReal.ofReal (μlo ^ (3/2:ℝ) / 10) = ENNReal.ofReal (μlo ^ 3 / 100) ^ (1/2:ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            Real.div_rpow (by positivity) (by norm_num), e100, e3]
      _ ≤ (transCount (through Y p) v θ : ℝ≥0∞) ^ (1/2:ℝ) := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal h1
      _ ≤ _ := ENNReal.rpow_le_rpow hdom (by norm_num)
  have hBm := measurableSet_broadSet hY v θ
  have hBball : broadSet Y v θ ⊆ ball 0 1 := (broadSet_subset Y v θ).trans hball
  calc ENNReal.ofReal (μlo ^ (3/2:ℝ) / 10) * volume (broadSet Y v θ)
      = ∫⁻ p in broadSet Y v θ, ENNReal.ofReal (μlo ^ (3/2:ℝ) / 10) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ p in broadSet Y v θ, f p := setLIntegral_mono hfm hlarge
    _ ≤ ∫⁻ p in ball 0 1, f p := lintegral_mono_set hBball
    _ ≤ _ := key

/-- **Weak plane map** (sticky Lemma 4.3, without robust transversality).  If the shadings have
pointwise multiplicity in `[μlo, μhi]` and the broad points carry little mass (numeric
hypothesis), then a refinement keeping an eighth of the mass has a measurable unit normal map
within `max (θ/β) β` of every kept direction. -/
theorem weak_plane_map (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ θ β δ μlo μhi : ℝ, 0 < θ → θ ≤ 1 → 0 < β → 0 < δ → δ ≤ 1 → 0 < μlo →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) → (⋃ i, Y i) ⊆ ball 0 1 →
      (∀ p ∈ ⋃ i, Y i, μlo ≤ incidence Y p ∧ incidence Y p ≤ μhi) →
      20 * C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) * μhi ≤
        μlo ^ (3/2:ℝ) * shadingMass Y →
      ∃ (Z : Fin n → Set Space) (P : Space → Space),
        (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet (Z i)) ∧ shadingMass Y / 8 ≤ shadingMass Z ∧
        Measurable P ∧ (∀ p ∈ ⋃ i, Z i, ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Z i → |inner ℝ (v i) (P p)| ≤ max (θ / β) β) := by
  obtain ⟨C, hC, hvol⟩ := volume_broadSet_le ε hε
  refine ⟨C, hC, ?_⟩
  intro θ β δ μlo μhi hθ hθ1 hβ hδ hδ1 hμ n x v Y hv hY hYT hball hbnd hnum
  obtain ⟨Z, P, hZY, hZm, hPm, hPn, hPi, hinc⟩ := narrow_atom_selection Y v hv hY hθ hβ
  refine ⟨Z, P, hZY, hZm, ?_, hPm, hPn, hPi⟩
  have hYfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((subset_iUnion Y i).trans hball))
  have hZfin : ∀ i, volume (Z i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hZY i))
  have hZ0 : 0 ≤ shadingMass Z :=
    Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  by_cases hne : (⋃ i, Y i).Nonempty
  swap
  · have hmass0 : shadingMass Y = 0 := by
      rw [shadingMass]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : Y i = ∅ := by
        by_contra h
        exact hne ((Set.nonempty_iff_ne_empty.2 h).mono (subset_iUnion Y i))
      simp [this]
    rw [hmass0, zero_div]; exact hZ0
  obtain ⟨p₀, hp₀⟩ := hne
  have hμhi : 0 < μhi := lt_of_lt_of_le hμ ((hbnd p₀ hp₀).1.trans (hbnd p₀ hp₀).2)
  set B := broadSet Y v θ with hB
  have hBm : MeasurableSet B := measurableSet_broadSet hY v θ
  have hBfin : volume B ≠ ∞ := ne_top_of_le_ne_top measure_ball_lt_top.ne
    (measure_mono ((broadSet_subset Y v θ).trans hball))
  -- pointwise inequality
  have hpt : ∀ p, incidence Y p ≤ 4 * incidence Z p + B.indicator (fun _ => μhi) p := by
    intro p
    by_cases hpB : p ∈ B
    · rw [indicator_of_mem hpB]
      have hpY := broadSet_subset Y v θ hpB
      have := (hbnd p hpY).2
      have := incidence_nonneg Z p
      linarith
    · rw [indicator_of_notMem hpB, add_zero]
      apply hinc p
      simp only [hB, broadSet, mem_ofPred_eq, not_lt] at hpB
      exact hpB
  -- integrate
  have hBint : Integrable (B.indicator fun _ => μhi) :=
    (integrableOn_const (C := μhi) hBfin).integrable_indicator hBm
  have hint : shadingMass Y ≤ 4 * shadingMass Z + μhi * (volume B).toReal := by
    have h1 := integral_mono (integrable_incidence hY hYfin)
      (((integrable_incidence hZm hZfin).const_mul 4).add hBint) hpt
    simp only [Pi.add_apply] at h1
    rw [integral_incidence hY hYfin, integral_add ((integrable_incidence hZm hZfin).const_mul 4)
      hBint, integral_const_mul, integral_incidence hZm hZfin, integral_indicator hBm,
      setIntegral_const, smul_eq_mul] at h1
    rw [Measure.real] at h1
    linarith [mul_comm μhi (volume B).toReal]
  -- the broad set is small
  have hv := hvol θ δ μlo hθ hθ1 hδ hδ1 hμ n x v Y hv hY hYT hball (fun p hp => (hbnd p hp).1)
  have hA : 0 < μlo ^ (3/2:ℝ) / 10 := by positivity
  have hvR : μlo ^ (3/2:ℝ) / 10 * (volume B).toReal ≤
      C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le, ENNReal.toReal_ofReal (by positivity)]
      at this
  have hsmall : μhi * (volume B).toReal ≤ shadingMass Y / 2 := by
    have hmu : 0 < μlo ^ (3/2:ℝ) := by positivity
    have hB0 : 0 ≤ (volume B).toReal := ENNReal.toReal_nonneg
    have h2 : μlo ^ (3/2:ℝ) * (μhi * (volume B).toReal) ≤
        10 * C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) * μhi := by
      nlinarith
    have h3 : μlo ^ (3/2:ℝ) * (μhi * (volume B).toReal) ≤ μlo ^ (3/2:ℝ) * (shadingMass Y / 2) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hmu
  linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
