-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ParentContributors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalPrismGeometry

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file ParentContributors.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory

def LongPrism (a b L : ℝ) (c e₁ e₂ e₃ : Space) : Set Space :=
  {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b ∧
    |inner ℝ e₃ (y - c)| ≤ L}

lemma long_prism_volume {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    volume (LongPrism a b L c e₁ e₂ e₃) = ENNReal.ofReal (8 * a * b * L) := by
  obtain ⟨B, h₁, h₂, h₃⟩ := basis_of_frame he
  let d : Fin 3 → ℝ := ![a, b, L]
  have hset : LongPrism a b L c e₁ e₂ e₃ =
      {y : Space | ∀ i, -d i ≤ B.repr (y - c) i ∧ B.repr (y - c) i ≤ d i} := by
    ext y
    simp only [LongPrism, mem_ofPred_eq, OrthonormalBasis.repr_apply_apply]
    constructor
    · rintro ⟨h₁', h₂', h₃'⟩ i
      fin_cases i
      · simpa [d, h₁] using abs_le.mp h₁'
      · simpa [d, h₂] using abs_le.mp h₂'
      · simpa [d, h₃] using abs_le.mp h₃'
    · intro h
      exact ⟨by simpa [d, h₁] using abs_le.mpr (h 0),
        by simpa [d, h₂] using abs_le.mpr (h 1), by simpa [d, h₃] using abs_le.mpr (h 2)⟩
  rw [hset, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  simp only [Fin.prod_univ_three]
  change ENNReal.ofReal (a - -a) * ENNReal.ofReal (b - -b) * ENNReal.ofReal (L - -L) = _
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma UnorientedNear.projection_bound {r : ℝ} {v w e : Space}
    (h : UnorientedNear r v w) (he : ‖e‖ = 1) :
    |inner ℝ e w| ≤ |inner ℝ e v| + r := by
  rcases h.symm with h | h
  · have hprox : |inner ℝ e (w - v)| ≤ r :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [he, one_mul] using h)
    have heq : inner ℝ e w = inner ℝ e (w - v) + inner ℝ e v := by
      simp only [inner_sub_right]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  · have hprox : |inner ℝ e (w + v)| ≤ r :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [he, one_mul] using h)
    have heq : inner ℝ e w = inner ℝ e (w + v) - inner ℝ e v := by
      simp only [inner_add_right]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)

lemma tube_projection_about_center_refined {δ : ℝ} {x v e y : Space}
    (he : ‖e‖ = 1) (hy : y ∈ Tube δ x v) :
    |inner ℝ e (y - center x v)| < δ + (1 / 2 : ℝ) * |inner ℝ e v| := by
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hyz
  have hnear : |inner ℝ e (y - (x + t • v))| < δ :=
    (abs_real_inner_le_norm _ _).trans_lt (by simpa [he, ← dist_eq_norm] using hyz)
  have ht' : |t - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hhalf : |(t - 1 / 2) * inner ℝ e v| ≤ (1 / 2 : ℝ) * |inner ℝ e v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
  have hcoord : inner ℝ e (y - center x v) =
      inner ℝ e (y - (x + t • v)) + (t - 1 / 2) * inner ℝ e v := by
    simp only [center, inner_sub_right, inner_add_right, inner_smul_right]
    ring
  rw [hcoord]
  exact (abs_add_le _ _).trans_lt (by linarith)

/-- A coarse tube sharing a contained unit fine tube with a prism lies in a
controlled enlargement of that prism, including its longitudinal coordinate. -/
theorem parent_tube_in_enlarged_long_prism {δ τ a b L : ℝ}
    (hδ : 0 < δ) (hτhalf : τ ≤ 1 / 2)
    {x v z w c e₁ e₂ e₃ : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hparent : Tube δ x v ⊆ Tube τ z w)
    (hprism : Tube δ x v ⊆ LongPrism a b L c e₁ e₂ e₃) :
    Tube τ z w ⊆ LongPrism (2 * a + 5 * τ) (2 * b + 5 * τ) (L + 2) c e₁ e₂ e₃ := by
  have hn₁ : ‖e₁‖ = 1 := by simpa using he.norm_eq_one (0 : Fin 3)
  have hn₂ : ‖e₂‖ = 1 := by simpa using he.norm_eq_one (1 : Fin 3)
  have hn₃ : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  have hmid : center x v ∈ Tube δ x v := by
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨1 / 2, by norm_num, by simp [center]⟩
  have hm := hprism hmid
  have hc := (center_near_of_tube_subset hδ hv hw hparent).le
  have haxis := axes_near_of_tube_subset hδ hv hw hparent
  have hleft := hprism (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hright := hprism (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  have hdir₁ : |inner ℝ e₁ w| ≤ 2 * a + 4 * τ :=
    (haxis.projection_bound hn₁).trans (by linarith [axis_projection_of_endpoints hleft.1 hright.1])
  have hdir₂ : |inner ℝ e₂ w| ≤ 2 * b + 4 * τ :=
    (haxis.projection_bound hn₂).trans (by linarith [axis_projection_of_endpoints hleft.2.1 hright.2.1])
  have hbase (e : Space) (hne : ‖e‖ = 1) {q : ℝ}
      (hq : |inner ℝ e (center x v - c)| ≤ q) :
      |inner ℝ e (center z w - c)| ≤ q + 2 * τ := by
    have hprox : |inner ℝ e (center z w - center x v)| ≤ 2 * τ :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [hne, one_mul, norm_sub_rev] using hc)
    have heq : inner ℝ e (center z w - c) =
        inner ℝ e (center z w - center x v) + inner ℝ e (center x v - c) := by
      simp only [inner_sub_right]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  have htransverse (e : Space) (hne : ‖e‖ = 1) {q : ℝ}
      (hq : |inner ℝ e (center x v - c)| ≤ q)
      (hdir : |inner ℝ e w| ≤ 2 * q + 4 * τ) {y : Space} (hy : y ∈ Tube τ z w) :
      |inner ℝ e (y - c)| ≤ 2 * q + 5 * τ := by
    have hproj := tube_projection_about_center_refined hne hy
    have hbase' := hbase e hne hq
    have heq : inner ℝ e (y - c) =
        inner ℝ e (y - center z w) + inner ℝ e (center z w - c) := by
      simp only [inner_sub_right]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  intro y hy
  refine ⟨htransverse e₁ hn₁ hm.1 hdir₁ hy, htransverse e₂ hn₂ hm.2.1 hdir₂ hy, ?_⟩
  have hproj := tube_projection_about_center hw hn₃ hy
  have hbase' := hbase e₃ hn₃ hm.2.2
  have heq : inner ℝ e₃ (y - c) =
      inner ℝ e₃ (y - center z w) + inner ℝ e₃ (center z w - c) := by
    simp only [inner_sub_right]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

theorem parent_tube_in_long_prism {δ τ a b : ℝ}
    (hδ : 0 < δ) (hτhalf : τ ≤ 1 / 2)
    {x v z w c e₁ e₂ e₃ : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hparent : Tube δ x v ⊆ Tube τ z w)
    (hprism : Tube δ x v ⊆ Prism a b c e₁ e₂ e₃) :
    Tube τ z w ⊆ LongPrism (2 * a + 5 * τ) (2 * b + 5 * τ) 3 c e₁ e₂ e₃ := by
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    parent_tube_in_enlarged_long_prism (L := 1) hδ hτhalf hv hw he hparent hprism

/-- Only boundedly many essentially distinct coarse tubes can contribute any
fine-tube incidence to a prism whose widths are bounded by C times their radius.
This counts actual containments, including incidences introduced by recentering. -/
theorem coarse_parents_contributing_to_long_prism {n q : ℕ} {δ τ a b C L : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ C * τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    (ncard {l | ∃ i, Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
      Tube δ (x i) (v i) ⊆ LongPrism a b L c e₁ e₂ e₃} : ℝ) ≤
        64000000 * (L + 2) ^ 2 * (2 * C + 5) ^ 4 := by
  let R := (2 * C + 5) * τ
  let Q := LongPrism R R (L + 2) c e₁ e₂ e₃
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hvol : volume Q = ENNReal.ofReal (8 * R * R * (L + 2)) :=
    long_prism_volume hR hR (by positivity) c e₁ e₂ e₃ he
  have hfinite : volume Q ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hbound₁ : 2 * a + 5 * τ ≤ R := by dsimp [R]; nlinarith
  have hbound₂ : 2 * b + 5 * τ ≤ R := by dsimp [R]; nlinarith
  have hcount : ncard {l | ∃ i, Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
      Tube δ (x i) (v i) ⊆ LongPrism a b L c e₁ e₂ e₃} ≤
      contained (fun l => Tube τ (z l) (w l)) Q := by
    apply Set.ncard_le_ncard
    · rintro l ⟨i, hiparent, hiprism⟩ y hy
      have h := parent_tube_in_enlarged_long_prism hδ hτhalf (hv i) (hw l) he hiparent hiprism hy
      exact ⟨h.1.trans hbound₁, h.2.1.trans hbound₂, h.2.2⟩
    · exact Set.toFinite _
  have hp := packing_contained_in_enclosure hτ z w hw hsep Q Q hfinite (fun _ h => h)
  rw [hvol, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)] at hp
  have hpreal : (contained (fun l => Tube τ (z l) (w l)) Q : ℝ) * τ ^ 4 ≤
      1000000 * (8 * R * R * (L + 2)) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hp
  apply (mul_le_mul_iff_left₀ (pow_pos hτ 4)).mp
  calc
    _ ≤ (contained (fun l => Tube τ (z l) (w l)) Q : ℝ) * τ ^ 4 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)
    _ ≤ 1000000 * (8 * R * R * (L + 2)) ^ 2 := hpreal
    _ = (64000000 * (L + 2) ^ 2 * (2 * C + 5) ^ 4) * τ ^ 4 := by dsimp [R]; ring

theorem coarse_parents_contributing_to_prism {n q : ℕ} {δ τ a b C : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ C * τ) (hC : 0 ≤ C)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    (ncard {l | ∃ i, Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
      Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃} : ℝ) ≤
        576000000 * (2 * C + 5) ^ 4 := by
  convert coarse_parents_contributing_to_long_prism (L := 1) hδ hτ hτhalf ha hab hb hC
    zero_le_one x v hv z w hw hsep c e₁ e₂ e₃ he using 1 <;> norm_num [Prism, LongPrism]

/-- Uniform parentwise KT control passes to all true incidences in a small
prism, with only the geometric parent-contributor loss. -/
theorem parentwise_katzTao_in_prism {n q : ℕ} {δ τ a b C K : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ C * τ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (hcover : ∀ i, ∃ l, Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l))
    (hKT : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal K * volume U)
    (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    ∀ U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃ ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal ((576000000 * (2 * C + 5) ^ 4) * K) * volume U := by
  classical
  intro U hU
  let S := Finset.univ.filter fun l => ∃ i, Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
    Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃
  let N := ncard {i | Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃ ∧ Tube δ (x i) (v i) ⊆ U}
  let F (l : Fin q) := ncard {i | Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
    Tube δ (x i) (v i) ⊆ U}
  have hS : (S.card : ℝ) ≤ 576000000 * (2 * C + 5) ^ 4 := by
    have hh := coarse_parents_contributing_to_prism hδ hτ hτhalf ha hab hb hC
      x v hv z w hw hsep c e₁ e₂ e₃ he
    rw [WangZahlLot.Obl.wz_concentrated_convex_factorization.ncard_fintype] at hh
    convert hh using 1
    congr 2
    ext l
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount : N ≤ ∑ l ∈ S, F l := by
    have hsub : {i | Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃ ∧ Tube δ (x i) (v i) ⊆ U} ⊆
        ⋃ l ∈ S, {i | Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧ Tube δ (x i) (v i) ⊆ U} := by
      intro i hi
      obtain ⟨l, hl⟩ := hcover i
      exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hl, hi.1⟩, hl, hi.2⟩⟩
    exact (Set.ncard_le_ncard hsub).trans (S.set_ncard_biUnion_le _)
  have hcount' : (N : ENNReal) ≤ ∑ l ∈ S, (F l : ENNReal) := by exact_mod_cast hcount
  change ENNReal.ofReal ((N : ℝ) * δ ^ 2) ≤ _
  calc
    _ = (N : ENNReal) * ENNReal.ofReal (δ ^ 2) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ (∑ l ∈ S, (F l : ENNReal)) * ENNReal.ofReal (δ ^ 2) := mul_le_mul' hcount' le_rfl
    _ = ∑ l ∈ S, (F l : ENNReal) * ENNReal.ofReal (δ ^ 2) := Finset.sum_mul _ _ _
    _ ≤ ∑ _l ∈ S, ENNReal.ofReal K * volume U := by
      apply Finset.sum_le_sum
      intro l hl
      simpa only [F, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hKT l U hU
    _ = (S.card : ENNReal) * (ENNReal.ofReal K * volume U) := by simp
    _ = ENNReal.ofReal ((S.card : ℝ) * K) * volume U := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hS hK)) le_rfl

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
