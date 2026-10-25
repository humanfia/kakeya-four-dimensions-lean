-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranch.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.NetCover
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Regularize

/-!
# Towards the sticky branch of a repaired trichotomy

For a canonical family (no antipodal directions), radii `ρ_k = ρ₀ L^k` (integer `L`, so the
grids of size `ρ_k / 20` are nested):

* `common_classes`: a subfamily whose members share, at every level, the residue class mod
  `200000` of their (foot, direction) cell;
* `cell_cover`: for such a set, the net of representatives of its cells at one level is an exact
  cover (unit, half-overlap, `∃!`, used), and the tubes inside a net tube are exactly the
  members of its cell;
* `lineCell_nest`: equal cells at a finer level are equal at every coarser level.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- Pigeonhole: a subfamily on which a key with values in `t` is constant. -/
theorem constant_key_refine {ι β : Type*} [DecidableEq ι] [DecidableEq β] (U : Finset ι)
    (hU : U.Nonempty) (key : ι → β) (t : Finset β) (ht : ∀ i ∈ U, key i ∈ t) :
    ∃ S ⊆ U, S.Nonempty ∧ (U.card : ℝ) ≤ t.card * S.card ∧
      ∀ i ∈ S, ∀ i' ∈ S, key i = key i' := by
  classical
  have htne : t.Nonempty := by
    obtain ⟨i, hi⟩ := hU
    exact ⟨key i, ht i hi⟩
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast Finset.card_pos.2 htne
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to ht htne
    (b := (U.card : ℝ) / t.card) (by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ htpos.ne'])
  refine ⟨U.filter (fun i => key i = y), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.2 hU
    have : (0 : ℝ) < (U.card : ℝ) / t.card := div_pos hUpos htpos
    exact_mod_cast lt_of_lt_of_le this hy
  · rw [div_le_iff₀ htpos] at hy
    linarith
  · intro i hi i' hi'
    rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hi').2]

/-- The residue class mod `M` of the cell of a tube at radius `ρ`. -/
noncomputable def classKey (M : ℕ) (ρ : ℝ) (x v : Sp) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (fun c => (lineCell (ρ / 20) x v).1 c % (M : ℤ), fun c => (lineCell (ρ / 20) x v).2 c % (M : ℤ))

/-- The set of possible residue classes, of size `M⁶`. -/
lemma classKey_mem {M : ℕ} (hM : 0 < M) (ρ : ℝ) (x v : Sp) :
    classKey M ρ x v ∈ (Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) M) ×ˢ
      (Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) M) := by
  have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
  have hmem : ∀ k : ℤ, k % (M : ℤ) ∈ Finset.Ico (0 : ℤ) M := by
    intro k
    rw [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ hM0.ne', Int.emod_lt_of_pos _ hM0⟩
  rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  exact ⟨fun c => hmem _, fun c => hmem _⟩

lemma card_classes (M : ℕ) :
    (((Fintype.piFinset fun _ : Fin 3 => Finset.Ico (0 : ℤ) M) ×ˢ
      (Fintype.piFinset fun _ : Fin 3 => Finset.Ico (0 : ℤ) M)).card : ℝ) = (M : ℝ) ^ 6 := by
  rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Int.card_Ico, sub_zero]
  push_cast
  rw [Int.toNat_natCast]
  ring

/-- Common residue classes at all levels: a subfamily whose members share the class key at
every radius `ρs k`, `k < N`. -/
theorem common_classes {n : ℕ} (x v : Fin n → Sp) {M : ℕ} (hM : 0 < M) (ρs : ℕ → ℝ) :
    ∀ (N : ℕ) (U : Finset (Fin n)), U.Nonempty →
      ∃ S ⊆ U, S.Nonempty ∧ (U.card : ℝ) ≤ ((M : ℝ) ^ 6) ^ N * S.card ∧
        ∀ k < N, ∀ i ∈ S, ∀ i' ∈ S,
          classKey M (ρs k) (x i) (v i) = classKey M (ρs k) (x i') (v i') := by
  intro N
  induction N with
  | zero =>
    intro U hU
    exact ⟨U, subset_rfl, hU, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    intro U hU
    obtain ⟨S₁, hS₁U, hS₁ne, hS₁card, hS₁cls⟩ := ih U hU
    obtain ⟨S₂, hS₂S₁, hS₂ne, hS₂card, hS₂cls⟩ := constant_key_refine S₁ hS₁ne
      (fun i => classKey M (ρs N) (x i) (v i)) _ (fun i _ => classKey_mem hM (ρs N) (x i) (v i))
    refine ⟨S₂, hS₂S₁.trans hS₁U, hS₂ne, ?_, fun k hk i hi i' hi' => ?_⟩
    · rw [card_classes] at hS₂card
      calc (U.card : ℝ) ≤ ((M : ℝ) ^ 6) ^ N * S₁.card := hS₁card
        _ ≤ ((M : ℝ) ^ 6) ^ N * ((M : ℝ) ^ 6 * S₂.card) := by gcongr
        _ = ((M : ℝ) ^ 6) ^ (N + 1) * S₂.card := by ring
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact hS₁cls k hk' i (hS₂S₁ hi) i' (hS₂S₁ hi')
      · exact hS₂cls i hi i' hi'

/-- Nesting of grids: equal cells at size `s` are equal at size `m s` (`m` a natural number). -/
lemma cellIdx_nest {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) {y y' : Sp}
    (h : cellIdx s y = cellIdx s y') : cellIdx ((m : ℝ) * s) y = cellIdx ((m : ℝ) * s) y' := by
  funext c
  have hc := congrFun h c
  unfold cellIdx at hc ⊢
  have e : ∀ a : ℝ, a / ((m : ℝ) * s) = (a / s) / (m : ℝ) := by
    intro a; field_simp
  rw [e, e, Int.floor_div_natCast, Int.floor_div_natCast, hc]

lemma lineCell_nest {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) {x v x' v' : Sp}
    (h : lineCell s x v = lineCell s x' v') :
    lineCell ((m : ℝ) * s) x v = lineCell ((m : ℝ) * s) x' v' := by
  unfold lineCell at h ⊢
  rw [cellIdx_nest hs hm (congrArg Prod.fst h), cellIdx_nest hs hm (congrArg Prod.snd h)]

/-- The exact cover of a set with a common class at radius `ρ`, built from the cells of the
set: unit directions, pairwise half-overlap, every tube of `S` in exactly one net tube, every net
tube used, and the tubes of `S` inside a net tube are exactly the members of its cell. -/
theorem cell_cover {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcls : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i')) :
    ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → MeasureTheory.volume
          (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩
            Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤
          (1 / 2 : ENNReal) *
            MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧
      (∀ i ∈ S, ∃! j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
      (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
      (∀ j, ∃ i₀ ∈ S, z j = x i₀ ∧ w j = v i₀ ∧
          ∀ i ∈ S, (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ↔
            lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₀) (v i₀))) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set s : ℝ := ρ / 20 with hsdef
  have hs : 0 < s := by positivity
  set C := S.image (fun i => lineCell s (x i) (v i)) with hCdef
  have hrep : ∀ κ ∈ C, ∃ i ∈ S, lineCell s (x i) (v i) = κ := fun κ hκ => by
    simpa [hCdef] using hκ
  let rep : C → Fin n := fun κ => (hrep κ.1 κ.2).choose
  have hrepS : ∀ κ : C, rep κ ∈ S := fun κ => (hrep κ.1 κ.2).choose_spec.1
  have hrepcell : ∀ κ : C, lineCell s (x (rep κ)) (v (rep κ)) = κ.1 :=
    fun κ => (hrep κ.1 κ.2).choose_spec.2
  let e : C ≃ Fin C.card := C.equivFin
  have hCpos : 0 < C.card := by
    rw [Finset.card_pos]; exact hS.image _
  set z : Fin C.card → Sp := fun j => x (rep (e.symm j)) with hzdef
  set w : Fin C.card → Sp := fun j => v (rep (e.symm j)) with hwdef
  -- separation of the net
  have hsep : NetSeparated ρ z w := by
    intro j j' hjj'
    have hne : lineCell s (x (rep (e.symm j))) (v (rep (e.symm j))) ≠
        lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j'))) := by
      rw [hrepcell, hrepcell]
      intro h
      exact hjj' (e.symm.injective (Subtype.ext h))
    have hkey := hcls _ (hrepS (e.symm j)) _ (hrepS (e.symm j'))
    have hc1 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).1 c % ((200000 : ℕ) : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).1 c % ((200000 : ℕ) : ℤ) :=
      fun c => congrFun (congrArg Prod.fst hkey) c
    have hc2 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).2 c % ((200000 : ℕ) : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).2 c % ((200000 : ℕ) : ℤ) :=
      fun c => congrFun (congrArg Prod.snd hkey) c
    exact separated_of_same_class hδ hρ0 hρ (le_refl _) (hv _) (hv _) (hT _) (hT _)
      (hcan _) (hcan _) (hanti _ _) hc1 hc2 hne
  -- containment in the net tube of the own cell
  let own : ∀ i, i ∈ S → Fin C.card := fun i hi =>
    e ⟨_, Finset.mem_image_of_mem (fun i => lineCell s (x i) (v i)) hi⟩
  have hown : ∀ i (hi : i ∈ S), Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z (own i hi)) (z (own i hi) + w (own i hi))) := by
    intro i hi
    simp only [hzdef, hwdef, own, Equiv.symm_apply_apply]
    apply subset_of_same_cell hδ hs (by rw [hsdef]; linarith) (hv i) (hv _) (hT i) (hT _)
      (hcan i) (hcan _)
    rw [hrepcell]
  -- uniqueness
  have huniq : ∀ i ∈ S, ∀ j j₀, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j) (z j + w j)) →
      Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j₀) (z j₀ + w j₀)) → j = j₀ := by
    intro i hi j j₀ hj hj₀
    by_contra hne
    rcases hsep j j₀ hne with htr | hfar
    · have h1 := direction_near_of_subset hδ (hv i) (hv _) hj
      have h2 := direction_near_of_subset hδ (hv i) (hv _) hj₀
      have := min_dir_triangle (v := v i) (w := w j) (w' := w j₀)
      linarith
    · obtain ⟨⟨θ1, h01, h11, hd1⟩, -⟩ := endpoints_near_of_subset hδ hj
      obtain ⟨⟨θ2, h02, h12, hd2⟩, -⟩ := endpoints_near_of_subset hδ hj₀
      have := hfar (z j + θ1 • w j) (mem_segment_add_iff.2 ⟨θ1, h01, h11, rfl⟩)
        (z j₀ + θ2 • w j₀) (mem_segment_add_iff.2 ⟨θ2, h02, h12, rfl⟩)
      have := dist_triangle_left (z j + θ1 • w j) (z j₀ + θ2 • w j₀) (x i)
      linarith
  refine ⟨C.card, hCpos, z, w, fun j => hv _, fun j j' hjj' => ?_, fun i hi => ?_,
    fun j => ?_, fun j => ?_⟩
  · rcases hsep j j' hjj' with htr | hfar
    · exact half_overlap_of_transverse hρ0 (by linarith) (hv _) (hv _) htr
    · exact half_overlap_of_far hfar
  · exact ⟨_, hown i hi, fun j hj => huniq i hi j _ hj (hown i hi)⟩
  · refine ⟨rep (e.symm j), hrepS _, ?_⟩
    exact Metric.thickening_mono (by linarith) _
  · refine ⟨rep (e.symm j), hrepS _, rfl, rfl, fun i hi => ⟨fun hsub => ?_, fun hcell => ?_⟩⟩
    · -- inside the net tube `j` means: `j` is the own net tube, i.e. the same cell
      have hjj := huniq i hi j _ hsub (hown i hi)
      have : e.symm j = ⟨_, Finset.mem_image_of_mem (fun i => lineCell s (x i) (v i)) hi⟩ := by
        rw [hjj]; simp only [own, Equiv.symm_apply_apply]
      rw [hrepcell (e.symm j), this]
    · simp only [hzdef, hwdef]
      apply subset_of_same_cell hδ hs (by rw [hsdef]; linarith) (hv i) (hv _) (hT i) (hT _)
        (hcan i) (hcan _)
      exact hcell

/-! ### Packaging: the all-scales condition of the frozen `S` -/

/-- The all-scales condition of the frozen `S` (o015's premise `A`, error `ξ`), for a family
`(y, u)` of `m` tubes. -/
def AllScales (ξ δ : ℝ) {m : ℕ} (y u : Fin m → Sp) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-ξ) * ρ₀ ∧
    ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧
    (∀ j j', j ≠ j' → MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩
        Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤
        (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧
    (∀ i, ∃! j, Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
        Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
    (∀ j, ∃ i, Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
        Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
    (∀ j j', (Set.ncard {i | Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
        Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℝ) ≤
        δ ^ (-ξ) * (Set.ncard {i | Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
          Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))} : ℝ)) ∧
    (∀ j, ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∧
          Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆ W} : ℝ) * ρ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-ξ) * (Set.ncard {i | Metric.thickening δ (segment ℝ (y i) (y i + u i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℝ)) * MeasureTheory.volume W)

/-- Counting along an enumeration of a finset. -/
lemma ncard_enum {n : ℕ} (S : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    Set.ncard {j : Fin S.card | P (S.equivFin.symm j).1} = (S.filter P).card := by
  classical
  have himg : (fun j : Fin S.card => (S.equivFin.symm j).1) '' {j | P (S.equivFin.symm j).1} =
      ↑(S.filter P) := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(S.equivFin.symm j).2, hj⟩
    · rintro ⟨hi, hP⟩
      exact ⟨S.equivFin ⟨i, hi⟩, by simpa using hP, by simp⟩
  have hinj : Function.Injective (fun j : Fin S.card => (S.equivFin.symm j).1) := by
    intro j j' h
    exact S.equivFin.symm.injective (Subtype.ext h)
  rw [← Set.ncard_image_of_injective _ hinj, himg, Set.ncard_coe_finset]

/-- The unit tube around the centred segment in direction `w` contains `B(0,1)`. -/
lemma ball_subset_unit_tube {w : Sp} :
    Metric.ball (0 : Sp) 1 ⊆ Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w)
      (-(1 / 2 : ℝ) • w + w)) := by
  intro p hp
  refine Metric.mem_thickening_iff.2 ⟨0, ?_, ?_⟩
  · refine mem_segment_add_iff.2 ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    module
  · simpa [dist_zero_right, mem_ball_zero_iff] using hp

/-- The sticky branch, packaged. For a canonical family without antipodal directions and radii
`ρ_k = 2δ L^k` (`k < N`) climbing from `2δ` to at least `δ^ξ` (and at most `1/10000`) with ratio
`L ≤ δ^(-ξ)`, every nonempty `U` contains a subfamily `g` with
`|U| ≤ (200000⁶)^N (log₂|U| + 1)^N m` such that: if the members of each grid cell are
`δ^(-ξ)`-Frostman at the radius of the cell, and the subfamily is `δ^(-ξ)`-Frostman, then the
subfamily satisfies the all-scales condition of the frozen `S` with error `ξ`. -/
theorem sticky_branch {δ ξ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ) {L N : ℕ} (hL : 2 ≤ L)
    (hN : 0 < N) (hratio : (L : ℝ) ≤ δ ^ (-ξ)) (htwo : (2 : ℝ) ≤ δ ^ (-ξ))
    (htop1 : 2 * δ * (L : ℝ) ^ (N - 1) ≤ 1 / 10000)
    (htop2 : δ ^ ξ ≤ 2 * δ * (L : ℝ) ^ (N - 1))
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ (m : ℕ) (g : Fin m → Fin n), 0 < m ∧ Function.Injective g ∧ (∀ j, g j ∈ U) ∧
      (U.card : ℝ) ≤ (((200000 : ℕ) : ℝ) ^ 6) ^ N * ((Nat.log 2 U.card : ℝ) + 1) ^ N * m ∧
      ((∀ k < N, ∀ j₀ : Fin m, ∀ W : Set Sp, Convex ℝ W →
          ENNReal.ofReal ((Set.ncard {j | lineCell (2 * δ * (L : ℝ) ^ k / 20) (x (g j)) (v (g j)) =
              lineCell (2 * δ * (L : ℝ) ^ k / 20) (x (g j₀)) (v (g j₀)) ∧
              Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j))) ⊆ W} : ℝ) *
              (2 * δ * (L : ℝ) ^ k) ^ 2) ≤
          ENNReal.ofReal (δ ^ (-ξ) * (Set.ncard {j | lineCell (2 * δ * (L : ℝ) ^ k / 20)
              (x (g j)) (v (g j)) = lineCell (2 * δ * (L : ℝ) ^ k / 20) (x (g j₀)) (v (g j₀))} : ℝ)) *
            MeasureTheory.volume W) →
       (∀ W : Set Sp, Convex ℝ W →
          ENNReal.ofReal (Set.ncard {j | Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j))) ⊆ W} : ℝ) ≤
          ENNReal.ofReal (δ ^ (-ξ) * m) * MeasureTheory.volume W) →
       AllScales ξ δ (fun j => x (g j)) (fun j => v (g j))) := by
  classical
  set ρ : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (by norm_num) hL)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hρpos : ∀ k, 0 < ρ k := fun k => by simp only [hρdef]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρ k ≤ ρ k' := fun k k' hkk => by
    simp only [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hkk) (by positivity)
  have hρ0 : ρ 0 = 2 * δ := by simp [hρdef]
  have hρsmall : ∀ k < N, ρ k ≤ 1 / 10000 := fun k hk =>
    le_trans (hρmono k (N - 1) (by omega)) htop1
  have hρbig : ∀ k, 2 * δ ≤ ρ k := fun k => by rw [← hρ0]; exact hρmono 0 k (Nat.zero_le _)
  -- the cell maps and their nesting
  set κ : ℕ → Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun k i => lineCell (ρ k / 20) (x i) (v i)
    with hκdef
  have hnest : ∀ j k, j ≤ k → ∀ i i', κ j i = κ j i' → κ k i = κ k i' := by
    intro j k hjk i i' h
    have hm : 0 < L ^ (k - j) := pow_pos hL0 _
    have e : ρ k / 20 = ((L ^ (k - j) : ℕ) : ℝ) * (ρ j / 20) := by
      simp only [hρdef]
      push_cast
      rw [show k = j + (k - j) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring
    simp only [hκdef] at h ⊢
    rw [e]
    exact lineCell_nest (by have := hρpos j; positivity) hm h
  -- common classes, then dyadic regularization
  obtain ⟨S₁, hS₁U, hS₁ne, hS₁card, hS₁cls⟩ :=
    common_classes x v (M := 200000) (by norm_num) ρ N U hU
  obtain ⟨S₂, hS₂S₁, hS₂ne, hS₂card, hbal⟩ := dyadic_regularize N κ hnest S₁ hS₁ne
  set m := S₂.card with hmdef
  set g : Fin m → Fin n := fun j => (S₂.equivFin.symm j).1 with hgdef
  have hgS : ∀ j, g j ∈ S₂ := fun j => (S₂.equivFin.symm j).2
  have hginj : Function.Injective g := by
    intro j j' h
    exact S₂.equivFin.symm.injective (Subtype.ext h)
  have hgsurj : ∀ i (hi : i ∈ S₂), g (S₂.equivFin ⟨i, hi⟩) = i := by
    intro i hi
    simp only [hgdef, Equiv.symm_apply_apply]
  have hmpos : 0 < m := Finset.card_pos.2 hS₂ne
  refine ⟨m, g, hmpos, hginj, fun j => hS₁U (hS₂S₁ (hgS j)), ?_, ?_⟩
  · have hlog : (Nat.log 2 S₁.card : ℝ) ≤ Nat.log 2 U.card := by
      exact_mod_cast Nat.log_mono_right (Finset.card_le_card hS₁U)
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (((200000 : ℕ) : ℝ) ^ 6) ^ N := ⟨_, rfl⟩
    have hA : 0 ≤ A := by rw [hAdef]; positivity
    rw [← hAdef] at hS₁card ⊢
    have hlog0 : (0 : ℝ) ≤ (Nat.log 2 S₁.card : ℝ) + 1 := by positivity
    calc (U.card : ℝ) ≤ A * S₁.card := hS₁card
      _ ≤ A * (((Nat.log 2 S₁.card : ℝ) + 1) ^ N * S₂.card) :=
          mul_le_mul_of_nonneg_left hS₂card hA
      _ ≤ A * (((Nat.log 2 U.card : ℝ) + 1) ^ N * S₂.card) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hlog0 (by linarith) N) (Nat.cast_nonneg _)) hA
      _ = A * ((Nat.log 2 U.card : ℝ) + 1) ^ N * m := by ring
  intro hFF hFG ρ₀ hρ₀ hρ₀1
  have hdξ : (1 : ℝ) ≤ δ ^ (-ξ) := by linarith
  by_cases hcase : ρ₀ ≤ ρ (N - 1)
  · -- an intermediate radius of the grid
    have hex : ∃ k, k < N ∧ ρ₀ ≤ ρ k := ⟨N - 1, by omega, hcase⟩
    set kk := Nat.find hex with hkkdef
    obtain ⟨hkkN, hρ₀kk⟩ := Nat.find_spec hex
    have hkkle : ρ kk ≤ δ ^ (-ξ) * ρ₀ := by
      rcases Nat.eq_zero_or_pos kk with h0 | hpos
      · rw [h0, hρ0]
        calc 2 * δ ≤ δ ^ (-ξ) * δ := by nlinarith
          _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr
      · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        have hlt : k' < kk := by omega
        have hprev : ρ k' < ρ₀ := by
          by_contra hge
          exact Nat.find_min hex hlt ⟨by omega, le_of_not_gt hge⟩
        have hstep : ρ kk = (L : ℝ) * ρ k' := by
          simp only [hρdef]; rw [hk', pow_succ]; ring
        rw [hstep]
        calc (L : ℝ) * ρ k' ≤ (L : ℝ) * ρ₀ := by gcongr
          _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr; linarith
    have hcls2 : ∀ i ∈ S₂, ∀ i' ∈ S₂,
        classKey 200000 (ρ kk) (x i) (v i) = classKey 200000 (ρ kk) (x i') (v i') :=
      fun i hi i' hi' => hS₁cls kk hkkN i (hS₂S₁ hi) i' (hS₂S₁ hi')
    obtain ⟨q, hq, z, w, hw, hov, hexu, hused, hfib⟩ := cell_cover hδ (hρbig kk)
      (hρsmall kk hkkN) x v hv hT hcan hanti S₂ hS₂ne hcls2
    obtain ⟨c, hc⟩ := hbal kk hkkN
    -- the members of `S₂` inside the net tube `j`: those of its cell
    have hcount : ∀ j, ∃ i₀ ∈ S₂, Set.ncard {i : Fin m |
        Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j))} = pop S₂ (κ kk) i₀ ∧
        ∀ W : Set Sp, {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j)) ∧
          Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} =
          {i : Fin m | lineCell (ρ kk / 20) (x (g i)) (v (g i)) =
            lineCell (ρ kk / 20) (x i₀) (v i₀) ∧
            Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} := by
      intro j
      obtain ⟨i₀, hi₀, -, -, hiff⟩ := hfib j
      refine ⟨i₀, hi₀, ?_, fun W => ?_⟩
      · have hset : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
            Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j))} =
            {i : Fin m | lineCell (ρ kk / 20) (x (g i)) (v (g i)) =
              lineCell (ρ kk / 20) (x i₀) (v i₀)} := by
          ext i
          simp only [Set.mem_ofPred_eq]
          exact hiff (g i) (hgS i)
        rw [hset, hgdef]
        rw [ncard_enum S₂ (fun i => lineCell (ρ kk / 20) (x i) (v i) =
          lineCell (ρ kk / 20) (x i₀) (v i₀))]
        rfl
      · ext i
        simp only [Set.mem_ofPred_eq]
        rw [hiff (g i) (hgS i)]
    refine ⟨ρ kk, hρ₀kk, le_trans (hρsmall kk hkkN) (by norm_num), hkkle, q, hq, z, w, hw, hov,
      fun i => hexu (g i) (hgS i), fun j => ?_, fun j j' => ?_, fun j W hW => ?_⟩
    · obtain ⟨i, hi, hsub⟩ := hused j
      exact ⟨S₂.equivFin ⟨i, hi⟩, by beta_reduce; rw [hgsurj i hi]; exact hsub⟩
    · obtain ⟨i₀, hi₀, hcnt, -⟩ := hcount j
      obtain ⟨i₀', hi₀', hcnt', -⟩ := hcount j'
      rw [hcnt, hcnt']
      have h1 := (hc i₀ hi₀).2
      have h2 := (hc i₀' hi₀').1
      have h1' : (pop S₂ (κ kk) i₀ : ℝ) < 2 ^ (c + 1) := by exact_mod_cast h1
      have h2' : (2 : ℝ) ^ c ≤ pop S₂ (κ kk) i₀' := by exact_mod_cast h2
      have hpos' : (0 : ℝ) ≤ pop S₂ (κ kk) i₀' := Nat.cast_nonneg _
      calc (pop S₂ (κ kk) i₀ : ℝ) ≤ 2 ^ (c + 1) := h1'.le
        _ = 2 * 2 ^ c := by ring
        _ ≤ 2 * pop S₂ (κ kk) i₀' := by gcongr
        _ ≤ δ ^ (-ξ) * pop S₂ (κ kk) i₀' := by gcongr
    · obtain ⟨i₀, hi₀, hcnt, hset⟩ := hcount j
      rw [hset W, hcnt]
      have := hFF kk hkkN (S₂.equivFin ⟨i₀, hi₀⟩) W hW
      rw [hgsurj i₀ hi₀] at this
      have hpop : (Set.ncard {i : Fin m | lineCell (2 * δ * (L : ℝ) ^ kk / 20) (x (g i)) (v (g i)) =
          lineCell (2 * δ * (L : ℝ) ^ kk / 20) (x i₀) (v i₀)} : ℝ) = pop S₂ (κ kk) i₀ := by
        rw [hgdef]
        rw [ncard_enum S₂ (fun i => lineCell (2 * δ * (L : ℝ) ^ kk / 20) (x i) (v i) =
          lineCell (2 * δ * (L : ℝ) ^ kk / 20) (x i₀) (v i₀))]
        rfl
      rw [hpop] at this
      exact this
  · -- the unit radius
    rw [not_le] at hcase
    have hρ₀big : δ ^ ξ ≤ ρ₀ := le_trans htop2 hcase.le
    have h1le : (1 : ℝ) ≤ δ ^ (-ξ) * ρ₀ := by
      have : δ ^ (-ξ) * δ ^ ξ = 1 := by
        rw [← Real.rpow_add hδ]; simp
      calc (1 : ℝ) = δ ^ (-ξ) * δ ^ ξ := this.symm
        _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr
    set w₀ := v (g ⟨0, hmpos⟩)
    have hR : ∀ i : Fin m, Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
        Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀)) :=
      fun i => (hT (g i)).trans ball_subset_unit_tube
    refine ⟨1, hρ₀1, le_rfl, h1le, 1, one_pos, fun _ => -(1 / 2 : ℝ) • w₀, fun _ => w₀,
      fun _ => hv _, fun j j' hjj' => absurd (Subsingleton.elim j j') hjj',
      fun i => ⟨0, hR i, fun j _ => Subsingleton.elim _ _⟩, fun j => ⟨⟨0, hmpos⟩, hR _⟩,
      fun j j' => ?_, fun j W hW => ?_⟩
    · exact le_mul_of_one_le_left (Nat.cast_nonneg _) hdξ
    · have hset1 : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀)) ∧
          Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} =
          {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} := by
        ext i; simp only [Set.mem_ofPred_eq]; exact ⟨fun h => h.2, fun h => ⟨hR i, h⟩⟩
      have hset2 : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀))} =
          Set.univ := by
        ext i; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hR i
      rw [hset1, hset2, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, one_pow,
        mul_one]
      exact hFG W hW

open Classical in
/-- The all-scales condition for a prepared set. `S` has common residue classes at the radii
`ρ_k = 2δL^k` (`k < N`), cell populations within a ratio `δ^(-ξ)` at every level, cells
`δ^(-ξ)`-Frostman at their radius, and is globally `δ^(-ξ)`-Frostman. Then the enumerated
subfamily satisfies `AllScales ξ δ`. -/
theorem allScales_of_prepared {δ ξ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ) {L N : ℕ}
    (hL : 2 ≤ L) (hN : 0 < N) (hratio : (L : ℝ) ≤ δ ^ (-ξ)) (htwo : (2 : ℝ) ≤ δ ^ (-ξ))
    (htop1 : 2 * δ * (L : ℝ) ^ (N - 1) ≤ 1 / 10000)
    (htop2 : δ ^ ξ ≤ 2 * δ * (L : ℝ) ^ (N - 1))
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcls : ∀ k < N, ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i) (v i) =
      classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i') (v i'))
    (hbal : ∀ k < N, ∀ i ∈ S, ∀ i' ∈ S,
      (pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i : ℝ) ≤
        δ ^ (-ξ) * pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i')
    (hFF : ∀ k < N, ∀ i₀ ∈ S, ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i) =
          lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i₀) (v i₀) ∧
          Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card * (2 * δ * (L : ℝ) ^ k) ^ 2) ≤
      ENNReal.ofReal (δ ^ (-ξ) * pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i₀) *
        MeasureTheory.volume W)
    (hFG : ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
      ENNReal.ofReal (δ ^ (-ξ) * S.card) * MeasureTheory.volume W) :
    AllScales ξ δ (fun j => x (S.equivFin.symm j).1) (fun j => v (S.equivFin.symm j).1) := by
  classical
  set ρ : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (by norm_num) hL)
  have hρpos : ∀ k, 0 < ρ k := fun k => by simp only [hρdef]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρ k ≤ ρ k' := fun k k' hkk => by
    simp only [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hkk) (by positivity)
  have hρ0 : ρ 0 = 2 * δ := by simp [hρdef]
  have hρsmall : ∀ k < N, ρ k ≤ 1 / 10000 := fun k hk =>
    le_trans (hρmono k (N - 1) (by omega)) htop1
  have hρbig : ∀ k, 2 * δ ≤ ρ k := fun k => by rw [← hρ0]; exact hρmono 0 k (Nat.zero_le _)
  set m := S.card with hmdef
  set g : Fin m → Fin n := fun j => (S.equivFin.symm j).1 with hgdef
  have hgS : ∀ j, g j ∈ S := fun j => (S.equivFin.symm j).2
  have hgsurj : ∀ i (hi : i ∈ S), g (S.equivFin ⟨i, hi⟩) = i := by
    intro i hi
    simp only [hgdef, Equiv.symm_apply_apply]
  have hmpos : 0 < m := Finset.card_pos.2 hS
  intro ρ₀ hρ₀ hρ₀1
  have hdξ : (1 : ℝ) ≤ δ ^ (-ξ) := by linarith
  by_cases hcase : ρ₀ ≤ ρ (N - 1)
  · have hex : ∃ k, k < N ∧ ρ₀ ≤ ρ k := ⟨N - 1, by omega, hcase⟩
    set kk := Nat.find hex with hkkdef
    obtain ⟨hkkN, hρ₀kk⟩ := Nat.find_spec hex
    have hkkle : ρ kk ≤ δ ^ (-ξ) * ρ₀ := by
      rcases Nat.eq_zero_or_pos kk with h0 | hpos
      · rw [h0, hρ0]
        calc 2 * δ ≤ δ ^ (-ξ) * δ := by nlinarith
          _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr
      · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        have hlt : k' < kk := by omega
        have hprev : ρ k' < ρ₀ := by
          by_contra hge
          exact Nat.find_min hex hlt ⟨by omega, le_of_not_gt hge⟩
        have hstep : ρ kk = (L : ℝ) * ρ k' := by
          simp only [hρdef]; rw [hk', pow_succ]; ring
        rw [hstep]
        calc (L : ℝ) * ρ k' ≤ (L : ℝ) * ρ₀ := by gcongr
          _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr; linarith
    obtain ⟨q, hq, z, w, hw, hov, hexu, hused, hfib⟩ := cell_cover hδ (hρbig kk)
      (hρsmall kk hkkN) x v hv hT hcan hanti S hS (hcls kk hkkN)
    have hcount : ∀ j, ∃ i₀ ∈ S, Set.ncard {i : Fin m |
        Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j))} =
          pop S (fun i => lineCell (ρ kk / 20) (x i) (v i)) i₀ ∧
        ∀ W : Set Sp, {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j)) ∧
          Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} =
          {i : Fin m | lineCell (ρ kk / 20) (x (g i)) (v (g i)) =
            lineCell (ρ kk / 20) (x i₀) (v i₀) ∧
            Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} := by
      intro j
      obtain ⟨i₀, hi₀, -, -, hiff⟩ := hfib j
      refine ⟨i₀, hi₀, ?_, fun W => ?_⟩
      · have hset : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
            Metric.thickening (ρ kk) (segment ℝ (z j) (z j + w j))} =
            {i : Fin m | lineCell (ρ kk / 20) (x (g i)) (v (g i)) =
              lineCell (ρ kk / 20) (x i₀) (v i₀)} := by
          ext i
          simp only [Set.mem_ofPred_eq]
          exact hiff (g i) (hgS i)
        rw [hset]
        exact ncard_enum S (fun i => lineCell (ρ kk / 20) (x i) (v i) =
          lineCell (ρ kk / 20) (x i₀) (v i₀))
      · ext i
        simp only [Set.mem_ofPred_eq]
        rw [hiff (g i) (hgS i)]
    refine ⟨ρ kk, hρ₀kk, le_trans (hρsmall kk hkkN) (by norm_num), hkkle, q, hq, z, w, hw, hov,
      fun i => hexu (g i) (hgS i), fun j => ?_, fun j j' => ?_, fun j W hW => ?_⟩
    · obtain ⟨i, hi, hsub⟩ := hused j
      exact ⟨S.equivFin ⟨i, hi⟩, by simp only [Equiv.symm_apply_apply]; exact hsub⟩
    · obtain ⟨i₀, hi₀, hcnt, -⟩ := hcount j
      obtain ⟨i₀', hi₀', hcnt', -⟩ := hcount j'
      rw [hcnt, hcnt']
      exact hbal kk hkkN i₀ hi₀ i₀' hi₀'
    · obtain ⟨i₀, hi₀, hcnt, hset⟩ := hcount j
      rw [hset W, hcnt]
      have hset2 : (Set.ncard {i : Fin m | lineCell (ρ kk / 20) (x (g i)) (v (g i)) =
          lineCell (ρ kk / 20) (x i₀) (v i₀) ∧
          Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W}) =
          (S.filter (fun i => lineCell (ρ kk / 20) (x i) (v i) = lineCell (ρ kk / 20) (x i₀) (v i₀) ∧
            Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card :=
        ncard_enum S (fun i => lineCell (ρ kk / 20) (x i) (v i) = lineCell (ρ kk / 20) (x i₀) (v i₀) ∧
          Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)
      rw [hset2]
      exact hFF kk hkkN i₀ hi₀ W hW
  · rw [not_le] at hcase
    have hρ₀big : δ ^ ξ ≤ ρ₀ := le_trans htop2 hcase.le
    have h1le : (1 : ℝ) ≤ δ ^ (-ξ) * ρ₀ := by
      have : δ ^ (-ξ) * δ ^ ξ = 1 := by
        rw [← Real.rpow_add hδ]; simp
      calc (1 : ℝ) = δ ^ (-ξ) * δ ^ ξ := this.symm
        _ ≤ δ ^ (-ξ) * ρ₀ := by gcongr
    set w₀ := v (g ⟨0, hmpos⟩)
    have hR : ∀ i : Fin m, Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
        Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀)) :=
      fun i => (hT (g i)).trans ball_subset_unit_tube
    refine ⟨1, hρ₀1, le_rfl, h1le, 1, one_pos, fun _ => -(1 / 2 : ℝ) • w₀, fun _ => w₀,
      fun _ => hv _, fun j j' hjj' => absurd (Subsingleton.elim j j') hjj',
      fun i => ⟨0, hR i, fun j _ => Subsingleton.elim _ _⟩, fun j => ⟨⟨0, hmpos⟩, hR _⟩,
      fun j j' => ?_, fun j W hW => ?_⟩
    · exact le_mul_of_one_le_left (Nat.cast_nonneg _) hdξ
    · have hset1 : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀)) ∧
          Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} =
          {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} := by
        ext i; simp only [Set.mem_ofPred_eq]; exact ⟨fun h => h.2, fun h => ⟨hR i, h⟩⟩
      have hset2 : {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆
          Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • w₀) (-(1 / 2 : ℝ) • w₀ + w₀))} =
          Set.univ := by
        ext i; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hR i
      have hset3 : Set.ncard {i : Fin m | Metric.thickening δ (segment ℝ (x (g i)) (x (g i) + v (g i))) ⊆ W} =
          (S.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card :=
        ncard_enum S (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)
      rw [hset1, hset2, hset3, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, one_pow,
        mul_one]
      exact hFG W hW

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
