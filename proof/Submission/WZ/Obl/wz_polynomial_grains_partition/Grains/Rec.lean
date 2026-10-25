-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Rec.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Step

/-!
# The grains recursion (adapted from x0325, o005 branch x0325)

Nodes of level `t` are indexed by sequences `Fin t → Idx p` of merged-child indices; the leaves
of level `t` are the wall pieces of the nodes, by subcube. Besides x0325's mass identity, mass
decay and tube counts, the merged step gives the number of nodes and leaves of positive mass
(`node_count`, `leaf_count`) and a polynomial for every leaf (`leaf_poly`).
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Grains

open MeasureTheory

namespace RecAux

/-- Index of the children produced by one split step. -/
abbrev I (p : ℕ) := Idx p

/-- Index of the subcubes (leaves) of one split step. -/
abbrev Q (p : ℕ) := Fin 3 → Fin (2 ^ p)

open SplitAux in
/-- The properties of the data provided by `split_step`. -/
def StepProp (p : ℕ) (δ : ℝ) (A : Set Space) (a : Fin 3 → ℝ) (ℓ : ℝ)
    (C : I p → Set Space) (L : Q p → Set Space) (Qp : MvPolynomial (Fin 3) ℝ) : Prop :=
  (∀ i, MeasurableSet (C i) ∧ C i ⊆ A ∧ C i ⊆ subbox a ℓ i.1) ∧
  (∀ q, MeasurableSet (L q) ∧ L q ⊆ A ∧ L q ⊆ subbox a ℓ q) ∧
  (Pairwise fun i j => Disjoint (C i) (C j)) ∧
  (Pairwise fun q q' => Disjoint (L q) (L q')) ∧
  (∀ i q, Disjoint (C i) (L q)) ∧
  A = (⋃ i, C i) ∪ ⋃ q, L q ∧
  (∀ i, ((2 : ENNReal) ^ p) ^ 3 * volume (C i) ≤ 2 * volume A) ∧
  (Qp ≠ 0 ∧ Qp.totalDegree ≤ 18 * 2 ^ p ∧
    ∀ q, L q ⊆ Metric.thickening (100 * δ) (zeroSet Qp)) ∧
  (Finset.univ.filter fun i => volume (C i) ≠ 0).card ≤ 2 * 8 ^ p ∧
  (∀ x v : Space, ‖v‖ ≤ 1 →
    ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ C i).Nonempty}.ncard : ℝ) ≤
      20 * 2 ^ p) ∧
  (∀ x v : Space, ‖v‖ ≤ 1 → δ ≤ ℓ / 2 ^ p →
    ({q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ L q).Nonempty}.ncard : ℝ) ≤
      400 * 2 ^ p)

open Classical in
/-- The (chosen) data of one split step, or empty data when the hypotheses fail. -/
noncomputable def step (p : ℕ) (δ : ℝ) (A : Set Space) (a : Fin 3 → ℝ) (ℓ : ℝ) :
    (I p → Set Space) × (Q p → Set Space) × MvPolynomial (Fin 3) ℝ :=
  if h : 1 ≤ p ∧ 0 < δ ∧ MeasurableSet A ∧ 0 < ℓ ∧ A ⊆ box a ℓ then
    ((split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose,
      (split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose_spec.choose,
      (split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose_spec.choose_spec.choose)
  else (fun _ => ∅, fun _ => ∅, 1)

theorem step_spec {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {A : Set Space}
    (hA : MeasurableSet A) {a : Fin 3 → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hAQ : A ⊆ box a ℓ) :
    StepProp p δ A a ℓ (step p δ A a ℓ).1 (step p δ A a ℓ).2.1 (step p δ A a ℓ).2.2 := by
  have h : 1 ≤ p ∧ 0 < δ ∧ MeasurableSet A ∧ 0 < ℓ ∧ A ⊆ box a ℓ := ⟨hp, hδ, hA, hℓ, hAQ⟩
  rw [step, dite_eq_left h]
  exact (split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose_spec.choose_spec.choose_spec

/-- Side of the cubes at level `t`. -/
noncomputable def scale (p t : ℕ) : ℝ := 2 / ((2 : ℝ) ^ p) ^ t

/-- Corner of the subcube `q`. -/
noncomputable def subc (p : ℕ) (a : Fin 3 → ℝ) (ℓ : ℝ) (q : Q p) : Fin 3 → ℝ :=
  fun r => a r + ((q r : ℕ) : ℝ) * (ℓ / 2 ^ p)

theorem subbox_eq (p : ℕ) (a : Fin 3 → ℝ) (ℓ : ℝ) (q : Q p) :
    subbox a ℓ q = box (subc p a ℓ q) (ℓ / 2 ^ p) := by
  simp [subbox]
  rfl

theorem scale_pos (p t : ℕ) : 0 < scale p t := by
  unfold scale; positivity

theorem scale_succ (p t : ℕ) : scale p (t + 1) = scale p t / 2 ^ p := by
  unfold scale; rw [pow_succ, div_div]

theorem scale_le_two (p t : ℕ) : scale p t ≤ 2 := by
  unfold scale
  have : (1 : ℝ) ≤ ((2 : ℝ) ^ p) ^ t := one_le_pow₀ (one_le_pow₀ (by norm_num))
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem scale_anti (p : ℕ) {t t' : ℕ} (h : t ≤ t') : scale p t' ≤ scale p t := by
  unfold scale
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) h

theorem box_subset_closedBall (a : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    box a s ⊆ Metric.closedBall (WithLp.toLp 2 a : Space) (2 * s) := by
  intro x hx
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq]
  have h : ∀ i, dist (x i) ((WithLp.toLp 2 a : Space) i) ^ 2 ≤ s ^ 2 := by
    intro i
    have h1 := hx i
    have h2 : |x i - a i| ≤ s := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h3 : dist (x i) ((WithLp.toLp 2 a : Space) i) = |x i - a i| := Real.dist_eq _ _
    rw [h3]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  calc √(∑ i, dist (x i) ((WithLp.toLp 2 a : Space) i) ^ 2) ≤ √((2 * s) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Fin.sum_univ_three]
        nlinarith [h 0, h 1, h 2]
    _ = 2 * s := Real.sqrt_sq (by linarith)

theorem volume_box_eq (a : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    volume (box a s) = ENNReal.ofReal (s ^ 3) := by
  have : box a s = (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Set.Icc a (fun i => a i + s) := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hs]

theorem ball_subset_box : Metric.ball (0 : Space) 1 ⊆ box (fun _ => -1) 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  intro i
  have h1 := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at h1
  have h2 := abs_le.1 (h1.trans hx.le)
  constructor <;> linarith [h2.1, h2.2]

theorem ncard_setOf_eq_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    {a | P a}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp


theorem card_fiber_le {α β : Type*} [Fintype α] [DecidableEq β]
    (P : α → Prop) [DecidablePred P] (f : α → β) (S : Finset β) (c : ℝ)
    (hS : ∀ a, P a → f a ∈ S)
    (hfib : ∀ b ∈ S, ((Finset.univ.filter fun a => P a ∧ f a = b).card : ℝ) ≤ c) :
    ((Finset.univ.filter P).card : ℝ) ≤ S.card * c := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S) (fun a ha => hS a (by simpa using ha))]
  push_cast
  calc ∑ b ∈ S, (((Finset.univ.filter P).filter fun a => f a = b).card : ℝ) ≤ ∑ b ∈ S, c := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.filter_filter]
        exact hfib b hb
    _ = S.card * c := by rw [Finset.sum_const, nsmul_eq_mul]


/-- The pieces of level `t` of the recursion, with the corners of their cubes. -/
noncomputable def node (p : ℕ) (δ : ℝ) (E : Set Space) :
    (t : ℕ) → (Fin t → I p) → Set Space × (Fin 3 → ℝ)
  | 0, _ => (E, fun _ => -1)
  | t + 1, σ =>
    ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2 (scale p t)).1 (σ 0),
      subc p (node p δ E t (Fin.tail σ)).2 (scale p t) (σ 0).1)

/-- The leaves produced at level `t`. -/
noncomputable def leaf (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (σ : Fin t → I p) (q : Q p) :
    Set Space :=
  (step p δ (node p δ E t σ).1 (node p δ E t σ).2 (scale p t)).2.1 q

/-- The wall polynomial of the leaves of a node. -/
noncomputable def leafPoly (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (σ : Fin t → I p) :
    MvPolynomial (Fin 3) ℝ :=
  (step p δ (node p δ E t σ).1 (node p δ E t σ).2 (scale p t)).2.2

theorem node_succ (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (σ : Fin (t + 1) → I p) :
    node p δ E (t + 1) σ =
      ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2 (scale p t)).1 (σ 0),
        subc p (node p δ E t (Fin.tail σ)).2 (scale p t) (σ 0).1) := rfl

theorem node_cons (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (i : I p) (τ : Fin t → I p) :
    node p δ E (t + 1) (Fin.cons i τ) =
      ((step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).1 i,
        subc p (node p δ E t τ).2 (scale p t) i.1) := by
  rw [node_succ, Fin.tail_cons, Fin.cons_zero]

/-- Hypotheses of the recursion. -/
structure Hyp (p : ℕ) (δ : ℝ) (E : Set Space) : Prop where
  hp : 1 ≤ p
  hδ : 0 < δ
  hE : MeasurableSet E
  hEb : E ⊆ box (fun _ => -1) 2

section
variable {p : ℕ} {δ : ℝ} {E : Set Space}

theorem node_props (H : Hyp p δ E) (t : ℕ) : ∀ σ : Fin t → I p,
    MeasurableSet (node p δ E t σ).1 ∧ (node p δ E t σ).1 ⊆ box (node p δ E t σ).2 (scale p t) ∧
    (node p δ E t σ).1 ⊆ E ∧
    (((2 : ENNReal) ^ p) ^ 3) ^ t * volume (node p δ E t σ).1 ≤ 2 ^ t * volume E := by
  induction t with
  | zero =>
    intro σ
    refine ⟨H.hE, ?_, subset_rfl, ?_⟩
    · have : scale p 0 = 2 := by simp [scale]
      rw [this]
      exact H.hEb
    · simp [node]
  | succ t ih =>
    intro σ
    obtain ⟨h1, h2, h3, h4⟩ := ih (Fin.tail σ)
    obtain ⟨hC, -, -, -, -, -, hvol, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    rw [node_succ]
    refine ⟨(hC (σ 0)).1, ?_, (hC (σ 0)).2.1.trans h3, ?_⟩
    · have := (hC (σ 0)).2.2
      rwa [subbox_eq, ← scale_succ] at this
    · calc (((2 : ENNReal) ^ p) ^ 3) ^ (t + 1) *
            volume ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2
              (scale p t)).1 (σ 0))
          = (((2 : ENNReal) ^ p) ^ 3) ^ t * (((2 : ENNReal) ^ p) ^ 3 *
            volume ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2
              (scale p t)).1 (σ 0))) := by
            rw [pow_succ, mul_assoc]
        _ ≤ (((2 : ENNReal) ^ p) ^ 3) ^ t * (2 * volume (node p δ E t (Fin.tail σ)).1) :=
            mul_le_mul_right (hvol (σ 0)) _
        _ = 2 * ((((2 : ENNReal) ^ p) ^ 3) ^ t * volume (node p δ E t (Fin.tail σ)).1) := by
            ring
        _ ≤ 2 * (2 ^ t * volume E) := by gcongr
        _ = 2 ^ (t + 1) * volume E := by ring

theorem node_disj (H : Hyp p δ E) (t : ℕ) :
    Pairwise fun σ τ : Fin t → I p => Disjoint (node p δ E t σ).1 (node p δ E t τ).1 := by
  induction t with
  | zero => intro σ τ h; exact absurd (Subsingleton.elim σ τ) h
  | succ t ih =>
    intro σ τ hστ
    obtain ⟨h1, h2, -, -⟩ := node_props H t (Fin.tail σ)
    obtain ⟨h1', h2', -, -⟩ := node_props H t (Fin.tail τ)
    have hS := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    have hS' := step_spec H.hp H.hδ h1' (scale_pos p t) h2'
    show Disjoint (node p δ E (t + 1) σ).1 (node p δ E (t + 1) τ).1
    rw [node_succ, node_succ]
    by_cases htail : Fin.tail σ = Fin.tail τ
    · have h0 : σ 0 ≠ τ 0 := by
        intro h0
        apply hστ
        rw [← Fin.cons_self_tail σ, ← Fin.cons_self_tail τ, h0, htail]
      rw [← htail]
      exact hS.2.2.1 h0
    · exact (ih htail).mono (hS.1 (σ 0)).2.1 (hS'.1 (τ 0)).2.1

theorem mass_step (H : Hyp p δ E) (t : ℕ) (τ : Fin t → I p) :
    volume (node p δ E t τ).1 =
      ∑ i, volume (node p δ E (t + 1) (Fin.cons i τ)).1 + ∑ q, volume (leaf p δ E t τ q) := by
  obtain ⟨h1, h2, -, -⟩ := node_props H t τ
  obtain ⟨hC, hL, hCd, hLd, hCL, hU, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
  simp only [node_cons, leaf]
  conv_lhs => rw [hU]
  rw [measure_union (Set.disjoint_iUnion_left.2 fun i => Set.disjoint_iUnion_right.2 fun q =>
      hCL i q) (MeasurableSet.iUnion fun q => (hL q).1), measure_iUnion hCd (fun i => (hC i).1),
    measure_iUnion hLd (fun q => (hL q).1), tsum_fintype, tsum_fintype]

theorem mass_eq (H : Hyp p δ E) (t : ℕ) :
    volume E = ∑ σ : Fin t → I p, volume (node p δ E t σ).1 +
      ∑ t' ∈ Finset.range t, ∑ σ : Fin t' → I p, ∑ q, volume (leaf p δ E t' σ q) := by
  induction t with
  | zero => simp [node]
  | succ t ih =>
    rw [ih, Finset.sum_range_succ]
    have key : ∑ σ : Fin t → I p, volume (node p δ E t σ).1 =
        ∑ σ : Fin (t + 1) → I p, volume (node p δ E (t + 1) σ).1 +
          ∑ σ : Fin t → I p, ∑ q, volume (leaf p δ E t σ q) := by
      rw [Finset.sum_congr rfl (fun τ _ => mass_step H t τ), Finset.sum_add_distrib]
      congr 1
      have := Fintype.sum_equiv (Fin.consEquiv fun _ => I p)
        (fun y => volume (node p δ E (t + 1) (Fin.cons y.1 y.2)).1)
        (fun σ => volume (node p δ E (t + 1) σ).1) (fun y => rfl)
      rw [← this, Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [key]
    ring

theorem node_tube (H : Hyp p δ E) (x v : Space) (hv : ‖v‖ ≤ 1) (t : ℕ) :
    ({σ : Fin t → I p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
      (node p δ E t σ).1).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ t := by
  classical
  induction t with
  | zero =>
    rw [pow_zero]
    have : {σ : Fin 0 → I p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
        (node p δ E 0 σ).1).Nonempty}.ncard ≤ 1 := by
      calc _ ≤ (Set.univ : Set (Fin 0 → I p)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
        _ = 1 := by rw [Set.ncard_univ]; simp
    exact_mod_cast this
  | succ t ih =>
    rw [ncard_setOf_eq_card] at ih ⊢
    calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
            (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E t τ).1).Nonempty).card : ℝ) *
            (20 * 2 ^ p) := by
          apply card_fiber_le _ Fin.tail
          · intro σ hσ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            obtain ⟨h1, h2, -, -⟩ := node_props H t (Fin.tail σ)
            obtain ⟨hC, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
            rw [node_succ] at hσ
            exact hσ.mono (Set.inter_subset_inter_right _ (hC (σ 0)).2.1)
          · intro τ _
            obtain ⟨h1, h2, -, -⟩ := node_props H t τ
            obtain ⟨-, -, -, -, -, -, -, -, -, htC, -⟩ :=
              step_spec H.hp H.hδ h1 (scale_pos p t) h2
            have hc := htC x v hv
            rw [ncard_setOf_eq_card] at hc
            refine le_trans ?_ hc
            have hsub : (Finset.univ.filter fun σ : Fin (t + 1) → I p =>
                (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E (t + 1) σ).1).Nonempty ∧
                  Fin.tail σ = τ) ⊆
                (Finset.univ.filter fun i => (Metric.thickening δ (segment ℝ x (x + v)) ∩
                  (step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).1 i).Nonempty).image
                  (fun i => (Fin.cons i τ : Fin (t + 1) → I p)) := by
              intro σ hσ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
              obtain ⟨hσ1, hσ2⟩ := hσ
              rw [Finset.mem_image]
              refine ⟨σ 0, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [node_succ, hσ2] at hσ1
                exact hσ1
              · rw [← hσ2, Fin.cons_self_tail]
            exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
      _ ≤ (20 * 2 ^ p) ^ t * (20 * 2 ^ p) := by gcongr
      _ = (20 * 2 ^ p) ^ (t + 1) := (pow_succ _ _).symm

/-- The nodes of positive mass of level `t` number at most `(2 · 8^p)^t`. -/
theorem node_count (H : Hyp p δ E) (t : ℕ) :
    ((Finset.univ.filter fun σ : Fin t → I p => volume (node p δ E t σ).1 ≠ 0).card : ℝ) ≤
      (2 * 8 ^ p) ^ t := by
  classical
  induction t with
  | zero =>
    rw [pow_zero]
    have : (Finset.univ.filter fun σ : Fin 0 → I p => volume (node p δ E 0 σ).1 ≠ 0).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  | succ t ih =>
    calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
            volume (node p δ E t τ).1 ≠ 0).card : ℝ) * (2 * 8 ^ p) := by
          apply card_fiber_le _ Fin.tail
          · intro σ hσ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            obtain ⟨h1, h2, -, -⟩ := node_props H t (Fin.tail σ)
            obtain ⟨hC, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
            rw [node_succ] at hσ
            exact fun h0 => hσ (measure_mono_null (hC (σ 0)).2.1 h0)
          · intro τ _
            obtain ⟨h1, h2, -, -⟩ := node_props H t τ
            obtain ⟨-, -, -, -, -, -, -, -, hcount, -⟩ :=
              step_spec H.hp H.hδ h1 (scale_pos p t) h2
            have hsub : (Finset.univ.filter fun σ : Fin (t + 1) → I p =>
                volume (node p δ E (t + 1) σ).1 ≠ 0 ∧ Fin.tail σ = τ) ⊆
                (Finset.univ.filter fun i => volume
                  ((step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).1 i) ≠ 0).image
                  (fun i => (Fin.cons i τ : Fin (t + 1) → I p)) := by
              intro σ hσ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
              obtain ⟨hσ1, hσ2⟩ := hσ
              rw [Finset.mem_image]
              refine ⟨σ 0, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [node_succ, hσ2] at hσ1
                exact hσ1
              · rw [← hσ2, Fin.cons_self_tail]
            have := (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hcount)
            exact_mod_cast this
      _ ≤ (2 * 8 ^ p) ^ t * (2 * 8 ^ p) := by gcongr
      _ = (2 * 8 ^ p) ^ (t + 1) := (pow_succ _ _).symm

theorem leaf_props (H : Hyp p δ E) (t : ℕ) (σ : Fin t → I p) (q : Q p) :
    MeasurableSet (leaf p δ E t σ q) ∧ leaf p δ E t σ q ⊆ (node p δ E t σ).1 ∧
    leaf p δ E t σ q ⊆ box (subc p (node p δ E t σ).2 (scale p t) q) (scale p (t + 1)) ∧
    (leafPoly p δ E t σ ≠ 0 ∧ (leafPoly p δ E t σ).totalDegree ≤ 18 * 2 ^ p ∧
      leaf p δ E t σ q ⊆ Metric.thickening (100 * δ) (SplitAux.zeroSet (leafPoly p δ E t σ))) := by
  obtain ⟨h1, h2, -, -⟩ := node_props H t σ
  obtain ⟨-, hL, -, -, -, -, -, hpoly, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
  refine ⟨(hL q).1, (hL q).2.1, ?_, hpoly.1, hpoly.2.1, hpoly.2.2 q⟩
  have := (hL q).2.2
  rwa [subbox_eq, ← scale_succ] at this

theorem leaf_disj (H : Hyp p δ E) (t : ℕ) :
    Pairwise fun y z : (Fin t → I p) × Q p =>
      Disjoint (leaf p δ E t y.1 y.2) (leaf p δ E t z.1 z.2) := by
  intro y z hyz
  by_cases h : y.1 = z.1
  · have hq : y.2 ≠ z.2 := fun h' => hyz (Prod.ext h h')
    obtain ⟨h1, h2, -, -⟩ := node_props H t y.1
    obtain ⟨-, -, -, hLd, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    show Disjoint (leaf p δ E t y.1 y.2) (leaf p δ E t z.1 z.2)
    unfold leaf
    rw [← h]
    exact hLd hq
  · exact (node_disj H t h).mono (leaf_props H t y.1 y.2).2.1 (leaf_props H t z.1 z.2).2.1

theorem leaf_tube (H : Hyp p δ E) (x v : Space) (hv : ‖v‖ ≤ 1) (t : ℕ)
    (hδt : δ ≤ scale p (t + 1)) :
    ({y : (Fin t → I p) × Q p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
      leaf p δ E t y.1 y.2).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ t * (400 * 2 ^ p) := by
  classical
  have ih := node_tube H x v hv t
  rw [ncard_setOf_eq_card] at ih ⊢
  calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
          (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E t τ).1).Nonempty).card : ℝ) *
          (400 * 2 ^ p) := by
        apply card_fiber_le _ Prod.fst
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hy.mono (Set.inter_subset_inter_right _ (leaf_props H t y.1 y.2).2.1)
        · intro τ _
          obtain ⟨h1, h2, -, -⟩ := node_props H t τ
          obtain ⟨-, -, -, -, -, -, -, -, -, -, htL⟩ :=
            step_spec H.hp H.hδ h1 (scale_pos p t) h2
          have hc := htL x v hv (by rw [← scale_succ]; exact hδt)
          rw [ncard_setOf_eq_card] at hc
          refine le_trans ?_ hc
          have hsub : (Finset.univ.filter fun y : (Fin t → I p) × Q p =>
              (Metric.thickening δ (segment ℝ x (x + v)) ∩ leaf p δ E t y.1 y.2).Nonempty ∧
                y.1 = τ) ⊆
              (Finset.univ.filter fun q => (Metric.thickening δ (segment ℝ x (x + v)) ∩
                (step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).2.1 q).Nonempty).image
                (fun q => (τ, q)) := by
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            obtain ⟨hy1, hy2⟩ := hy
            rw [Finset.mem_image]
            refine ⟨y.2, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              unfold leaf at hy1
              rw [hy2] at hy1
              exact hy1
            · rw [← hy2]
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ (20 * 2 ^ p) ^ t * (400 * 2 ^ p) := by gcongr

/-- The leaves of positive mass of level `t` number at most `(2 · 8^p)^t · 8^p`. -/
theorem leaf_count (H : Hyp p δ E) (t : ℕ) :
    ((Finset.univ.filter fun y : (Fin t → I p) × Q p =>
      volume (leaf p δ E t y.1 y.2) ≠ 0).card : ℝ) ≤ (2 * 8 ^ p) ^ t * 8 ^ p := by
  classical
  have ih := node_count H t
  calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
          volume (node p δ E t τ).1 ≠ 0).card : ℝ) * 8 ^ p := by
        apply card_fiber_le _ Prod.fst
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun h0 => hy (measure_mono_null (leaf_props H t y.1 y.2).2.1 h0)
        · intro τ _
          have hsub : (Finset.univ.filter fun y : (Fin t → I p) × Q p =>
              volume (leaf p δ E t y.1 y.2) ≠ 0 ∧ y.1 = τ) ⊆
              (Finset.univ : Finset (Q p)).image (fun q => (τ, q)) := by
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            rw [Finset.mem_image]
            exact ⟨y.2, Finset.mem_univ _, by rw [← hy.2]⟩
          have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
          have h2 : (Finset.univ : Finset (Q p)).card = 8 ^ p := by
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul,
              mul_comm, pow_mul]
            norm_num
          rw [h2] at h1
          exact_mod_cast h1
    _ ≤ (2 * 8 ^ p) ^ t * 8 ^ p := by gcongr

end

end RecAux
end Grains
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
