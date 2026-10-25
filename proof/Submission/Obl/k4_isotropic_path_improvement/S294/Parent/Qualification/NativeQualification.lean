-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeQualification.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeQualification.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4986346c. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeRowFit

set_option autoImplicit false

/-!
# Native polynomial qualification (paper Prop. `a05:qualification`, `tex-06` l. 464–880)

The proposition: every graph-reference incidence outside a small failure set admits a three-row
polynomial of degree `≤ M` with coefficients `≤ K_qual` approximating the graph row `G` within
`h ^ M` at that incidence and on reference-labelled times of its own indexed trajectory, in its own
dyadic block, of the same true label, of ordinary duration `≥ h / K_qual`.

* `NativeQualified`: that property of one incidence (no time rescaling, original line, true label);
  `NativeGridQualified`: the same with the polynomial taken from the finite coefficient grid `η ℤ`
  (coordinates `|a| ≤ L`), which makes the failure set a finite union (`measurableSet_nativeGridQualified`).
* `NativeQualificationStatement` and `nativeQualificationStatement_of_higherJets`: the discovery step
  (l. 843–862): in every version-2 scalar-normal world (`Jets2.ScalarNormal`) whose row `F`
  represents the tangential graph row and whose ORIGINAL line coefficients obey the velocity-graph
  estimate, the higher jets produce a natively qualified incidence (`native_row_fit_of_jetFit`).
* `nativeGridQualified_of_nativeQualified`: coefficient rounding to the grid, error `+ (M + 1) η`.
* `false_of_world_in_failure_set`: no such world lies inside the failure set of the reference.
* `exists_slow_diagonal`, `eventually_rpow_inv_le_rpow`: the slow diagonal `ε_r = 1 / r(N)`,
  `K_qual = N ^ (1 / r(N))`, at the end of the proof.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set Polynomial Filter Topology

noncomputable section

section Predicates

variable {Λ : Type*} {ι : Type*}

/-- **Native qualification** of an incidence `z`: a three-row polynomial `Q` of degree `≤ M` with
coefficients `≤ Kq`, fitting the graph row `G` within `err` at `z` and on the times `v` of the same
dyadic block (`2⁻ᵀ`) of `z`'s own line `z.1` that are reference-labelled (`(z.1, v) ∈ Eref`) with the
same true label, of total ordinary duration `≥ dur`. -/
def NativeQualified (Eref : Set (Λ × ℝ)) (lab : Λ × ℝ → ι) (G : Λ × ℝ → Fin 3 → ℝ)
    (M T : ℕ) (Kq err dur : ℝ) (z : Λ × ℝ) : Prop :=
  ∃ Q : Fin 3 → Polynomial ℝ, (∀ j, (Q j).natDegree ≤ M) ∧ (∀ j k, |(Q j).coeff k| ≤ Kq) ∧
    (∀ j, |G z j - (Q j).eval z.2| ≤ err) ∧
    ENNReal.ofReal dur ≤ volume {v : ℝ | v ∈ dyadicBlock T z.2 ∧ (z.1, v) ∈ Eref ∧
      lab (z.1, v) = lab z ∧ ∀ j, |G (z.1, v) j - (Q j).eval v| ≤ err}

theorem NativeQualified.mono {Eref Eref' : Set (Λ × ℝ)} {lab : Λ × ℝ → ι}
    {G : Λ × ℝ → Fin 3 → ℝ} {M T : ℕ} {Kq Kq' err err' dur dur' : ℝ} {z : Λ × ℝ}
    (h : NativeQualified Eref lab G M T Kq err dur z) (hE : Eref ⊆ Eref') (hK : Kq ≤ Kq')
    (he : err ≤ err') (hd : dur' ≤ dur) :
    NativeQualified Eref' lab G M T Kq' err' dur' z := by
  obtain ⟨Q, hdeg, hco, hz, hdur⟩ := h
  refine ⟨Q, hdeg, fun j k => (hco j k).trans hK, fun j => (hz j).trans he, ?_⟩
  refine (ENNReal.ofReal_le_ofReal hd).trans (hdur.trans (measure_mono ?_))
  rintro v ⟨hv1, hv2, hv3, hv4⟩
  exact ⟨hv1, hE hv2, hv3, fun j => (hv4 j).trans he⟩

/-- The mesh polynomial with integer coordinates `a`: coefficients `η · a k` for `k ≤ M`. -/
def gridPoly (η : ℝ) {M : ℕ} (a : Fin (M + 1) → ℤ) : Polynomial ℝ :=
  ∑ k : Fin (M + 1), C (η * a k) * X ^ (k : ℕ)

/-- The mesh coordinates of a polynomial (rounding every coefficient down to `η ℤ`). -/
def meshCoords (η : ℝ) (M : ℕ) (Q : Polynomial ℝ) : Fin (M + 1) → ℤ :=
  fun k => ⌊Q.coeff k / η⌋

/-- **Grid qualification**: `NativeQualified` with the polynomial from the finite grid of mesh
polynomials with coordinates `|a j k| ≤ L`. -/
def NativeGridQualified (Eref : Set (Λ × ℝ)) (lab : Λ × ℝ → ι) (G : Λ × ℝ → Fin 3 → ℝ)
    (M T : ℕ) (η : ℝ) (L : ℤ) (err dur : ℝ) (z : Λ × ℝ) : Prop :=
  ∃ a : Fin 3 → Fin (M + 1) → ℤ, (∀ j k, |a j k| ≤ L) ∧
    (∀ j, |G z j - (gridPoly η (a j)).eval z.2| ≤ err) ∧
    ENNReal.ofReal dur ≤ volume {v : ℝ | v ∈ dyadicBlock T z.2 ∧ (z.1, v) ∈ Eref ∧
      lab (z.1, v) = lab z ∧ ∀ j, |G (z.1, v) j - (gridPoly η (a j)).eval v| ≤ err}

end Predicates

section Grid

theorem natDegree_gridPoly_le (η : ℝ) {M : ℕ} (a : Fin (M + 1) → ℤ) :
    (gridPoly η a).natDegree ≤ M := by
  unfold gridPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp k.isLt)

theorem coeff_gridPoly (η : ℝ) {M : ℕ} (a : Fin (M + 1) → ℤ) (n : ℕ) :
    (gridPoly η a).coeff n = if h : n < M + 1 then η * a ⟨n, h⟩ else 0 := by
  unfold gridPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hnb
      exact hb (Fin.ext hnb.symm)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hnb
    exact h (hnb ▸ b.isLt)

theorem eval_gridPoly (η : ℝ) {M : ℕ} (a : Fin (M + 1) → ℤ) (v : ℝ) :
    (gridPoly η a).eval v = ∑ k : Fin (M + 1), η * a k * v ^ (k : ℕ) := by
  simp [gridPoly, eval_finsetSum]

theorem abs_coeff_gridPoly_le {η : ℝ} (hη : 0 ≤ η) {M : ℕ} {a : Fin (M + 1) → ℤ} {L : ℤ}
    (ha : ∀ k, |a k| ≤ L) (n : ℕ) : |(gridPoly η a).coeff n| ≤ η * L := by
  have hL : (0 : ℝ) ≤ L := by exact_mod_cast (abs_nonneg _).trans (ha 0)
  rw [coeff_gridPoly]
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast ha ⟨n, h⟩) hη
  · rw [abs_zero]
    positivity

/-- Rounding down to the mesh `η ℤ` moves a number by less than `η`. -/
theorem abs_sub_mesh_le {η : ℝ} (hη : 0 < η) (x : ℝ) : |x - η * ⌊x / η⌋| ≤ η := by
  have h1 : (⌊x / η⌋ : ℝ) ≤ x / η := Int.floor_le _
  have h2 : x / η < ⌊x / η⌋ + 1 := Int.lt_floor_add_one _
  have h1' : η * ⌊x / η⌋ ≤ x := by
    have := mul_le_mul_of_nonneg_left h1 hη.le
    rwa [mul_div_cancel₀ _ hη.ne'] at this
  have h2' : x < η * ⌊x / η⌋ + η := by
    have := mul_lt_mul_of_pos_left h2 hη
    rwa [mul_div_cancel₀ _ hη.ne', mul_add, mul_one] at this
  rw [abs_le]
  constructor <;> linarith

theorem abs_meshCoords_le {η : ℝ} (hη : 0 < η) {M : ℕ} {Q : Polynomial ℝ} {Kq : ℝ}
    (hQ : ∀ k, |Q.coeff k| ≤ Kq) (k : Fin (M + 1)) :
    |meshCoords η M Q k| ≤ ⌈Kq / η⌉ + 1 := by
  set x := Q.coeff k with hx
  have hxK : |x| ≤ Kq := hQ k
  have h1 : (⌊x / η⌋ : ℝ) ≤ x / η := Int.floor_le _
  have h2 : x / η < ⌊x / η⌋ + 1 := Int.lt_floor_add_one _
  have h3 : x / η ≤ Kq / η := div_le_div_of_nonneg_right (le_of_abs_le hxK) hη.le
  have h4 : -(Kq / η) ≤ x / η := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (neg_le_of_abs_le hxK) hη.le
  have h5 : Kq / η ≤ (⌈Kq / η⌉ : ℝ) := Int.le_ceil _
  have hup : ⌊x / η⌋ ≤ ⌈Kq / η⌉ := by
    have : (⌊x / η⌋ : ℝ) ≤ (⌈Kq / η⌉ : ℝ) := by linarith
    exact_mod_cast this
  have hlo : -(⌈Kq / η⌉ + 1) ≤ ⌊x / η⌋ := by
    have : (-((⌈Kq / η⌉ : ℝ) + 1)) ≤ (⌊x / η⌋ : ℝ) := by linarith
    exact_mod_cast this
  show |⌊x / η⌋| ≤ ⌈Kq / η⌉ + 1
  rw [abs_le]
  constructor <;> omega

/-- Evaluation error of the grid rounding on `|v| ≤ 1`. -/
theorem abs_eval_sub_gridPoly_le {η : ℝ} (hη : 0 < η) {M : ℕ} {Q : Polynomial ℝ}
    (hQ : Q.natDegree ≤ M) {v : ℝ} (hv : |v| ≤ 1) :
    |Q.eval v - (gridPoly η (meshCoords η M Q)).eval v| ≤ (M + 1) * η := by
  have hQe : Q.eval v = ∑ k : Fin (M + 1), Q.coeff k * v ^ (k : ℕ) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hQ)]
    exact (Fin.sum_univ_eq_sum_range (fun i => Q.coeff i * v ^ i) (M + 1)).symm
  rw [hQe, eval_gridPoly, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : Fin (M + 1),
      |Q.coeff k * v ^ (k : ℕ) - η * (meshCoords η M Q k : ℝ) * v ^ (k : ℕ)| ≤ η := by
    intro k
    have hvk : |v ^ (k : ℕ)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hv
    rw [← sub_mul, abs_mul]
    calc |Q.coeff k - η * (meshCoords η M Q k : ℝ)| * |v ^ (k : ℕ)|
        ≤ η * 1 := mul_le_mul (abs_sub_mesh_le hη _) hvk (abs_nonneg _) hη.le
      _ = η := mul_one η
  calc _ ≤ ∑ k : Fin (M + 1),
        |Q.coeff k * v ^ (k : ℕ) - η * (meshCoords η M Q k : ℝ) * v ^ (k : ℕ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (M + 1), η := Finset.sum_le_sum fun k _ => hterm k
    _ = (M + 1) * η := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

variable {Λ : Type*} {ι : Type*}

/-- **Coefficient rounding** (paper l. 563–566): a natively qualified incidence is grid-qualified
with mesh `η`, coordinates `≤ ⌈Kq / η⌉ + 1` and error `err + (M + 1) η`, for reference times in
`[0, 1]` (keeping the occurrence, the witness times and their duration). -/
theorem nativeGridQualified_of_nativeQualified {Eref : Set (Λ × ℝ)} {lab : Λ × ℝ → ι}
    {G : Λ × ℝ → Fin 3 → ℝ} {M T : ℕ} {Kq err dur η : ℝ} (hη : 0 < η) {z : Λ × ℝ}
    (hEt : ∀ v, (z.1, v) ∈ Eref → v ∈ Icc (0 : ℝ) 1) (hzt : z.2 ∈ Icc (0 : ℝ) 1)
    (h : NativeQualified Eref lab G M T Kq err dur z) :
    NativeGridQualified Eref lab G M T η (⌈Kq / η⌉ + 1) (err + (M + 1) * η) dur z := by
  obtain ⟨Q, hdeg, hco, hz, hdur⟩ := h
  have habs : ∀ {v : ℝ}, v ∈ Icc (0 : ℝ) 1 → |v| ≤ 1 := fun hv => by
    rw [abs_of_nonneg hv.1]; exact hv.2
  have hround : ∀ j {v : ℝ}, v ∈ Icc (0 : ℝ) 1 → ∀ g : ℝ, |g - (Q j).eval v| ≤ err →
      |g - (gridPoly η (meshCoords η M (Q j))).eval v| ≤ err + (M + 1) * η := by
    intro j v hv g hg
    calc |g - (gridPoly η (meshCoords η M (Q j))).eval v|
        ≤ |g - (Q j).eval v| + |(Q j).eval v - (gridPoly η (meshCoords η M (Q j))).eval v| :=
          abs_sub_le _ _ _
      _ ≤ err + (M + 1) * η := add_le_add hg (abs_eval_sub_gridPoly_le hη (hdeg j) (habs hv))
  refine ⟨fun j => meshCoords η M (Q j), fun j k => abs_meshCoords_le hη (hco j) k,
    fun j => hround j hzt _ (hz j), hdur.trans (measure_mono ?_)⟩
  rintro v ⟨hv1, hv2, hv3, hv4⟩
  exact ⟨hv1, hv2, hv3, fun j => hround j (hEt v hv2) _ (hv4 j)⟩

/-- A grid-qualified incidence is natively qualified with coefficient bound `η L`. -/
theorem nativeQualified_of_nativeGridQualified {Eref : Set (Λ × ℝ)} {lab : Λ × ℝ → ι}
    {G : Λ × ℝ → Fin 3 → ℝ} {M T : ℕ} {η : ℝ} (hη : 0 ≤ η) {L : ℤ} {err dur : ℝ}
    {z : Λ × ℝ} (h : NativeGridQualified Eref lab G M T η L err dur z) :
    NativeQualified Eref lab G M T (η * L) err dur z := by
  obtain ⟨a, ha, hz, hdur⟩ := h
  exact ⟨fun j => gridPoly η (a j), fun j => natDegree_gridPoly_le η (a j),
    fun j k => abs_coeff_gridPoly_le hη (ha j) k, hz, hdur⟩

end Grid

section Measurability

variable {Λ ι : Type*} [MeasurableSpace Λ] [MeasurableSpace ι]

theorem measurable_dyadicBlock_left (T : ℕ) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ dyadicBlock T p.1} := by
  have hf : Measurable fun p : ℝ × ℝ => ((⌊p.1 * 2 ^ T⌋ : ℤ) : ℝ) :=
    Measurable.of_discrete.comp ((measurable_fst.mul_const _).floor)
  exact (measurableSet_le (hf.div_const _) measurable_snd).inter
    (measurableSet_le measurable_snd ((hf.add_const _).div_const _))

theorem measurableSet_gridFit {β : Type*} [MeasurableSpace β] {G : Λ × ℝ → Fin 3 → ℝ}
    (hG : Measurable G) (M : ℕ) (η err : ℝ) (a : Fin 3 → Fin (M + 1) → ℤ) {f : β → Λ × ℝ}
    {g : β → ℝ} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {b | ∀ j, |G (f b) j - (gridPoly η (a j)).eval (g b)| ≤ err} := by
  have heq : {b | ∀ j, |G (f b) j - (gridPoly η (a j)).eval (g b)| ≤ err} =
      ⋂ j : Fin 3, {b | |G (f b) j - (gridPoly η (a j)).eval (g b)| ≤ err} := by
    ext b; simp
  rw [heq]
  exact MeasurableSet.iInter fun j => measurableSet_le
    ((((measurable_pi_apply j).comp hG).comp hf).sub
      ((gridPoly η (a j)).continuous.measurable.comp hg)).abs measurable_const

/-- The grid qualification test is measurable (a countable union over grid coordinates), for a
measurable reference, graph row and true label with a measurable diagonal. -/
theorem measurableSet_nativeGridQualified {Eref : Set (Λ × ℝ)} (hE : MeasurableSet Eref)
    {lab : Λ × ℝ → ι} (hlab : Measurable lab) (hdiag : MeasurableSet {q : ι × ι | q.1 = q.2})
    {G : Λ × ℝ → Fin 3 → ℝ} (hG : Measurable G) (M T : ℕ) (η : ℝ) (L : ℤ) (err dur : ℝ) :
    MeasurableSet {z | NativeGridQualified Eref lab G M T η L err dur z} := by
  have heq : {z | NativeGridQualified Eref lab G M T η L err dur z} =
      ⋃ a : Fin 3 → Fin (M + 1) → ℤ, {_z : Λ × ℝ | ∀ j k, |a j k| ≤ L} ∩
        ({z | ∀ j, |G z j - (gridPoly η (a j)).eval z.2| ≤ err} ∩
          {z | ENNReal.ofReal dur ≤ volume {v : ℝ | v ∈ dyadicBlock T z.2 ∧ (z.1, v) ∈ Eref ∧
            lab (z.1, v) = lab z ∧ ∀ j, |G (z.1, v) j - (gridPoly η (a j)).eval v| ≤ err}}) := by
    ext z
    simp only [NativeGridQualified, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  rw [heq]
  refine MeasurableSet.iUnion fun a => (MeasurableSet.const _).inter
    ((measurableSet_gridFit hG M η err a measurable_id measurable_snd).inter ?_)
  let S : Set ((Λ × ℝ) × ℝ) := {q | q.2 ∈ dyadicBlock T q.1.2 ∧ (q.1.1, q.2) ∈ Eref ∧
    lab (q.1.1, q.2) = lab q.1 ∧ ∀ j, |G (q.1.1, q.2) j - (gridPoly η (a j)).eval q.2| ≤ err}
  have hm1 : Measurable fun q : (Λ × ℝ) × ℝ => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hS : MeasurableSet S := by
    refine ((measurable_dyadicBlock_left T).preimage
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).inter
      ((hE.preimage hm1).inter ((hdiag.preimage ((hlab.comp hm1).prodMk
        (hlab.comp measurable_fst))).inter (measurableSet_gridFit hG M η err a hm1 measurable_snd)))
  exact measurableSet_le measurable_const (measurable_measure_prodMk_left hS)

end Measurability

/-- **Native polynomial qualification in a scalar-normal world** (paper, proof of
Prop. `a05:qualification`, the discovery step, `tex-06` l. 843–862), in the fixed-power form of
`HigherJetsStatement`: in every version-2 scalar-normal world `ScalarNormal ν cz E F piece K ζ d`
(zoomed coefficients `cz`) with the scales of the higher-jet theorem, if the row `F` represents the
tangential graph row (`|G z i.succ - F z.2 i| ≤ rowError` on `E`), the ORIGINAL coefficients `c`
of the lines (`x = c₀ + c₁ t + c₂ t²`, velocity `(1, c₄, c₆)`, `|c| ≤ B`) obey the velocity-graph
estimate `|x' - G · (1, V)| ≤ graphError` on `E`, and the true label `lab` is constant on each line
in each dyadic block of `E`, then some `z ∈ E` is natively qualified with coefficients
`≤ 3B + (1 + 2B) N^ε`, error `graphError + (1 + 2B)(rowError + h^(M + 1/8))` and duration
`≥ h N^(-ε)` (`h = 2⁻ᵀ`), with witness times labelled by `E` itself. -/
def NativeQualificationStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ M : ℕ, 2 ≤ M → ∀ c_h : ℝ, 0 < c_h →
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (cz : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ → ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
        ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → ScalarNormal ν cz E F piece K ζ d →
        ∀ (ι : Type) (lab : Λ × ℝ → ι) (c : Λ → Fin 7 → ℝ) (G : Λ × ℝ → Fin 3 → ℝ)
          (B graphError rowError : ℝ), 0 ≤ B →
        (∀ z ∈ E, ∀ i, |c z.1 i| ≤ B) →
        (∀ z ∈ E, |c z.1 1 + 2 * c z.1 2 * z.2 -
          (G z 0 + G z 1 * c z.1 4 + G z 2 * c z.1 6)| ≤ graphError) →
        (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ - F z.2 i| ≤ rowError) →
        (∀ z ∈ E, ∀ v, (z.1, v) ∈ E → v ∈ dyadicBlock T z.2 → lab (z.1, v) = lab z) →
        ∃ z ∈ E, NativeQualified E lab G M T (3 * B + (1 + 2 * B) * N ^ ε)
          (graphError + (1 + 2 * B) * (rowError + ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)))
          (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) z

/-- The higher jets give native qualification (`native_row_fit_of_jetFit` on the produced jet). -/
theorem nativeQualificationStatement_of_higherJets (hHJ : HigherJetsStatement) :
    NativeQualificationStatement := by
  intro d hd0 hd1 M hM c_h hch
  obtain ⟨c_ζ, hcζ, h1⟩ := hHJ d hd0 hd1 M hM c_h hch
  refine ⟨c_ζ, hcζ, fun ε hε => ?_⟩
  obtain ⟨α, hα, N₀, h2⟩ := h1 ε hε
  refine ⟨α, hα, max N₀ 1, le_max_right _ _, ?_⟩
  intro N hN Λ _ ν cz E F piece K ζ T hK hT1 hT2 hζ hSN ι lab c G B graphError rowError hB hcB
    hgraph hrow hlab
  obtain ⟨z, hz, P, hfit⟩ :=
    h2 N ((le_max_left _ _).trans hN) Λ ν cz E F piece K ζ T hK hT1 hT2 hζ hSN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNε : 0 ≤ N ^ ε := Real.rpow_nonneg (by linarith) ε
  obtain ⟨Q, hdeg, hcoef, hpt, hvol⟩ := native_row_fit_of_jetFit c G hM hB hNε hz (hcB z hz)
    (fun v hv => hgraph (z.1, v) hv) (fun v hv => hrow (z.1, v) hv) hfit
  refine ⟨z, hz, Q, hdeg, hcoef, hpt, hvol.trans (measure_mono ?_)⟩
  rintro v ⟨hvB, hvE, hvQ⟩
  exact ⟨hvB, hvE, hlab z hz v hvE hvB, hvQ⟩

/-- **No qualifying-failure world** (paper l. 857–862): an incidence produced in a world `E` lying
inside the reference `Eref` qualifies for the reference, so no world built inside the failure set
`{z | ¬ NativeGridQualified Eref …}` can produce one, for any grid bounds dominating the produced
fit (`Kq ≤ η (L - 1)`, `err + (M + 1) η ≤ err'`, `dur' ≤ dur`, reference times in `[0, 1]`). -/
theorem false_of_world_in_failure_set {Λ ι : Type*} {E Eref : Set (Λ × ℝ)}
    {lab : Λ × ℝ → ι} {G : Λ × ℝ → Fin 3 → ℝ} {M T : ℕ} {Kq err dur η err' dur' : ℝ} {L : ℤ}
    (hη : 0 < η) (hsub : E ⊆ Eref) (hEt : ∀ z ∈ Eref, z.2 ∈ Icc (0 : ℝ) 1)
    (hL : Kq ≤ η * (L - 1)) (herr : err + (M + 1) * η ≤ err') (hdur : dur' ≤ dur)
    (hfail : ∀ z ∈ E, ¬ NativeGridQualified Eref lab G M T η L err' dur' z)
    (hq : ∃ z ∈ E, NativeQualified E lab G M T Kq err dur z) : False := by
  obtain ⟨z, hz, hq⟩ := hq
  have hq' := hq.mono hsub le_rfl le_rfl hdur
  have hg := nativeGridQualified_of_nativeQualified hη (fun v hv => hEt (z.1, v) hv)
    (hEt z (hsub hz)) hq'
  apply hfail z hz
  obtain ⟨a, ha, hpt, hvol⟩ := hg
  have hceil : ⌈Kq / η⌉ + 1 ≤ L := by
    have h1 : Kq / η ≤ (L : ℝ) - 1 := by
      rw [div_le_iff₀ hη]; linarith
    have h2 : ⌈Kq / η⌉ ≤ L - 1 := by
      apply Int.ceil_le.mpr
      push_cast
      exact h1
    omega
  refine ⟨a, fun j k => (ha j k).trans hceil, fun j => (hpt j).trans herr,
    hvol.trans (measure_mono ?_)⟩
  rintro v ⟨hv1, hv2, hv3, hv4⟩
  exact ⟨hv1, hv2, hv3, fun j => (hv4 j).trans herr⟩

section Diagonal

/-- **The slow diagonal** (paper, end of the proof of Prop. `a05:qualification`): if for every
`r ≥ 1` the failure fractions `e r k` (at `ε = 1 / r`) eventually fall below every `δ > 0`, then
along some `R k → ∞` (slowly) the fractions `e (R k) k` tend to zero. -/
theorem exists_slow_diagonal (e : ℕ → ℕ → ℝ)
    (he : ∀ r, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, e r k ≤ δ) :
    ∃ R : ℕ → ℕ, (∀ k, 1 ≤ R k) ∧ Tendsto R atTop atTop ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, e (R k) k ≤ δ := by
  classical
  -- a threshold for `r`: beyond it the fraction at `r` is at most `1 / r`
  have hk : ∀ r : ℕ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → e (r + 1) k ≤ 1 / ((r : ℝ) + 1) := by
    intro r
    have := he (r + 1) (by omega) (1 / ((r : ℝ) + 1)) (by positivity)
    rw [eventually_atTop] at this
    obtain ⟨k₀, hk₀⟩ := this
    exact ⟨k₀, fun k hk => by exact_mod_cast hk₀ k hk⟩
  choose k₀ hk₀ using hk
  -- monotone thresholds, at least `r`
  let κ : ℕ → ℕ := fun r => (Finset.range (r + 1)).sup k₀ + r
  have hκ_ge : ∀ r, k₀ r ≤ κ r := fun r =>
    (Finset.le_sup (f := k₀) (Finset.mem_range.mpr (Nat.lt_succ_self r))).trans
      (Nat.le_add_right _ _)
  have hκ_r : ∀ r, r ≤ κ r := fun r => Nat.le_add_left _ _
  -- `R₀ k`: the largest `r ≤ k` whose threshold has passed
  let R₀ : ℕ → ℕ := fun k => Nat.findGreatest (fun r => κ r ≤ k) k
  have hR₀spec : ∀ k, κ 0 ≤ k → κ (R₀ k) ≤ k := fun k hk =>
    Nat.findGreatest_spec (P := fun r => κ r ≤ k) (Nat.zero_le k) hk
  have hR₀ge : ∀ r k, κ r ≤ k → r ≤ R₀ k := fun r k hk =>
    Nat.le_findGreatest ((hκ_r r).trans hk) hk
  refine ⟨fun k => R₀ k + 1, fun k => Nat.le_add_left _ _, ?_, ?_⟩
  · apply tendsto_atTop_atTop.mpr
    intro r
    exact ⟨κ r, fun k hk => (hR₀ge r k hk).trans (Nat.le_succ _)⟩
  · intro δ hδ
    obtain ⟨r₀, hr₀⟩ := exists_nat_one_div_lt hδ
    rw [eventually_atTop]
    refine ⟨max (κ 0) (κ r₀), fun k hk => ?_⟩
    have hk0 : κ 0 ≤ k := (le_max_left _ _).trans hk
    have hkr : κ r₀ ≤ k := (le_max_right _ _).trans hk
    have hspec := hR₀spec k hk0
    have hR : r₀ ≤ R₀ k := hR₀ge r₀ k hkr
    have hbound := hk₀ (R₀ k) k ((hκ_ge _).trans hspec)
    refine hbound.trans ?_
    have h1 : (r₀ : ℝ) + 1 ≤ (R₀ k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hR
    have h2 : 1 / ((R₀ k : ℝ) + 1) ≤ 1 / ((r₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) h1
    linarith

/-- Along a diagonal `R k → ∞`, the bound `N ^ (1 / R k)` is eventually below every fixed power
`N ^ ε` (`K_qual = N ^ (1 / r(N))` is a subpower). -/
theorem eventually_rpow_inv_le_rpow {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {N : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, N k ^ (1 / (R k : ℝ)) ≤ N k ^ ε := by
  obtain ⟨r₀, hr₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [hR.eventually_ge_atTop (r₀ + 1)] with k hk
  apply Real.rpow_le_rpow_of_exponent_le (hN k)
  have h1 : (r₀ : ℝ) + 1 ≤ (R k : ℝ) := by exact_mod_cast hk
  have h2 : 1 / (R k : ℝ) ≤ 1 / ((r₀ : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) h1
  linarith

end Diagonal

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
