import Mathlib

/-!
# Polynomial sublevel mass from floor-cell ceilings

A measure on the plane that is only known to put mass at most `m` on each
floor cell of side `w` (no density) still gives a polynomial sublevel set
small mass: every cell meeting the sublevel set lies in a slightly enlarged
sublevel set, so the number of such cells is controlled by its volume.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial

/-- The floor cell of side `w` and integer index `q` in the plane. -/
def floorCell (w : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {z | (fun e => ⌊z e / w⌋) = q}

theorem mem_floorCell_iff {w : ℝ} (hw : 0 < w) (q : Fin 2 → ℤ) (z : Fin 2 → ℝ) :
    z ∈ floorCell w q ↔ ∀ e, (q e : ℝ) * w ≤ z e ∧ z e < ((q e : ℝ) + 1) * w := by
  constructor
  · intro hz e
    have h : ⌊z e / w⌋ = q e := congrFun hz e
    rw [Int.floor_eq_iff] at h
    constructor
    · have := h.1
      rwa [le_div_iff₀ hw] at this
    · have := h.2
      rwa [div_lt_iff₀ hw] at this
  · intro hz
    funext e
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hw]
      exact (hz e).1
    · rw [div_lt_iff₀ hw]
      exact (hz e).2

theorem floorCell_eq_pi {w : ℝ} (hw : 0 < w) (q : Fin 2 → ℤ) :
    floorCell w q = Set.pi univ (fun e => Ico ((q e : ℝ) * w) (((q e : ℝ) + 1) * w)) := by
  ext z
  rw [mem_floorCell_iff hw]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]

theorem measurableSet_floorCell {w : ℝ} (hw : 0 < w) (q : Fin 2 → ℤ) :
    MeasurableSet (floorCell w q) := by
  rw [floorCell_eq_pi hw]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_floorCell {w : ℝ} (hw : 0 < w) (q : Fin 2 → ℤ) :
    volume (floorCell w q) = ENNReal.ofReal (w ^ 2) := by
  rw [floorCell_eq_pi hw, Real.volume_pi_Ico]
  have hlen (e : Fin 2) : ((q e : ℝ) + 1) * w - (q e : ℝ) * w = w := by ring
  simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hw.le]

theorem floorCell_pairwiseDisjoint (w : ℝ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (floorCell w q) (floorCell w q')) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hqq' (hz.symm.trans hz')

/-- Two points of one floor cell differ by less than its side in every coordinate. -/
theorem abs_sub_lt_of_mem_floorCell {w : ℝ} (hw : 0 < w) {q : Fin 2 → ℤ}
    {z z' : Fin 2 → ℝ} (hz : z ∈ floorCell w q) (hz' : z' ∈ floorCell w q) (e : Fin 2) :
    |z e - z' e| < w := by
  rw [mem_floorCell_iff hw] at hz hz'
  rw [abs_lt]
  constructor
  · nlinarith [(hz e).1, (hz e).2, (hz' e).1, (hz' e).2]
  · nlinarith [(hz e).1, (hz e).2, (hz' e).1, (hz' e).2]

/-- Floor indices of points of the half box are bounded. -/
theorem floor_index_bound {w : ℝ} (hw : 0 < w) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(⌊t / w⌋ : ℤ)| ≤ (⌈1 / w⌉₊ : ℤ) + 1 := by
  have hc : (1 / w : ℝ) ≤ ⌈1 / w⌉₊ := Nat.le_ceil _
  have htw : |t / w| ≤ 1 / w := by
    rw [abs_div, abs_of_pos hw]
    apply div_le_div_of_nonneg_right _ hw.le
    linarith
  rw [abs_le] at htw ⊢
  constructor
  · have h1 : (-(⌈1 / w⌉₊ : ℝ) - 1 : ℝ) < ⌊t / w⌋ := by
      have := Int.sub_one_lt_floor (t / w)
      linarith
    have h2 : ((-((⌈1 / w⌉₊ : ℤ) + 1) : ℤ) : ℝ) < ⌊t / w⌋ := by
      push_cast
      linarith
    exact_mod_cast h2.le
  · have h1 : (⌊t / w⌋ : ℝ) ≤ t / w := Int.floor_le _
    have h2 : ((⌊t / w⌋ : ℤ) : ℝ) ≤ (((⌈1 / w⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2

/-- **Cell sublevel bound.** A measure with mass at most `m` on every floor cell
of side `w ≤ 1/2` gives the sublevel set of a Lipschitz polynomial on the half
box mass at most `m / w²` times the volume of a slightly enlarged sublevel set
in the unit box. No measurability of the tested events is required. -/
theorem cell_sublevel_mass_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (base : α → Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ) {w m s L : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1 / 2) (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hcell : ∀ q : Fin 2 → ℤ, μ {a | (fun e => ⌊base a e / w⌋) = q} ≤ ENNReal.ofReal m)
    (hLip : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, ∀ z' ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z P - eval z' P| ≤ L * (|z 0 - z' 0| + |z 1 - z' 1|)) :
    μ {a | base a ∈ Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) ∧ |eval (base a) P| ≤ s} ≤
      ENNReal.ofReal (m / w ^ 2) *
        volume {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval z P| ≤ s + 2 * L * w} := by
  classical
  set M : ℤ := (⌈1 / w⌉₊ : ℤ) + 1 with hMdef
  let bad₀ : Set (Fin 2 → ℝ) := {z | z ∈ Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) ∧ |eval z P| ≤ s}
  let bad₁ : Set (Fin 2 → ℝ) := {z | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval z P| ≤ s + 2 * L * w}
  let box : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-M) M
  let G : Finset (Fin 2 → ℤ) := box.filter fun q => (floorCell w q ∩ bad₀).Nonempty
  -- (a) the bad events are covered by the preimages of the cells of `G`
  have hcover : {a | base a ∈ Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) ∧ |eval (base a) P| ≤ s} ⊆
      ⋃ q ∈ G, {a | (fun e => ⌊base a e / w⌋) = q} := by
    intro a ha
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun e => ⌊base a e / w⌋, ?_, rfl⟩
    simp only [G, box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun e => ?_, ⟨base a, rfl, ha⟩⟩
    have he : |base a e| ≤ 1 / 2 := by
      rw [abs_le]
      have h1 := ha.1.1 e
      have h2 := ha.1.2 e
      constructor <;> linarith
    have hb := floor_index_bound hw he
    rw [abs_le] at hb
    exact ⟨hb.1, hb.2⟩
  -- (b) every cell of `G` lies in the enlarged sublevel set
  have hsub : ∀ q ∈ G, floorCell w q ⊆ bad₁ := by
    intro q hq z hz
    simp only [G, Finset.mem_filter] at hq
    obtain ⟨z₀, hz₀c, hz₀⟩ := hq.2
    have hdist (e : Fin 2) : |z e - z₀ e| < w := abs_sub_lt_of_mem_floorCell hw hz hz₀c e
    have hz₀e (e : Fin 2) : |z₀ e| ≤ 1 / 2 := by
      have h1 := hz₀.1.1 e
      have h2 := hz₀.1.2 e
      rw [abs_le]
      constructor <;> linarith
    have hze (e : Fin 2) : |z e| ≤ 1 := by
      have h := abs_sub_abs_le_abs_sub (z e) (z₀ e)
      linarith [hdist e, hz₀e e]
    have hzbox : z ∈ Icc (-1 : Fin 2 → ℝ) 1 :=
      ⟨fun e => by have := (abs_le.mp (hze e)).1; simpa using this,
        fun e => by have := (abs_le.mp (hze e)).2; simpa using this⟩
    have hz₀box : z₀ ∈ Icc (-1 : Fin 2 → ℝ) 1 :=
      ⟨fun e => by have := (abs_le.mp (hz₀e e)).1; simp; linarith,
        fun e => by have := (abs_le.mp (hz₀e e)).2; simp; linarith⟩
    refine ⟨hzbox, ?_⟩
    have hvar := hLip z hzbox z₀ hz₀box
    have h0 := hdist 0
    have h1 := hdist 1
    have hsum : L * (|z 0 - z₀ 0| + |z 1 - z₀ 1|) ≤ 2 * L * w := by nlinarith
    have htri := abs_sub_abs_le_abs_sub (eval z P) (eval z₀ P)
    linarith [hz₀.2]
  -- (c) counting the cells of `G` by volume
  have hcount : (G.card : ENNReal) * ENNReal.ofReal (w ^ 2) ≤ volume bad₁ := by
    have hunion : volume (⋃ q ∈ G, floorCell w q) = ∑ q ∈ G, volume (floorCell w q) := by
      apply measure_biUnion_finset
      · intro q _ q' _ hqq'
        exact floorCell_pairwiseDisjoint w hqq'
      · intro q _
        exact measurableSet_floorCell hw q
    have hle : volume (⋃ q ∈ G, floorCell w q) ≤ volume bad₁ :=
      measure_mono (Set.iUnion₂_subset hsub)
    rw [hunion] at hle
    simp only [volume_floorCell hw, Finset.sum_const, nsmul_eq_mul] at hle
    exact hle
  -- (d) the mass of the bad events
  have hmass : μ {a | base a ∈ Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) ∧ |eval (base a) P| ≤ s} ≤
      (G.card : ENNReal) * ENNReal.ofReal m := by
    calc
      _ ≤ μ (⋃ q ∈ G, {a | (fun e => ⌊base a e / w⌋) = q}) := measure_mono hcover
      _ ≤ ∑ q ∈ G, μ {a | (fun e => ⌊base a e / w⌋) = q} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _q ∈ G, ENNReal.ofReal m := Finset.sum_le_sum fun q _ => hcell q
      _ = (G.card : ENNReal) * ENNReal.ofReal m := by simp
  -- (e) combine
  have hw2 : 0 < w ^ 2 := by positivity
  have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m / w ^ 2) * ENNReal.ofReal (w ^ 2) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hm hw2.le), div_mul_cancel₀ m hw2.ne']
  calc
    _ ≤ (G.card : ENNReal) * ENNReal.ofReal m := hmass
    _ = ENNReal.ofReal (m / w ^ 2) * ((G.card : ENNReal) * ENNReal.ofReal (w ^ 2)) := by
      rw [hsplit]
      ring
    _ ≤ ENNReal.ofReal (m / w ^ 2) * volume bad₁ := by gcongr

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
