-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/GridSeven.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/GridSeven.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenFromGroup

/-!
# Seven directions about any zoom centre, from breadth on a fixed cube grid

A producer knows breadth on a fixed grid of cube cells of side `ℓ`: in every cell the group's
events have a normalized velocity law that charges no strip of width `δ` by more than `κ` of the
cell's mass, and its velocity tail beyond `R` by at most `τ`. About any zoom centre `cz` whose
ball of radius `ρ` carries group mass at least `Mloc`, the grid cells of the index box of that
ball, zoomed by `λ`, are the cells of `seven_directions_of_group`; cells lighter than
`Mloc / (2 Nc)` (`Nc = (2ρ/ℓ + 2)³` bounds the number of cells) are dropped, and the retained
cells' own velocity laws, summed, are the common palette.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open GeneralPositionSampling
open scoped ENNReal

/-- The half-open grid cell of side `ℓ` with index `k`. -/
def gridCell (ℓ : ℝ) (k : Fin 3 → ℤ) : Set Base := {x | ∀ i, ⌊x i / ℓ⌋ = k i}

lemma measurableSet_gridCell (ℓ : ℝ) (k : Fin 3 → ℤ) : MeasurableSet (gridCell ℓ k) := by
  have : gridCell ℓ k = ⋂ i, (fun x : Base => ⌊x i / ℓ⌋) ⁻¹' {k i} := by
    ext x; simp [gridCell]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun x : Base => x i / ℓ) := by fun_prop
  exact (Int.measurable_floor.comp hm) (measurableSet_singleton _)

/-- The zoomed image of a grid cell. -/
def zoomedCell (cz : Fin 3 → ℝ) (lam ℓ : ℝ) (k : Fin 3 → ℤ) : Set Base :=
  {z | ∀ i, ⌊(cz i + z i / lam) / ℓ⌋ = k i}

lemma measurableSet_zoomedCell (cz : Fin 3 → ℝ) (lam ℓ : ℝ) (k : Fin 3 → ℤ) :
    MeasurableSet (zoomedCell cz lam ℓ k) := by
  have : zoomedCell cz lam ℓ k = ⋂ i, (fun z : Base => ⌊(cz i + z i / lam) / ℓ⌋) ⁻¹' {k i} := by
    ext z; simp [zoomedCell]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun z : Base => (cz i + z i / lam) / ℓ) := by fun_prop
  exact (Int.measurable_floor.comp hm) (measurableSet_singleton _)

lemma zoomMap_mem_zoomedCell_iff (cz : Fin 3 → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (ℓ : ℝ)
    (k : Fin 3 → ℤ) (x : Base) :
    zoomMap (WithLp.toLp 2 cz) lam x ∈ zoomedCell cz lam ℓ k ↔ x ∈ gridCell ℓ k := by
  have h : ∀ i, cz i + zoomMap (WithLp.toLp 2 cz) lam x i / lam = x i := by
    intro i
    simp only [zoomMap, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    simp
  simp only [zoomedCell, gridCell, mem_ofPred_eq, h]

lemma norm_le_sqrt_three_mul {z : Base} {r : ℝ} (h : ∀ i, |z i| ≤ r) :
    ‖z‖ ≤ Real.sqrt 3 * r := by
  have hr : 0 ≤ r := (abs_nonneg _).trans (h 0)
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖z i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin 3, r ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = Real.sqrt 3 * r := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hr]; norm_num

lemma lineDir_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (lam : ℝ) (l : Line) :
    lineDir (lam • M) l = lam • lineDir M l := by
  ext i; simp [lineDir]; ring

lemma lineVelocity_smul (M : Matrix (Fin 3) (Fin 3) ℝ) {lam : ℝ} (hlam : lam ≠ 0) (l : Line) :
    lineVelocity (lam • M) l = lineVelocity M l := by
  simp only [lineVelocity, lineDir_smul, PiLp.smul_apply, smul_eq_mul]
  congr 1
  ext i
  fin_cases i <;> simp [mul_div_mul_left _ _ hlam]

/-- The index box of the grid cells meeting the ball of radius `ρ` about `cz`. -/
def gridBox (cz : Fin 3 → ℝ) (ρ ℓ : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊(cz i - ρ) / ℓ⌋ ⌊(cz i + ρ) / ℓ⌋

lemma card_gridBox_le (cz : Fin 3 → ℝ) {ρ ℓ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < ℓ) :
    ((gridBox cz ρ ℓ).card : ℝ) ≤ (2 * ρ / ℓ + 2) ^ 3 := by
  rw [gridBox, Fintype.card_piFinset]
  push_cast
  rw [Fin.prod_univ_three]
  have hone : ∀ i, (((Finset.Icc ⌊(cz i - ρ) / ℓ⌋ ⌊(cz i + ρ) / ℓ⌋).card : ℕ) : ℝ) ≤
      2 * ρ / ℓ + 2 := by
    intro i
    rw [Int.card_Icc]
    have h1 : (⌊(cz i + ρ) / ℓ⌋ : ℝ) ≤ (cz i + ρ) / ℓ := Int.floor_le _
    have h2 : (cz i - ρ) / ℓ - 1 < (⌊(cz i - ρ) / ℓ⌋ : ℝ) := Int.sub_one_lt_floor _
    have hle : ⌊(cz i - ρ) / ℓ⌋ ≤ ⌊(cz i + ρ) / ℓ⌋ + 1 := by
      have : ⌊(cz i - ρ) / ℓ⌋ ≤ ⌊(cz i + ρ) / ℓ⌋ :=
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hℓ.le)
      omega
    have hn0 : 0 ≤ ⌊(cz i + ρ) / ℓ⌋ + 1 - ⌊(cz i - ρ) / ℓ⌋ := by omega
    have hcast : (((⌊(cz i + ρ) / ℓ⌋ + 1 - ⌊(cz i - ρ) / ℓ⌋).toNat : ℕ) : ℝ) =
        ((⌊(cz i + ρ) / ℓ⌋ + 1 - ⌊(cz i - ρ) / ℓ⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn0]
    rw [hcast]
    push_cast
    have hsplit : (cz i + ρ) / ℓ - ((cz i - ρ) / ℓ - 1) + 1 = 2 * ρ / ℓ + 2 := by
      field_simp; ring
    linarith
  have h0 : ∀ i, (0 : ℝ) ≤ (((Finset.Icc ⌊(cz i - ρ) / ℓ⌋ ⌊(cz i + ρ) / ℓ⌋).card : ℕ) : ℝ) :=
    fun i => Nat.cast_nonneg _
  calc _ ≤ (2 * ρ / ℓ + 2) * (2 * ρ / ℓ + 2) * (2 * ρ / ℓ + 2) := by
        apply mul_le_mul (mul_le_mul (hone 0) (hone 1) (h0 1) (by positivity)) (hone 2) (h0 2)
          (by positivity)
    _ = _ := by ring

lemma mem_gridBox_of_mem_ball {cz : Fin 3 → ℝ} {ρ ℓ : ℝ} (hℓ : 0 < ℓ) {x : Base}
    (hx : x ∈ ball (WithLp.toLp 2 cz) ρ) :
    (fun i => ⌊x i / ℓ⌋) ∈ gridBox cz ρ ℓ := by
  rw [gridBox, Fintype.mem_piFinset]
  intro i
  rw [mem_ball, dist_eq_norm] at hx
  have hi : |x i - cz i| < ρ := by
    have := (PiLp.norm_apply_le (x - WithLp.toLp 2 cz) i).trans_lt hx
    simpa using this
  rw [abs_lt] at hi
  refine Finset.mem_Icc.mpr ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hℓ.le
  · exact div_le_div_of_nonneg_right (by linarith) hℓ.le

lemma abs_sub_of_mem_gridBox {cz : Fin 3 → ℝ} {ρ ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 3 → ℤ}
    (hk : k ∈ gridBox cz ρ ℓ) {x : Base} (hx : x ∈ gridCell ℓ k) (i : Fin 3) :
    |x i - cz i| ≤ ρ + ℓ := by
  rw [gridBox, Fintype.mem_piFinset] at hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (hk i)
  have hxi := hx i
  have h1 : (k i : ℝ) ≤ x i / ℓ := by rw [← hxi]; exact Int.floor_le _
  have h2 : x i / ℓ < k i + 1 := by rw [← hxi]; exact Int.lt_floor_add_one _
  have h3 : (cz i - ρ) / ℓ - 1 < (k i : ℝ) := by
    have := Int.sub_one_lt_floor ((cz i - ρ) / ℓ)
    have h' : (⌊(cz i - ρ) / ℓ⌋ : ℝ) ≤ k i := by exact_mod_cast hlo
    linarith
  have h4 : (k i : ℝ) ≤ (cz i + ρ) / ℓ := by
    have h' : (k i : ℝ) ≤ ⌊(cz i + ρ) / ℓ⌋ := by exact_mod_cast hhi
    exact h'.trans (Int.floor_le _)
  have e1 : x i < (k i + 1) * ℓ := by
    have := (div_lt_iff₀ hℓ).mp h2; linarith
  have e2 : (k i) * ℓ ≤ x i := by
    have := (le_div_iff₀ hℓ).mp h1; linarith
  have e3 : (cz i - ρ) - ℓ < k i * ℓ := by
    have := (div_lt_iff₀ hℓ).mp (by linarith : (cz i - ρ) / ℓ < k i + 1)
    nlinarith
  have e4 : k i * ℓ ≤ cz i + ρ := by
    have := (le_div_iff₀ hℓ).mp h4; linarith
  rw [abs_le]; constructor <;> nlinarith

/-- **Seven directions about a zoom centre from grid breadth.** -/
theorem seven_directions_near_centre {c₁ c₁' : Fin 3 → ℝ} {M₁ M₁' : Matrix (Fin 3) (Fin 3) ℝ}
    {B B' : ℝ} (hM : M₁' * M₁ = 1) (hc : ∀ k, c₁' k = -∑ i : Fin 3, M₁' k i * c₁ i)
    (hB : B' * B = 1) {R0 Rc : Poly} {Pot : MvPolynomial (Fin 3) ℝ}
    {εfit A₁ σ Vc At A0 θ h τw lam ℓ ρ β Mloc Mtot : ℝ} (cz : Fin 3 → ℝ)
    (hlam : 0 < lam) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hMloc : 0 < Mloc) (hβ : 0 < β)
    (μ0 : Measure Event) (Gev : Set Event) (hGm : MeasurableSet Gev)
    (hline : ∀ p ∈ Gev, 0 < lineDir M₁ p.1 0 ∧ (8 * At * (lam * lineDir M₁ p.1 0))⁻¹ ≤ τw ∧
      ∀ s, |s - p.2| ≤ τw → PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint p.1 s))
    (hdens : ∀ U : Set Base, MeasurableSet U →
      μ0 (Gev ∩ (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹' U) ≤
        ENNReal.ofReal β * volume U)
    (htot : μ0 Gev ≤ ENNReal.ofReal Mtot)
    (hloc : ENNReal.ofReal Mloc ≤ μ0 (Gev ∩
      (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹' ball (WithLp.toLp 2 cz) ρ))
    {δ R w : ℝ} (hδ : 0 < δ) (hw : 0 < w) {κ τ : ℝ≥0∞}
    (hb : ∀ (k : Fin 3 → ℤ) (m : EuclideanSpace ℝ (Fin 2)) (c₀ : ℝ), ‖m‖ = 1 →
      μ0 (Gev ∩ (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹' gridCell ℓ k ∩
        (fun p : Event => lineVelocity M₁ p.1) ⁻¹' {x | |inner ℝ m x - c₀| ≤ δ}) ≤
      κ * μ0 (Gev ∩ (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹'
        gridCell ℓ k))
    (htail : ∀ k : Fin 3 → ℤ,
      μ0 (Gev ∩ (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹' gridCell ℓ k ∩
        (fun p : Event => lineVelocity M₁ p.1) ⁻¹' {v | R < ‖v‖}) ≤
      τ * μ0 (Gev ∩ (fun p : Event => normalizedBase c₁ M₁ B (graphPoint p.1 p.2)) ⁻¹'
        gridCell ℓ k))
    (hgood : 686 * κ + 7 * τ < 1)
    (hAt : 0 ≤ At) (hR : 1 + 2 * (R + w) ^ 2 ≤ At ^ 2) (hch : Real.sqrt 3 * (lam * ℓ) ≤ h)
    (hwh : w ≤ h) (hθ1 : θ ≤ 1)
    (hdetA : A0⁻¹ ≤ δ ^ 2 - 4 * w * (2 * R + w / 2))
    (hball : Real.sqrt 3 * (lam * (ρ + ℓ)) ≤ 1)
    (hvolA : 2 * ENNReal.ofReal (2 * (2 * ρ / ℓ + 2) ^ 3 / Mloc) ^ 7 *
        (ENNReal.ofReal (β / lam ^ 3) * ENNReal.ofReal A0⁻¹) * ENNReal.ofReal Mtot ^ 6 ≤
      1 - (686 * κ + 7 * τ)) :
    ∃ (p : Fin 7 → Base) (E : Set Base),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) ∧
      (∀ i k l : Fin 7, i ≠ k → i ≠ l → k ≠ l →
        A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p k, p l] r) t)|) ∧
      MeasurableSet E ∧ E ⊆ closedBall (0 : Base) 1 ∧ ENNReal.ofReal A0⁻¹ ≤ volume E ∧
      ∀ u ∈ E, ∀ i, CertifiedTubeWitness
        (transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' lam) B' R0)
        (basePullback (zoomShift c₁' M₁' cz) (zoomMatrix M₁' lam) Pot)
        (transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' lam) B' Rc)
        εfit A₁ σ Vc At θ h u (p i) := by
  classical
  set cube : Event → Base := fun p => normalizedBase c₁ M₁ B (graphPoint p.1 p.2) with hcube
  have hcubem : Measurable cube := measurable_eventBase c₁ M₁ B
  set vel : Event → EuclideanSpace ℝ (Fin 2) := fun p => lineVelocity M₁ p.1 with hvel
  have hvelm : Measurable vel := measurable_lineVelocity M₁
  set m : (Fin 3 → ℤ) → ℝ≥0∞ := fun k => μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k) with hmdef
  set S := gridBox cz ρ ℓ with hS
  set Nc : ℝ := (2 * ρ / ℓ + 2) ^ 3 with hNc
  have hNc0 : 0 < Nc := by positivity
  set floor : ℝ := Mloc / (2 * Nc) with hfloor
  have hfloor0 : 0 < floor := by positivity
  set Sret := S.filter (fun k => ENNReal.ofReal floor ≤ m k) with hSret
  -- the retained cells carry at least half of the local mass
  have hcover : ENNReal.ofReal Mloc ≤ ∑ k ∈ S, m k := by
    refine hloc.trans ((measure_mono ?_).trans (measure_biUnion_finset_le S _))
    intro p hp
    have hk := mem_gridBox_of_mem_ball hℓ hp.2
    refine mem_iUnion₂.mpr ⟨_, hk, hp.1, ?_⟩
    intro i
    rfl
  have hdrop : ∑ k ∈ S.filter (fun k => ¬ ENNReal.ofReal floor ≤ m k), m k ≤
      ENNReal.ofReal (Mloc / 2) := by
    calc ∑ k ∈ S.filter (fun k => ¬ ENNReal.ofReal floor ≤ m k), m k
        ≤ ∑ _k ∈ S.filter (fun k => ¬ ENNReal.ofReal floor ≤ m k), ENNReal.ofReal floor :=
          Finset.sum_le_sum fun k hk => (not_le.mp (Finset.mem_filter.mp hk).2).le
      _ ≤ ∑ _k ∈ S, ENNReal.ofReal floor :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (S.card : ℝ≥0∞) * ENNReal.ofReal floor := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal Nc * ENNReal.ofReal floor := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (card_gridBox_le cz hρ.le hℓ)
      _ = ENNReal.ofReal (Mloc / 2) := by
          rw [← ENNReal.ofReal_mul hNc0.le, hfloor]
          congr 1
          field_simp
  have hret : ENNReal.ofReal (Mloc / 2) ≤ ∑ k ∈ Sret, m k := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => ENNReal.ofReal floor ≤ m k) m
    have hhalf : ENNReal.ofReal Mloc = ENNReal.ofReal (Mloc / 2) + ENNReal.ofReal (Mloc / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    have h1 : ENNReal.ofReal (Mloc / 2) + ENNReal.ofReal (Mloc / 2) ≤
        ∑ k ∈ Sret, m k + ENNReal.ofReal (Mloc / 2) := by
      rw [← hhalf]
      calc ENNReal.ofReal Mloc ≤ ∑ k ∈ S, m k := hcover
        _ = ∑ k ∈ Sret, m k + ∑ k ∈ S.filter (fun k => ¬ ENNReal.ofReal floor ≤ m k), m k :=
            hsplit.symm
        _ ≤ ∑ k ∈ Sret, m k + ENNReal.ofReal (Mloc / 2) := add_le_add le_rfl hdrop
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1
  -- the cells
  let ι := {k // k ∈ Sret}
  have hne : Nonempty ι := by
    by_contra hempty
    have hSret0 : Sret = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro k hk
      exact hempty ⟨⟨k, hk⟩⟩
    rw [hSret0, Finset.sum_empty] at hret
    exact absurd (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < Mloc / 2)) (not_lt.mpr hret)
  set cell : ι → Set Base := fun k => zoomedCell cz lam ℓ k.1 with hcelldef
  have hlamne : lam ≠ 0 := hlam.ne'
  set cZ := zoomForwardShift c₁ cz lam with hcZ
  set MZ : Matrix (Fin 3) (Fin 3) ℝ := lam • M₁ with hMZ
  obtain ⟨hMinvZ, hcinvZ⟩ := zoomForward_inverse hM hc cz hlamne
  have hzoomEv : ∀ (k : Fin 3 → ℤ),
      Gev ∩ (fun p : Event => normalizedBase cZ MZ B (graphPoint p.1 p.2)) ⁻¹'
        zoomedCell cz lam ℓ k = Gev ∩ cube ⁻¹' gridCell ℓ k := by
    intro k
    ext p
    simp only [mem_inter_iff, mem_preimage, hcZ, hMZ, normalizedBase_zoom]
    rw [zoomMap_mem_zoomedCell_iff cz hlamne ℓ k]
  have hvelZ : (fun p : Event => lineVelocity MZ p.1) = vel := by
    funext p
    exact lineVelocity_smul M₁ hlamne p.1
  -- palette: the sum of the retained cells' velocity laws
  set π : Measure (EuclideanSpace ℝ (Fin 2)) :=
    ∑ k : ι, (μ0.restrict (Gev ∩ cube ⁻¹' gridCell ℓ k.1)).map vel with hπdef
  have hGk : ∀ k : Fin 3 → ℤ, MeasurableSet (Gev ∩ cube ⁻¹' gridCell ℓ k) :=
    fun k => hGm.inter (hcubem (measurableSet_gridCell ℓ k))
  have hmk_le : ∀ k : Fin 3 → ℤ, m k ≤ ENNReal.ofReal Mtot :=
    fun k => (measure_mono inter_subset_left).trans htot
  have hπU : ∀ U, MeasurableSet U →
      π U = ∑ k : ι, μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k.1 ∩ vel ⁻¹' U) := by
    intro U hU
    rw [hπdef, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.map_apply hvelm hU, Measure.restrict_apply (hvelm hU), inter_comm]
  have hπuniv : π univ = ∑ k : ι, m k.1 := by
    rw [hπU univ MeasurableSet.univ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [preimage_univ, inter_univ]
  have hsumι : ∑ k : ι, m k.1 = ∑ k ∈ Sret, m k := by
    rw [← Finset.sum_coe_sort Sret]
  have : IsFiniteMeasure π := by
    constructor
    rw [hπuniv, hsumι]
    exact ENNReal.sum_lt_top.mpr fun k _ => (hmk_le k).trans_lt ENNReal.ofReal_lt_top
  have hπ0 : π univ ≠ 0 := by
    rw [hπuniv, hsumι]
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < Mloc / 2))
      hret).ne'
  set K : ℝ≥0∞ := ENNReal.ofReal (2 * Nc / Mloc) with hKdef
  have hKm : ∀ k : ι, 1 ≤ K * m k.1 := by
    intro k
    have hk := (Finset.mem_filter.mp k.2).2
    calc (1 : ℝ≥0∞) = K * ENNReal.ofReal floor := by
          rw [hKdef, ← ENNReal.ofReal_mul (by positivity), hfloor]
          rw [show 2 * Nc / Mloc * (Mloc / (2 * Nc)) = 1 by field_simp]
          simp
      _ ≤ K * m k.1 := by gcongr
  have hSretS : ∀ k : ι, k.1 ∈ S := fun k => (Finset.mem_filter.mp k.2).1
  have hcellBall : ∀ k : ι, cell k ⊆ closedBall (0 : Base) 1 := by
    intro k z hz
    set x : Base := WithLp.toLp 2 (fun i => cz i + z i / lam) with hx
    have hxcell : x ∈ gridCell ℓ k.1 := fun i => hz i
    have hzi : ∀ i, |z i| ≤ lam * (ρ + ℓ) := by
      intro i
      have h1 := abs_sub_of_mem_gridBox hℓ (hSretS k) hxcell i
      have hxi : x i - cz i = z i / lam := by simp [hx]
      rw [hxi, abs_div, abs_of_pos hlam, div_le_iff₀ hlam] at h1
      linarith
    rw [mem_closedBall, dist_zero_right]
    exact (norm_le_sqrt_three_mul hzi).trans (by nlinarith [Real.sqrt_nonneg 3])
  have hdiam : ∀ k : ι, ∀ u ∈ cell k, ∀ y ∈ cell k, ‖u - y‖ ≤ Real.sqrt 3 * (lam * ℓ) := by
    intro k u hu y hy
    apply norm_le_sqrt_three_mul
    intro i
    have hfl : ⌊(cz i + u i / lam) / ℓ⌋ = ⌊(cz i + y i / lam) / ℓ⌋ := (hu i).trans (hy i).symm
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have heq : (cz i + u i / lam) / ℓ - (cz i + y i / lam) / ℓ = (u i - y i) / (lam * ℓ) := by
      field_simp; ring
    rw [heq, abs_div, abs_of_pos (by positivity : 0 < lam * ℓ), div_lt_one (by positivity)] at h1
    simpa using h1.le
  have hdisj : Pairwise (Function.onFun Disjoint cell) := by
    intro k k' hkk'
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    apply hkk'
    apply Subtype.ext
    funext i
    exact (hz i).symm.trans (hz' i)
  have hmpos : ∀ k : ι, m k.1 ≠ 0 := by
    intro k
    have hk := (Finset.mem_filter.mp k.2).2
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hfloor0) hk).ne'
  have hX : ∑ k : ι, m k.1 ≤ ENNReal.ofReal Mtot := by
    rw [hsumι]
    have hdisjS : (Sret : Set (Fin 3 → ℤ)).PairwiseDisjoint (fun k => Gev ∩ cube ⁻¹' gridCell ℓ k) := by
      intro k _ k' _ hkk'
      rw [Function.onFun, Set.disjoint_left]
      intro p hp hp'
      apply hkk'
      funext i
      exact (hp.2 i).symm.trans (hp'.2 i)
    rw [← measure_biUnion_finset hdisjS (fun k _ => hGk k)]
    exact (measure_mono (iUnion₂_subset fun k _ => inter_subset_left)).trans htot
  have hX0 : ∑ k : ι, m k.1 ≠ 0 := by
    rw [hsumι]
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < Mloc / 2))
      hret).ne'
  have hXtop : ∑ k : ι, m k.1 ≠ ∞ := (hX.trans_lt ENNReal.ofReal_lt_top).ne
  refine seven_directions_of_group (c := cZ) (M := MZ) (B := B) (τw := τw) hMinvZ hcinvZ hB μ0 Gev hGm ?_
    cell (fun k => measurableSet_zoomedCell cz lam ℓ k.1) hdisj hcellBall hdiam ?_ ?_
    (ENNReal.ofReal (β / lam ^ 3)) ?_ π hπ0 (K := K) ENNReal.ofReal_ne_top ?_ hδ hw ?_ ?_ hgood hne
    hAt hR hch hwh hθ1 hdetA ?_ (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · intro p hp
    obtain ⟨h0, h1, h2⟩ := hline p hp
    have hdir : lineDir MZ p.1 0 = lam * lineDir M₁ p.1 0 := by
      rw [hMZ, lineDir_smul]; rfl
    refine ⟨?_, ?_, h2⟩
    · rw [hdir]; exact mul_pos hlam h0
    · rw [hdir]; exact h1
  · intro k
    rw [hzoomEv]
    exact hmpos k
  · intro k
    rw [hzoomEv]
    exact ((hmk_le k.1).trans_lt ENNReal.ofReal_lt_top).ne
  · intro k
    rw [hzoomEv]
    have hpre : gridCell ℓ k.1 = zoomMap (WithLp.toLp 2 cz) lam ⁻¹' cell k := by
      ext x
      exact (zoomMap_mem_zoomedCell_iff cz hlamne ℓ k.1 x).symm
    calc m k.1 ≤ ENNReal.ofReal β * volume (gridCell ℓ k.1) :=
          hdens _ (measurableSet_gridCell ℓ k.1)
      _ = ENNReal.ofReal β * (ENNReal.ofReal (lam ^ 3)⁻¹ * volume (cell k)) := by
          rw [hpre, volume_preimage_zoomMap _ hlam]
      _ = ENNReal.ofReal (β / lam ^ 3) * volume (cell k) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hβ.le, div_eq_mul_inv]
  · intro k U hU
    rw [hzoomEv, hvelZ]
    have hsingle : μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k.1 ∩ vel ⁻¹' U) ≤ π U := by
      rw [hπU U hU]
      exact Finset.single_le_sum (f := fun k : ι => μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k.1 ∩ vel ⁻¹' U))
        (fun _ _ => bot_le) (Finset.mem_univ k)
    calc μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k.1 ∩ vel ⁻¹' U) ≤ 1 * π U := by rw [one_mul]; exact hsingle
      _ ≤ (K * m k.1) * π U := by gcongr; exact hKm k
      _ = K * π U * μ0 (Gev ∩ cube ⁻¹' gridCell ℓ k.1) := by ring
  · intro k mv c₀ hmv
    rw [hzoomEv, hvelZ]
    exact hb k.1 mv c₀ hmv
  · intro k
    rw [hzoomEv, hvelZ]
    exact htail k.1
  · -- the volume budget
    have hsumZ : ∑ k : ι, μ0 (Gev ∩ (fun p : Event => normalizedBase cZ MZ B (graphPoint p.1 p.2)) ⁻¹'
        cell k) = ∑ k : ι, m k.1 := Finset.sum_congr rfl fun k _ => by rw [hzoomEv]
    rw [hsumZ, hπuniv]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ hX0)) (Or.inl (ENNReal.pow_ne_top hXtop))]
    calc 2 * K ^ 7 * (ENNReal.ofReal (β / lam ^ 3) * ENNReal.ofReal A0⁻¹) *
          (∑ k : ι, m k.1) ^ 7
        = (2 * K ^ 7 * (ENNReal.ofReal (β / lam ^ 3) * ENNReal.ofReal A0⁻¹) *
          (∑ k : ι, m k.1) ^ 6) * (∑ k : ι, m k.1) := by ring
      _ ≤ (2 * K ^ 7 * (ENNReal.ofReal (β / lam ^ 3) * ENNReal.ofReal A0⁻¹) *
          ENNReal.ofReal Mtot ^ 6) * (∑ k : ι, m k.1) := by gcongr
      _ ≤ (1 - (686 * κ + 7 * τ)) * (∑ k : ι, m k.1) := by gcongr

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
