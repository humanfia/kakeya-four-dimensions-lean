import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Collision

/- Adapted from this LOT tree (oai_074_kakeya_four_dimensions), obligation o217
(`k4_horizontal_endpoint_parameter_bootstrap`), branch `x0763` at commit `ade0f356`, file
`Submission/Obl/k4_horizontal_endpoint_parameter_bootstrap/FirstJet/Concentrate.lean`, written by
session x0763 for this tree from the paper (Proposition 5.4); only the namespace is changed. -/

/-!
# The slope-concentration inequality

The elementary core of "Concentrating the residual slopes" in the proof of paper
Proposition 5.4 (`prop:scalar-normal`). Labeled incidences `(l,u) ∈ E` carry a scalar
`L l u` within `e` of a line `z l + u k l`; at every time the scalar meets at most `C₁`
bins of width `p`; a cap bounds the mass of a (cell, bin) at a time by `C₂`; and
trajectories whose slopes are `w`-close to that of `l` lie in at most `Ncells` cells.
Then the labeled mass `M = (ν ⊗ dt)(E)` obeys

`M² ≤ C₁ (C₂ Ncells M + (2(p+2e)/w) ν(Ω)²)`.

Collisions (pairs in a common bin at a common time) are at least `M²/C₁` by
Cauchy–Schwarz; close-slope collisions are paid by the cap, far-slope ones by the short
time during which two lines with slopes `w` apart stay within `p + 2e`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- `(∫ g)² ≤ ∫ g²` for a measure of total mass at most one. -/
theorem sq_lintegral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (hμ : μ Set.univ ≤ 1)
    {g : X → ENNReal} (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ) ^ 2 ≤ ∫⁻ x, g x ^ 2 ∂μ := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h1 : (μ Set.univ) ^ (1 / (2:ℝ)) ≤ 1 := ENNReal.rpow_le_one hμ (by norm_num)
  have h2 : (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, g x ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := by
    calc (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, g x ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * (μ Set.univ) ^ (1 / (2:ℝ)) := h
      _ ≤ (∫⁻ x, g x ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * 1 := by gcongr
      _ = _ := mul_one _
  have h3 : (∫⁻ x, g x ∂μ) ^ (2:ℝ) ≤ ((∫⁻ x, g x ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
    ENNReal.rpow_le_rpow h2 (by norm_num)
  rw [← ENNReal.rpow_mul] at h3
  norm_num at h3
  have e : ∀ y : ENNReal, y ^ (2:ℝ) = y ^ (2:ℕ) := fun y => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simpa [e] using h3

/-- Two lines whose slopes differ by more than `w` stay within `r` of each other only for a
time of length at most `2r/w`. -/
theorem volume_close_times {a b r w : ℝ} (hw : 0 < w) (hb : w < |b|) :
    volume {u : ℝ | |a + u * b| < r} ≤ ENNReal.ofReal (2 * r / w) := by
  have hb0 : 0 < |b| := hw.trans hb
  have hbne : b ≠ 0 := abs_pos.1 hb0
  rcases le_or_gt r 0 with hr | hr
  · have : {u : ℝ | |a + u * b| < r} = ∅ := by
      ext u; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact hr.trans (abs_nonneg _)
    rw [this, measure_empty]; exact bot_le
  have hsub : {u : ℝ | |a + u * b| < r} ⊆ Icc (-a / b - r / |b|) (-a / b + r / |b|) := by
    intro u hu
    simp only [mem_ofPred_eq] at hu
    have : |u - (-a / b)| ≤ r / |b| := by
      rw [le_div_iff₀ hb0, ← abs_mul]
      have : (u - -a / b) * b = a + u * b := by field_simp; ring
      rw [this]; exact hu.le
    rw [mem_Icc]; constructor <;> linarith [(abs_le.1 this).1, (abs_le.1 this).2]
  calc volume {u : ℝ | |a + u * b| < r} ≤ volume (Icc (-a / b - r / |b|) (-a / b + r / |b|)) :=
        measure_mono hsub
    _ = ENNReal.ofReal (2 * r / |b|) := by rw [Real.volume_Icc]; congr 1; ring
    _ ≤ ENNReal.ofReal (2 * r / w) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by linarith) hw hb.le)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pairs of trajectories labeled at a common time in a common bin. -/
def timeColl (E : Set (Ω × ℝ)) (bin : Ω → ℝ → ℤ) : Set ((Ω × Ω) × ℝ) :=
  {x | (x.1.1, x.2) ∈ E ∧ (x.1.2, x.2) ∈ E ∧ bin x.1.1 x.2 = bin x.1.2 x.2}

theorem measurable_fst_snd : Measurable (fun x : (Ω × Ω) × ℝ => (x.1.1, x.2)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem measurable_snd_snd : Measurable (fun x : (Ω × Ω) × ℝ => (x.1.2, x.2)) :=
  (measurable_snd.comp measurable_fst).prodMk measurable_snd

theorem measurableSet_timeColl {E : Set (Ω × ℝ)} (hE : MeasurableSet E) {bin : Ω → ℝ → ℤ}
    (hbin : Measurable (fun q : Ω × ℝ => bin q.1 q.2)) : MeasurableSet (timeColl E bin) :=
  (measurable_fst_snd hE).inter ((measurable_snd_snd hE).inter
    (measurableSet_eq_fun (hbin.comp measurable_fst_snd) (hbin.comp measurable_snd_snd)))

/-- Collision lower bound: `M² ≤ C₁ · (collisions)`. -/
theorem timeColl_lower (ν : Measure Ω) [IsFiniteMeasure ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    (hE01 : ∀ q ∈ E, q.2 ∈ Icc (0:ℝ) 1) {bin : Ω → ℝ → ℤ}
    (hbin : Measurable (fun q : Ω × ℝ => bin q.1 q.2)) {C₁ : ℝ}
    (hcount : ∀ u, ∃ B : Finset ℤ, (B.card : ℝ) ≤ C₁ ∧ ∀ l, (l, u) ∈ E → bin l u ∈ B) :
    ((ν.prod volume) E) ^ 2 ≤ ENNReal.ofReal C₁ * ((ν.prod ν).prod volume) (timeColl E bin) := by
  rw [Measure.prod_apply_symm hE, Measure.prod_apply_symm (measurableSet_timeColl hE hbin)]
  set g : ℝ → ENNReal := fun u => ν ((fun x => (x, u)) ⁻¹' E) with hgdef
  have hg : Measurable g := measurable_measure_prodMk_right hE
  have hg0 : ∀ u ∉ Icc (0:ℝ) 1, g u = 0 := by
    intro u hu
    have : (fun x => (x, u)) ⁻¹' E = (∅ : Set Ω) := by
      ext l; simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro h; exact hu (hE01 _ h)
    simp [hgdef, this]
  have e1 : ∫⁻ u, g u = ∫⁻ u in Icc (0:ℝ) 1, g u := by
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; ext u
    by_cases hu : u ∈ Icc (0:ℝ) 1
    · simp [hu]
    · simp [hu, hg0 u hu]
  rw [e1]
  have hJ := sq_lintegral_le (volume.restrict (Icc (0:ℝ) 1)) (by simp) hg.aemeasurable
  refine hJ.trans ((setLIntegral_le_lintegral _ _).trans ?_)
  rw [← lintegral_const_mul _ (measurable_measure_prodMk_right (measurableSet_timeColl hE hbin))]
  apply lintegral_mono
  intro u
  show g u ^ 2 ≤ ENNReal.ofReal C₁ * (ν.prod ν) ((fun x => (x, u)) ⁻¹' timeColl E bin)
  obtain ⟨B, hBc, hB⟩ := hcount u
  have hW : MeasurableSet {l | (l, u) ∈ E} := measurable_prodMk_right hE
  have hf : Measurable (fun l => bin l u) := hbin.comp (measurable_id.prodMk measurable_const)
  have hcl := collision_lower ν hW hf B (fun l hl => hB l hl)
  have hslice : (fun x : Ω × Ω => (x, u)) ⁻¹' timeColl E bin =
      collSet {l | (l, u) ∈ E} (fun l => bin l u) := rfl
  rw [hslice]
  calc g u ^ 2 = ν {l | (l, u) ∈ E} ^ 2 := rfl
    _ ≤ (B.card : ENNReal) * (ν.prod ν) (collSet {l | (l, u) ∈ E} (fun l => bin l u)) := hcl
    _ ≤ ENNReal.ofReal C₁ * (ν.prod ν) (collSet {l | (l, u) ∈ E} (fun l => bin l u)) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hBc

/-- Far-slope collisions: pairs whose line slopes differ by more than `w` share a bin only for
time `2(p+2e)/w`. -/
theorem farColl_le (ν : Measure Ω) [IsFiniteMeasure ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    {z k : Ω → ℝ} (hk : Measurable k) {L : Ω → ℝ → ℝ}
    (hL : Measurable (fun q : Ω × ℝ => L q.1 q.2)) {p e w : ℝ} (hp : 0 < p) (hw : 0 < w)
    (hmodel : ∀ q ∈ E, |L q.1 q.2 - (z q.1 + q.2 * k q.1)| ≤ e) :
    ((ν.prod ν).prod volume) (timeColl E (fun l u => ⌊L l u / p⌋) ∩
        {x | w < |k x.1.2 - k x.1.1|}) ≤
      ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2 := by
  have hbin : Measurable (fun q : Ω × ℝ => ⌊L q.1 q.2 / p⌋) :=
    Int.measurable_floor.comp (hL.div_const p)
  have hfar : MeasurableSet {x : (Ω × Ω) × ℝ | w < |k x.1.2 - k x.1.1|} :=
    measurableSet_lt measurable_const
      (((hk.comp (measurable_snd.comp measurable_fst)).sub
        (hk.comp (measurable_fst.comp measurable_fst))).abs)
  rw [Measure.prod_apply ((measurableSet_timeColl (bin := fun l u => ⌊L l u / p⌋) hE hbin).inter
    hfar)]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
          {x | w < |k x.1.2 - k x.1.1|})) ∂(ν.prod ν)
      ≤ ∫⁻ _x, ENNReal.ofReal (2 * (p + 2 * e) / w) ∂(ν.prod ν) := by
        apply lintegral_mono
        rintro ⟨l, l'⟩
        dsimp only
        by_cases hll : w < |k l' - k l|
        · refine le_trans (measure_mono ?_) (volume_close_times (a := z l' - z l)
            (b := k l' - k l) (r := p + 2 * e) hw hll)
          rintro u ⟨⟨hl, hl', hbin_eq⟩, -⟩
          simp only [mem_ofPred_eq]
          have h1 := hmodel _ hl
          have h2 := hmodel _ hl'
          simp only at h1 h2 hbin_eq
          have hfl : |L l u / p - L l' u / p| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor hbin_eq
          have hfl' : |L l u - L l' u| < p := by
            rw [← sub_div, abs_div, abs_of_pos hp, div_lt_one hp] at hfl; exact hfl
          have : z l' - z l + u * (k l' - k l) =
              (L l' u - L l u) + (L l u - (z l + u * k l)) + (-(L l' u - (z l' + u * k l'))) := by
            ring
          rw [this]
          have h3 : |L l' u - L l u| < p := by rw [abs_sub_comm]; exact hfl'
          calc |(L l' u - L l u) + (L l u - (z l + u * k l)) + (-(L l' u - (z l' + u * k l')))|
              ≤ |L l' u - L l u| + |L l u - (z l + u * k l)| + |-(L l' u - (z l' + u * k l'))| :=
                abs_add_three _ _ _
            _ < p + 2 * e := by rw [abs_neg]; linarith
        · have : Prod.mk (l, l') ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
              {x | w < |k x.1.2 - k x.1.1|}) = ∅ := by
            ext u; simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
              iff_false, not_and]
            intro _; exact hll
          rw [this, measure_empty]; exact bot_le
    _ = ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2 := by
        rw [lintegral_const, ← univ_prod_univ, Measure.prod_prod, sq]

/-- Close-slope collisions: paid by the cap, at most `C₂ Ncells` per labeled incidence. -/
theorem closeColl_le (ν : Measure Ω) [IsFiniteMeasure ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    {k : Ω → ℝ} (hk : Measurable k) {L : Ω → ℝ → ℝ}
    (hL : Measurable (fun q : Ω × ℝ => L q.1 q.2)) {ι : Type*} (c : Ω → ι) {p w C₂ : ℝ}
    (Ncells : ℕ)
    (hcap : ∀ (u : ℝ) (γ : ι) (b : ℤ),
      ν {l | (l, u) ∈ E ∧ c l = γ ∧ ⌊L l u / p⌋ = b} ≤ ENNReal.ofReal C₂)
    (hcells : ∀ l, ∃ Γ : Finset ι, Γ.card ≤ Ncells ∧ ∀ l', |k l' - k l| ≤ w → c l' ∈ Γ) :
    ((ν.prod ν).prod volume) (timeColl E (fun l u => ⌊L l u / p⌋) ∩
        {x | |k x.1.2 - k x.1.1| ≤ w}) ≤
      ENNReal.ofReal C₂ * Ncells * (ν.prod volume) E := by
  have hbin : Measurable (fun q : Ω × ℝ => ⌊L q.1 q.2 / p⌋) :=
    Int.measurable_floor.comp (hL.div_const p)
  have hclose : MeasurableSet {x : (Ω × Ω) × ℝ | |k x.1.2 - k x.1.1| ≤ w} :=
    measurableSet_le (((hk.comp (measurable_snd.comp measurable_fst)).sub
        (hk.comp (measurable_fst.comp measurable_fst))).abs) measurable_const
  have hS := (measurableSet_timeColl (bin := fun l u => ⌊L l u / p⌋) hE hbin).inter hclose
  rw [Measure.prod_apply_symm hS, Measure.prod_apply_symm hE, ← lintegral_const_mul _
    (measurable_measure_prodMk_right hE)]
  apply lintegral_mono
  intro u
  show (ν.prod ν) ((fun x => (x, u)) ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
      {x | |k x.1.2 - k x.1.1| ≤ w})) ≤ ENNReal.ofReal C₂ * Ncells * ν ((fun x => (x, u)) ⁻¹' E)
  have hSu : MeasurableSet ((fun x : Ω × Ω => (x, u)) ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
      {x | |k x.1.2 - k x.1.1| ≤ w})) := measurable_prodMk_right hS
  rw [Measure.prod_apply hSu, ← lintegral_indicator_const (measurable_prodMk_right hE)]
  apply lintegral_mono
  intro l
  dsimp only
  by_cases hl : (l, u) ∈ E
  · have hind : ((fun x => (x, u)) ⁻¹' E).indicator (fun _ => ENNReal.ofReal C₂ * Ncells) l =
        ENNReal.ofReal C₂ * Ncells := indicator_of_mem (s := (fun x => (x, u)) ⁻¹' E) hl _
    rw [hind]
    obtain ⟨Γ, hΓc, hΓ⟩ := hcells l
    have hsub : Prod.mk l ⁻¹' ((fun x => (x, u)) ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
        {x | |k x.1.2 - k x.1.1| ≤ w})) ⊆
        ⋃ γ ∈ Γ, {l' | (l', u) ∈ E ∧ c l' = γ ∧ ⌊L l' u / p⌋ = ⌊L l u / p⌋} := by
      rintro l' ⟨⟨_, hl', hb⟩, hkl⟩
      simp only [mem_ofPred_eq] at hkl
      exact mem_iUnion₂.2 ⟨c l', hΓ l' hkl, hl', rfl, hb.symm⟩
    calc ν (Prod.mk l ⁻¹' ((fun x => (x, u)) ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
          {x | |k x.1.2 - k x.1.1| ≤ w})))
        ≤ ν (⋃ γ ∈ Γ, {l' | (l', u) ∈ E ∧ c l' = γ ∧ ⌊L l' u / p⌋ = ⌊L l u / p⌋}) :=
          measure_mono hsub
      _ ≤ ∑ γ ∈ Γ, ν {l' | (l', u) ∈ E ∧ c l' = γ ∧ ⌊L l' u / p⌋ = ⌊L l u / p⌋} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _γ ∈ Γ, ENNReal.ofReal C₂ := Finset.sum_le_sum (fun γ _ => hcap u γ _)
      _ = Γ.card * ENNReal.ofReal C₂ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Ncells * ENNReal.ofReal C₂ := by gcongr
      _ = ENNReal.ofReal C₂ * Ncells := mul_comm _ _
  · have : Prod.mk l ⁻¹' ((fun x => (x, u)) ⁻¹' (timeColl E (fun l u => ⌊L l u / p⌋) ∩
        {x | |k x.1.2 - k x.1.1| ≤ w})) = ∅ := by
      ext l'; simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h.1 hl
    rw [this, measure_empty]; exact bot_le

/-- **The slope-concentration inequality.** -/
theorem slope_concentration_ineq (ν : Measure Ω) [IsFiniteMeasure ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) (hE01 : ∀ q ∈ E, q.2 ∈ Icc (0:ℝ) 1) {z k : Ω → ℝ}
    (hk : Measurable k) {L : Ω → ℝ → ℝ} (hL : Measurable (fun q : Ω × ℝ => L q.1 q.2))
    {ι : Type*} (c : Ω → ι) {p e w C₁ C₂ : ℝ} (hp : 0 < p) (hw : 0 < w) (Ncells : ℕ)
    (hmodel : ∀ q ∈ E, |L q.1 q.2 - (z q.1 + q.2 * k q.1)| ≤ e)
    (hcount : ∀ u, ∃ B : Finset ℤ, (B.card : ℝ) ≤ C₁ ∧ ∀ l, (l, u) ∈ E → ⌊L l u / p⌋ ∈ B)
    (hcap : ∀ (u : ℝ) (γ : ι) (b : ℤ),
      ν {l | (l, u) ∈ E ∧ c l = γ ∧ ⌊L l u / p⌋ = b} ≤ ENNReal.ofReal C₂)
    (hcells : ∀ l, ∃ Γ : Finset ι, Γ.card ≤ Ncells ∧ ∀ l', |k l' - k l| ≤ w → c l' ∈ Γ) :
    ((ν.prod volume) E) ^ 2 ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ * Ncells * (ν.prod volume) E +
      ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2) := by
  have hbin : Measurable (fun q : Ω × ℝ => ⌊L q.1 q.2 / p⌋) :=
    Int.measurable_floor.comp (hL.div_const p)
  refine (timeColl_lower (bin := fun l u => ⌊L l u / p⌋) ν hE hE01 hbin hcount).trans ?_
  gcongr
  have hsplit : timeColl E (fun l u => ⌊L l u / p⌋) ⊆
      (timeColl E (fun l u => ⌊L l u / p⌋) ∩ {x | |k x.1.2 - k x.1.1| ≤ w}) ∪
      (timeColl E (fun l u => ⌊L l u / p⌋) ∩ {x | w < |k x.1.2 - k x.1.1|}) := by
    intro x hx
    rcases le_or_gt (|k x.1.2 - k x.1.1|) w with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  calc ((ν.prod ν).prod volume) (timeColl E (fun l u => ⌊L l u / p⌋))
      ≤ ((ν.prod ν).prod volume) ((timeColl E (fun l u => ⌊L l u / p⌋) ∩
          {x | |k x.1.2 - k x.1.1| ≤ w}) ∪
          (timeColl E (fun l u => ⌊L l u / p⌋) ∩ {x | w < |k x.1.2 - k x.1.1|})) :=
        measure_mono hsplit
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (closeColl_le ν hE hk hL c Ncells hcap hcells)
        (farColl_le ν hE hk hL hp hw hmodel)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
