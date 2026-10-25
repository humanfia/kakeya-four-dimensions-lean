import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.TimeChoice
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.SlopeConc

/-!
# One group of the reading time

Fix a block `[t₀, t₀ + H]`, a set `T` of times in it on which the row is affine,
`|F t i - (a i + (t - t₀) A i)| ≤ Efit`, and a reading time `t* ∈ T`. The trajectories labeled
at `t*` are grouped by the `H`-bin `g` of `B_l = x̄_l(t₀) - F(t*) · y_l`. In normalized block time
`u = (t - t₀)/H` the group's scalar `L_l(u) = (S_l(t₀ + H u) - g H)/H` follows the line
`z_l + u k_l`, `k_l = γ_l - A · y_l`, up to `4 K Efit / H` (`group_model`).

`group_heavy_slope` verifies all hypotheses of `exists_heavy_slope_interval` for one group
(after removing the light `p₀`-cells of `y`) and returns a heavy interval of residual slopes.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The base value `B_l = x̄_l(t₀) - F(t*) · y_l`. -/
def baseVal (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (t₀ ts : ℝ) (l : Ω) : ℝ :=
  xbar β γ l t₀ - (F ts 0 * y l 0 + F ts 1 * y l 1)

/-- The residual slope `k_l = γ_l - A · y_l`. -/
def resSlope (y : Ω → Fin 2 → ℝ) (γ : Ω → ℝ) (A : Fin 2 → ℝ) (l : Ω) : ℝ :=
  γ l - (A 0 * y l 0 + A 1 * y l 1)

/-- The normalized group scalar `L_l(u) = (S_l(t₀ + H u) - g H)/H`. -/
def groupScal (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (t₀ H : ℝ) (g : ℤ)
    (l : Ω) (u : ℝ) : ℝ :=
  (scal y β γ F l (t₀ + H * u) - g * H) / H

/-- The `p₀`-cell of the tangential coordinates. -/
def yCell (y : Ω → Fin 2 → ℝ) (p₀ : ℝ) (l : Ω) : ℤ × ℤ := (⌊y l 0 / p₀⌋, ⌊y l 1 / p₀⌋)

/-- The normalized labels of a set `G` of trajectories in the block, at fitting times. -/
def groupLabels (E : Set (Ω × ℝ)) (T : Set ℝ) (t₀ H : ℝ) (G : Set Ω) : Set (Ω × ℝ) :=
  {q | q.1 ∈ G ∧ q.2 ∈ Icc (0 : ℝ) 1 ∧ t₀ + H * q.2 ∈ T ∧ (q.1, t₀ + H * q.2) ∈ E}

/-- The model of the group scalar along the affine row. -/
theorem group_model {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {F : ℝ → Fin 2 → ℝ} {t₀ H Efit ts : ℝ}
    {T : Set ℝ} {a A : Fin 2 → ℝ} (hH : 0 < H)
    (hfit : ∀ t ∈ T, ∀ i, |F t i - (a i + (t - t₀) * A i)| ≤ Efit) (hts : ts ∈ T)
    (g : ℤ) (l : Ω) {u : ℝ} (hu : t₀ + H * u ∈ T) :
    |groupScal y β γ F t₀ H g l u -
        ((baseVal y β γ F t₀ ts l - g * H) / H + (ts - t₀) / H * (A 0 * y l 0 + A 1 * y l 1) +
          u * resSlope y γ A l)| ≤ 2 * Efit * (|y l 0| + |y l 1|) / H := by
  have e0 := hfit _ hu 0
  have e1 := hfit _ hu 1
  have s0 := hfit _ hts 0
  have s1 := hfit _ hts 1
  set ε0 := F (t₀ + H * u) 0 - (a 0 + (t₀ + H * u - t₀) * A 0)
  set ε1 := F (t₀ + H * u) 1 - (a 1 + (t₀ + H * u - t₀) * A 1)
  set δ0 := F ts 0 - (a 0 + (ts - t₀) * A 0)
  set δ1 := F ts 1 - (a 1 + (ts - t₀) * A 1)
  have key : groupScal y β γ F t₀ H g l u -
      ((baseVal y β γ F t₀ ts l - g * H) / H + (ts - t₀) / H * (A 0 * y l 0 + A 1 * y l 1) +
        u * resSlope y γ A l) = -((ε0 - δ0) * y l 0 + (ε1 - δ1) * y l 1) / H := by
    unfold groupScal baseVal resSlope scal xbar
    simp only [ε0, ε1, δ0, δ1]
    field_simp
    ring
  rw [key, abs_div, abs_neg, abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  calc |(ε0 - δ0) * y l 0 + (ε1 - δ1) * y l 1|
      ≤ |ε0 - δ0| * |y l 0| + |ε1 - δ1| * |y l 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (2 * Efit) * |y l 0| + (2 * Efit) * |y l 1| := by
        gcongr
        · exact (abs_sub _ _).trans (by linarith)
        · exact (abs_sub _ _).trans (by linarith)
    _ = 2 * Efit * (|y l 0| + |y l 1|) := by ring

theorem measurableSet_groupLabels {E : Set (Ω × ℝ)} (hE : MeasurableSet E) {T : Set ℝ}
    (hT : MeasurableSet T) (t₀ H : ℝ) {G : Set Ω} (hG : MeasurableSet G) :
    MeasurableSet (groupLabels E T t₀ H G) := by
  have hφ : Measurable (fun q : Ω × ℝ => (q.1, t₀ + H * q.2)) :=
    measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))
  have h1 : MeasurableSet {q : Ω × ℝ | q.1 ∈ G} := measurable_fst hG
  have h2 : MeasurableSet {q : Ω × ℝ | q.2 ∈ Icc (0 : ℝ) 1} := measurable_snd measurableSet_Icc
  have h3 : MeasurableSet {q : Ω × ℝ | t₀ + H * q.2 ∈ T} :=
    (measurable_const.add (measurable_const.mul measurable_snd)) hT
  have h4 : MeasurableSet {q : Ω × ℝ | (q.1, t₀ + H * q.2) ∈ E} := hφ hE
  exact h1.inter (h2.inter (h3.inter h4))

/-- The normalized labels have mass `∫_G durT / H`. -/
theorem groupLabels_mass (ν : Measure Ω) [SFinite ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    {T : Set ℝ} (hT : MeasurableSet T) {t₀ H : ℝ} (hH : 0 < H) (hTsub : T ⊆ Icc t₀ (t₀ + H))
    {G : Set Ω} (hG : MeasurableSet G) :
    (ν.prod volume) (groupLabels E T t₀ H G) =
      ENNReal.ofReal H⁻¹ * ∫⁻ l in G, durIn E T l ∂ν := by
  rw [Measure.prod_apply (measurableSet_groupLabels hE hT t₀ H hG), ← lintegral_indicator hG,
    ← lintegral_const_mul _ ((measurable_durIn hE hT).indicator hG)]
  congr 1; ext l
  by_cases hl : l ∈ G
  · rw [indicator_of_mem hl]
    -- the slice is the affine preimage of the labeled times in `T`
    have hslice : Prod.mk l ⁻¹' groupLabels E T t₀ H G =
        (fun u => t₀ + H * u) ⁻¹' {t | t ∈ T ∧ (l, t) ∈ E} := by
      ext u
      simp only [mem_preimage, groupLabels, mem_ofPred_eq, hl, true_and]
      constructor
      · rintro ⟨-, hT', hE'⟩; exact ⟨hT', hE'⟩
      · rintro ⟨hT', hE'⟩
        refine ⟨⟨?_, ?_⟩, hT', hE'⟩
        · have := (hTsub hT').1
          by_contra h; push Not at h
          nlinarith
        · have := (hTsub hT').2
          by_contra h; push Not at h
          nlinarith
    rw [hslice]
    have hmap : (fun u : ℝ => t₀ + H * u) ⁻¹' {t | t ∈ T ∧ (l, t) ∈ E} =
        (fun u : ℝ => H * u) ⁻¹' ((fun v : ℝ => t₀ + v) ⁻¹' {t | t ∈ T ∧ (l, t) ∈ E}) := rfl
    rw [hmap, Real.volume_preimage_mul_left hH.ne', measure_preimage_add]
    unfold durIn
    rw [abs_inv, abs_of_pos hH]
  · rw [indicator_of_notMem hl, mul_zero]
    have : Prod.mk l ⁻¹' groupLabels E T t₀ H G = ∅ := by
      ext u; simp [groupLabels, hl]
    rw [this, measure_empty]


/-- The scalar of a group trajectory stays within `(4K² + K + 1) H` of `g H` in the block. -/
theorem group_scal_bound {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ)
    (hK : 1 ≤ K) {t₀ H ts t : ℝ} (hH : 0 < H) (hζH : ζ ≤ H) (ht : t ∈ Icc t₀ (t₀ + H))
    (hts : ts ∈ Icc t₀ (t₀ + H)) {g : ℤ} {l : Ω} (hlts : (l, ts) ∈ E) (hlt : (l, t) ∈ E)
    (hg : ⌊baseVal y β γ F t₀ ts l / H⌋ = g) :
    |scal y β γ F l t - g * H| ≤ (4 * K ^ 2 + K + 1) * H := by
  have hB1 : (g : ℝ) * H ≤ baseVal y β γ F t₀ ts l := by
    have := Int.floor_le (baseVal y β γ F t₀ ts l / H); rw [hg] at this
    rwa [le_div_iff₀ hH] at this
  have hB2 : baseVal y β γ F t₀ ts l < ((g : ℝ) + 1) * H := by
    have := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l / H); rw [hg] at this
    rwa [div_lt_iff₀ hH] at this
  have hF : ∀ i, |F t i - F ts i| ≤ 2 * K * H := by
    intro i
    refine (h.rowLip t ts ⟨l, hlt⟩ ⟨l, hlts⟩ i).trans ?_
    have : |t - ts| ≤ H := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hts.1, hts.2]
    nlinarith
  have hγ := h.bound_γ l
  have hy0 := h.bound_y l 0
  have hy1 := h.bound_y l 1
  have key : scal y β γ F l t - g * H = (baseVal y β γ F t₀ ts l - g * H) + (t - t₀) * γ l -
      ((F t 0 - F ts 0) * y l 0 + (F t 1 - F ts 1) * y l 1) := by
    unfold scal baseVal xbar; ring
  rw [key]
  have h1 : |baseVal y β γ F t₀ ts l - g * H| ≤ H := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |(t - t₀) * γ l| ≤ H * K := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]) hγ (abs_nonneg _)
      hH.le
  have h3 : |(F t 0 - F ts 0) * y l 0 + (F t 1 - F ts 1) * y l 1| ≤ 4 * K ^ 2 * H := by
    calc |(F t 0 - F ts 0) * y l 0 + (F t 1 - F ts 1) * y l 1|
        ≤ |F t 0 - F ts 0| * |y l 0| + |F t 1 - F ts 1| * |y l 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (2 * K * H) * K + (2 * K * H) * K := by
          gcongr
          · exact hF 0
          · exact hF 1
      _ = 4 * K ^ 2 * H := by ring
  calc |(baseVal y β γ F t₀ ts l - g * H) + (t - t₀) * γ l -
        ((F t 0 - F ts 0) * y l 0 + (F t 1 - F ts 1) * y l 1)|
      ≤ |baseVal y β γ F t₀ ts l - g * H| + |(t - t₀) * γ l| +
          |(F t 0 - F ts 0) * y l 0 + (F t 1 - F ts 1) * y l 1| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ H + H * K + 4 * K ^ 2 * H := by linarith
    _ = (4 * K ^ 2 + K + 1) * H := by ring

/-- The trajectories labeled at `ts` whose base value lies in the `H`-bin `g`. -/
def groupSet (E : Set (Ω × ℝ)) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ)
    (t₀ ts H : ℝ) (g : ℤ) : Set Ω :=
  {l | (l, ts) ∈ E ∧ ⌊baseVal y β γ F t₀ ts l / H⌋ = g}

/-- Keep the trajectories of `S` whose `p₀`-cell carries mass `≥ f`. -/
def heavyPart (ν : Measure Ω) (S : Set Ω) (y : Ω → Fin 2 → ℝ) (p₀ f : ℝ) : Set Ω :=
  S ∩ {l | ENNReal.ofReal f ≤ ν (S ∩ {l' | yCell y p₀ l' = yCell y p₀ l})}

/-- The scalar-bin count constant of a group. -/
def cnt1 (K d p₀ : ℝ) : ℝ := 2 * (K * (2 * (4 * K ^ 2 + K + 1) / p₀) ^ d)

/-- The (cell, bin) cap constant of a group. -/
def cap2 (K d H p₀ : ℝ) : ℝ := (1 / H + 2) ^ 2 * (4 * K + 3) * (K * (H * p₀) ^ (2 + d))

/-- The slope variation inside a `p₀`-cell. -/
def slopeVar (K KA H p₀ ζ : ℝ) : ℝ :=
  K * (H * (1 + 2 * K) + 2 * K * p₀ + 2 * p₀ + ζ) + 2 * KA * p₀

theorem measurable_baseVal {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (F : ℝ → Fin 2 → ℝ) (t₀ ts : ℝ) :
    Measurable (baseVal y β γ F t₀ ts) := by
  have h0 : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp hy
  have h1 : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp hy
  unfold baseVal xbar
  fun_prop

theorem measurableSet_groupSet {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y) (hβ : Measurable β)
    (hγ : Measurable γ) (F : ℝ → Fin 2 → ℝ) (t₀ ts H : ℝ) (g : ℤ) :
    MeasurableSet (groupSet E y β γ F t₀ ts H g) := by
  have h1 : MeasurableSet {l : Ω | (l, ts) ∈ E} := measurable_prodMk_right hE
  have h2 : Measurable fun l => ⌊baseVal y β γ F t₀ ts l / H⌋ :=
    Int.measurable_floor.comp ((measurable_baseVal hy hβ hγ F t₀ ts).div_const H)
  exact h1.inter (h2 (measurableSet_singleton g))

theorem measurable_yCell {y : Ω → Fin 2 → ℝ} (hy : Measurable y) (p₀ : ℝ) :
    Measurable (yCell y p₀) := by
  have h0 : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp hy
  have h1 : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp hy
  exact (Int.measurable_floor.comp (h0.div_const p₀)).prodMk
    (Int.measurable_floor.comp (h1.div_const p₀))

theorem measurableSet_heavyPart (ν : Measure Ω) {S : Set Ω} (hS : MeasurableSet S)
    {y : Ω → Fin 2 → ℝ} (hy : Measurable y) (p₀ f : ℝ) :
    MeasurableSet (heavyPart ν S y p₀ f) := by
  have : {l | ENNReal.ofReal f ≤ ν (S ∩ {l' | yCell y p₀ l' = yCell y p₀ l})} =
      yCell y p₀ ⁻¹' {c | ENNReal.ofReal f ≤ ν (S ∩ {l' | yCell y p₀ l' = c})} := rfl
  unfold heavyPart
  rw [this]
  exact hS.inter (measurable_yCell hy p₀ (DiscreteMeasurableSpace.forall_measurableSet _))

/-- A floor shifted by `g / p₀`. -/
theorem floor_sub_mem {x c : ℝ} :
    ⌊x - c⌋ ∈ ({⌊(⌊x⌋ : ℝ) - c⌋, ⌊(⌊x⌋ : ℝ) - c⌋ + 1} : Finset ℤ) := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have a1 : ⌊(⌊x⌋ : ℝ) - c⌋ ≤ ⌊x - c⌋ := Int.floor_le_floor (by linarith)
  have a2 : ⌊x - c⌋ ≤ ⌊(⌊x⌋ : ℝ) - c⌋ + 1 := by
    have : x - c ≤ ((⌊x⌋ : ℝ) - c) + 1 := by linarith
    calc ⌊x - c⌋ ≤ ⌊((⌊x⌋ : ℝ) - c) + 1⌋ := Int.floor_le_floor this
      _ = ⌊(⌊x⌋ : ℝ) - c⌋ + 1 := Int.floor_add_one _
  rcases eq_or_lt_of_le a1 with h | h
  · simp [h]
  · have : ⌊x - c⌋ = ⌊(⌊x⌋ : ℝ) - c⌋ + 1 := by omega
    simp [this]

/-- One group: a heavy interval of residual slopes. -/
theorem group_heavy_slope {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : Data ν y β γ E F d K ζ) (hK : 1 ≤ K) (hd : 0 ≤ d) (hζ0 : 0 ≤ ζ)
    {E' : Set (Ω × ℝ)} (hE' : MeasurableSet E') (hE'E : E' ⊆ E)
    {t₀ H : ℝ} (hH : 0 < H) (hζH : ζ ≤ H)
    {T : Set ℝ} (hT : MeasurableSet T) (hTsub : T ⊆ Icc t₀ (t₀ + H))
    {a A : Fin 2 → ℝ} {Efit KA : ℝ} (hEfit : 0 ≤ Efit) (hKA : 0 ≤ KA)
    (hfit : ∀ t ∈ T, ∀ i, |F t i - (a i + (t - t₀) * A i)| ≤ Efit) (hA : ∀ i, |A i| ≤ KA)
    {ts : ℝ} (hts : ts ∈ T) (g : ℤ) {p₀ f m M₀ w' : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hζq : ζ ≤ H * p₀) (hr1 : 2 * (4 * K ^ 2 + K + 1) * H ≤ 1)
    (hf : 0 < f) (hm : 0 ≤ m) (hM₀ : 0 < M₀) (hw' : 0 < w')
    (hmass : ENNReal.ofReal M₀ ≤
      ((ν.restrict (groupSet E' y β γ F t₀ ts H g)).prod volume)
        (groupLabels E' T t₀ H (heavyPart ν (groupSet E' y β γ F t₀ ts H g) y p₀ f)))
    (hbudget : cnt1 K d p₀ * cap2 K d H p₀ * (m / f + 2) ≤ M₀ / 2)
    (hfar : ENNReal.ofReal (cnt1 K d p₀) * (ENNReal.ofReal (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') *
      ν (groupSet E' y β γ F t₀ ts H g) ^ 2) < ENNReal.ofReal (M₀ ^ 2 / 2)) :
    ∃ κ : ℝ, ENNReal.ofReal m ≤ ν (heavyPart ν (groupSet E' y β γ F t₀ ts H g) y p₀ f ∩
      {l | |resSlope y γ A l - κ| ≤ w' + slopeVar K KA H p₀ ζ}) := by
  classical
  set G0 := groupSet E' y β γ F t₀ ts H g with hG0
  set G := heavyPart ν G0 y p₀ f with hGdef
  set ν' := ν.restrict G0 with hν'
  have hγm := h.measurable_γ
  have hβm := h.measurable_β
  have hy0m : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp h.measurable_y
  have hy1m : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp h.measurable_y
  have hkm : Measurable (resSlope y γ A) := by unfold resSlope; fun_prop
  have hG0m : MeasurableSet G0 := measurableSet_groupSet hE' h.measurable_y h.measurable_β
    h.measurable_γ F t₀ ts H g
  have hGm : MeasurableSet G := measurableSet_heavyPart ν hG0m h.measurable_y p₀ f
  have hGG0 : G ⊆ G0 := inter_subset_left
  set Eg := groupLabels E' T t₀ H G with hEg
  have hEgm : MeasurableSet Eg := measurableSet_groupLabels hE' hT t₀ H hGm
  have hHp1 : H * p₀ ≤ 1 := by
    have : H ≤ 1 := by nlinarith
    nlinarith
  have hK7 : 0 < 4 * K ^ 2 + K + 1 := by positivity
  have hLm : Measurable (fun q : Ω × ℝ => groupScal y β γ F t₀ H g q.1 q.2) := by
    have hF := h.measurable_F
    have hF0 : Measurable fun t => F t 0 := (measurable_pi_apply 0).comp hF
    have hF1 : Measurable fun t => F t 1 := (measurable_pi_apply 1).comp hF
    unfold groupScal scal xbar
    fun_prop
  have hV : 0 ≤ slopeVar K KA H p₀ ζ := by
    unfold slopeVar
    have : 0 ≤ H * (1 + 2 * K) + 2 * K * p₀ + 2 * p₀ + ζ := by positivity
    have : 0 ≤ 2 * KA * p₀ := by positivity
    nlinarith
  -- the model
  have hmodel : ∀ q ∈ Eg, |groupScal y β γ F t₀ H g q.1 q.2 -
      ((fun l => (baseVal y β γ F t₀ ts l - g * H) / H +
        (ts - t₀) / H * (A 0 * y l 0 + A 1 * y l 1)) q.1 + q.2 * resSlope y γ A q.1)| ≤
      4 * K * Efit / H := by
    intro q hq
    obtain ⟨hqG, hqI, hqT, hqE⟩ := hq
    refine (group_model hH hfit hts g q.1 hqT).trans ?_
    have hy0 := h.bound_y q.1 0
    have hy1 := h.bound_y q.1 1
    rw [div_le_div_iff_of_pos_right hH]
    nlinarith
  have hcount : ∀ u, ∃ B : Finset ℤ, (B.card : ℝ) ≤ cnt1 K d p₀ ∧
      ∀ l, (l, u) ∈ Eg → ⌊groupScal y β γ F t₀ H g l u / p₀⌋ ∈ B := by
    intro u
    set K7 := 4 * K ^ 2 + K + 1 with hK7def
    have hqr : H * p₀ ≤ 2 * K7 * H := by nlinarith
    obtain ⟨C, hC, hmem⟩ := h.support (t₀ + H * u) (H * p₀) (2 * K7 * H) (g * H - K7 * H)
      hζq hqr hr1
    refine ⟨C.biUnion (fun n => ({⌊(n : ℝ) - g / p₀⌋, ⌊(n : ℝ) - g / p₀⌋ + 1} : Finset ℤ)),
      ?_, ?_⟩
    · have h1 : ((C.biUnion (fun n => ({⌊(n : ℝ) - g / p₀⌋, ⌊(n : ℝ) - g / p₀⌋ + 1} :
          Finset ℤ))).card : ℝ) ≤ 2 * C.card := by
        have := Finset.card_biUnion_le (s := C)
          (t := fun n => ({⌊(n : ℝ) - g / p₀⌋, ⌊(n : ℝ) - g / p₀⌋ + 1} : Finset ℤ))
        have h2 : ∑ n ∈ C, ({⌊(n : ℝ) - g / p₀⌋, ⌊(n : ℝ) - g / p₀⌋ + 1} : Finset ℤ).card ≤
            ∑ _n ∈ C, 2 := Finset.sum_le_sum (fun n _ => Finset.card_le_two)
        rw [Finset.sum_const, smul_eq_mul] at h2
        have := this.trans h2
        exact_mod_cast (by omega : _ ≤ 2 * C.card)
      have hratio : 2 * K7 * H / (H * p₀) = 2 * K7 / p₀ := by field_simp
      rw [hratio] at hC
      unfold cnt1
      rw [← hK7def]
      linarith
    · intro l hl
      obtain ⟨hlG, -, hlT, hlE⟩ := hl
      have hb := group_scal_bound h hK hH hζH (hTsub hlT) (hTsub hts) (hE'E (hGG0 hlG).1)
        (hE'E hlE) (hGG0 hlG).2
      rw [← hK7def] at hb
      have hn := hmem l (hE'E hlE) (by linarith [(abs_le.mp hb).1])
        (by linarith [(abs_le.mp hb).2])
      refine Finset.mem_biUnion.mpr ⟨_, hn, ?_⟩
      have : groupScal y β γ F t₀ H g l u / p₀ =
          scal y β γ F l (t₀ + H * u) / (H * p₀) - g / p₀ := by
        unfold groupScal; field_simp
      rw [this]
      exact floor_sub_mem
  have hcap : ∀ (u : ℝ) (c : ℤ × ℤ) (b : ℤ),
      ν' {l | (l, u) ∈ Eg ∧ yCell y p₀ l = c ∧ ⌊groupScal y β γ F t₀ H g l u / p₀⌋ = b} ≤
        ENNReal.ofReal (cap2 K d H p₀) := by
    intro u c b
    refine (Measure.restrict_le_self _).trans ?_
    have hHp0 : 0 < H * p₀ := mul_pos hH hp₀
    have key := slab_absCap h (by linarith) (t := t₀ + H * u) (q := H * p₀) (σ := p₀)
      (ω := H * p₀) (y00 := c.1 * p₀) (y10 := c.2 * p₀) (s₀ := g * H + b * (H * p₀))
      hζq hHp1 hHp0 hp₀.le hHp0.le
      {l | (l, u) ∈ Eg ∧ yCell y p₀ l = c ∧ ⌊groupScal y β γ F t₀ H g l u / p₀⌋ = b} (by
        intro l hl
        obtain ⟨⟨hlG, -, hlT, hlE⟩, hc, hbin⟩ := hl
        have hc1 : ⌊y l 0 / p₀⌋ = c.1 := congrArg Prod.fst hc
        have hc2 : ⌊y l 1 / p₀⌋ = c.2 := congrArg Prod.snd hc
        have f1 := Int.floor_le (y l 0 / p₀)
        have f2 := Int.lt_floor_add_one (y l 0 / p₀)
        have f3 := Int.floor_le (y l 1 / p₀)
        have f4 := Int.lt_floor_add_one (y l 1 / p₀)
        have f5 := Int.floor_le (groupScal y β γ F t₀ H g l u / p₀)
        have f6 := Int.lt_floor_add_one (groupScal y β γ F t₀ H g l u / p₀)
        rw [hc1] at f1 f2; rw [hc2] at f3 f4; rw [hbin] at f5 f6
        rw [le_div_iff₀ hp₀] at f1 f3 f5
        rw [div_lt_iff₀ hp₀] at f2 f4 f6
        unfold groupScal at f5 f6
        rw [le_div_iff₀ hH] at f5
        rw [div_lt_iff₀ hH] at f6
        refine ⟨hE'E hlE, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
        · nlinarith
        · nlinarith)
    refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    unfold cap2
    have e1 : p₀ / (H * p₀) = 1 / H := by field_simp
    have e2 : H * p₀ / (H * p₀) = 1 := div_self hHp0.ne'
    rw [e1, e2]
    ring
  have hvar : ∀ l ∈ G, ∀ l' ∈ G, yCell y p₀ l = yCell y p₀ l' →
      |resSlope y γ A l - resSlope y γ A l'| ≤ slopeVar K KA H p₀ ζ := by
    intro l hl l' hl' hc
    have hlE : (l, ts) ∈ E := hE'E (hGG0 hl).1
    have hl'E : (l', ts) ∈ E := hE'E (hGG0 hl').1
    have hg1 := (hGG0 hl).2
    have hg2 := (hGG0 hl').2
    -- tangential coordinates in the same cell
    have hcell : ∀ i : Fin 2, ⌊y l i / p₀⌋ = ⌊y l' i / p₀⌋ → |y l i - y l' i| ≤ p₀ := by
      intro i hi
      have a1 := Int.floor_le (y l i / p₀)
      have a2 := Int.lt_floor_add_one (y l i / p₀)
      have a3 := Int.floor_le (y l' i / p₀)
      have a4 := Int.lt_floor_add_one (y l' i / p₀)
      rw [hi] at a1 a2
      rw [le_div_iff₀ hp₀] at a1 a3
      rw [div_lt_iff₀ hp₀] at a2 a4
      rw [abs_le]; constructor <;> nlinarith
    have hd0 := hcell 0 (congrArg Prod.fst hc)
    have hd1 := hcell 1 (congrArg Prod.snd hc)
    -- base values in the same `H`-bin
    have hbase : |baseVal y β γ F t₀ ts l - baseVal y β γ F t₀ ts l'| ≤ H := by
      have a1 := Int.floor_le (baseVal y β γ F t₀ ts l / H)
      have a2 := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l / H)
      have a3 := Int.floor_le (baseVal y β γ F t₀ ts l' / H)
      have a4 := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l' / H)
      rw [hg1] at a1 a2; rw [hg2] at a3 a4
      rw [le_div_iff₀ hH] at a1 a3
      rw [div_lt_iff₀ hH] at a2 a4
      rw [abs_le]; constructor <;> nlinarith
    have htsI := hTsub hts
    have hγl := h.bound_γ l
    have hγl' := h.bound_γ l'
    have hF0 := h.bound_F ts 0
    have hF1 := h.bound_F ts 1
    -- the scalar values at `ts`
    have hxb : |xbar β γ l ts - xbar β γ l' ts| ≤ H * (1 + 2 * K) + 2 * K * p₀ := by
      have key : xbar β γ l ts - xbar β γ l' ts =
          (baseVal y β γ F t₀ ts l - baseVal y β γ F t₀ ts l') + (ts - t₀) * (γ l - γ l') +
          (F ts 0 * (y l 0 - y l' 0) + F ts 1 * (y l 1 - y l' 1)) := by
        unfold baseVal xbar; ring
      rw [key]
      have b1 : |(ts - t₀) * (γ l - γ l')| ≤ H * (2 * K) := by
        rw [abs_mul]
        apply mul_le_mul _ ((abs_sub _ _).trans (by linarith)) (abs_nonneg _) hH.le
        rw [abs_le]; constructor <;> linarith [htsI.1, htsI.2]
      have b2 : |F ts 0 * (y l 0 - y l' 0) + F ts 1 * (y l 1 - y l' 1)| ≤ 2 * K * p₀ := by
        calc |F ts 0 * (y l 0 - y l' 0) + F ts 1 * (y l 1 - y l' 1)|
            ≤ |F ts 0| * |y l 0 - y l' 0| + |F ts 1| * |y l 1 - y l' 1| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ K * p₀ + K * p₀ := by gcongr
          _ = 2 * K * p₀ := by ring
      calc |(baseVal y β γ F t₀ ts l - baseVal y β γ F t₀ ts l') + (ts - t₀) * (γ l - γ l') +
            (F ts 0 * (y l 0 - y l' 0) + F ts 1 * (y l 1 - y l' 1))|
          ≤ |baseVal y β γ F t₀ ts l - baseVal y β γ F t₀ ts l'| +
              |(ts - t₀) * (γ l - γ l')| +
              |F ts 0 * (y l 0 - y l' 0) + F ts 1 * (y l 1 - y l' 1)| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ H + H * (2 * K) + 2 * K * p₀ := by linarith
        _ = H * (1 + 2 * K) + 2 * K * p₀ := by ring
    have hslope := h.slopeLip l l' ts ts hlE hl'E
    simp only [sub_self, abs_zero, zero_add] at hslope
    have hγd : |γ l - γ l'| ≤ K * (H * (1 + 2 * K) + 2 * K * p₀ + 2 * p₀ + ζ) := by
      refine hslope.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have hAd : |A 0 * y l 0 + A 1 * y l 1 - (A 0 * y l' 0 + A 1 * y l' 1)| ≤ 2 * KA * p₀ := by
      have key : A 0 * y l 0 + A 1 * y l 1 - (A 0 * y l' 0 + A 1 * y l' 1) =
          A 0 * (y l 0 - y l' 0) + A 1 * (y l 1 - y l' 1) := by ring
      rw [key]
      calc |A 0 * (y l 0 - y l' 0) + A 1 * (y l 1 - y l' 1)|
          ≤ |A 0| * |y l 0 - y l' 0| + |A 1| * |y l 1 - y l' 1| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ KA * p₀ + KA * p₀ := by gcongr <;> exact hA _
        _ = 2 * KA * p₀ := by ring
    have key : resSlope y γ A l - resSlope y γ A l' =
        (γ l - γ l') - (A 0 * y l 0 + A 1 * y l 1 - (A 0 * y l' 0 + A 1 * y l' 1)) := by
      unfold resSlope; ring
    rw [key]
    unfold slopeVar
    exact (abs_sub _ _).trans (by linarith)
  have hfloor : ∀ l ∈ G, ENNReal.ofReal f ≤ ν' (G ∩ {l' | yCell y p₀ l' = yCell y p₀ l}) := by
    intro l hl
    have hcm : MeasurableSet {l' | yCell y p₀ l' = yCell y p₀ l} :=
      measurable_yCell h.measurable_y p₀ (measurableSet_singleton _)
    rw [hν', Measure.restrict_apply (hGm.inter hcm)]
    refine hl.2.trans (measure_mono ?_)
    rintro l' ⟨hl'G0, hl'c⟩
    refine ⟨⟨⟨hl'G0, ?_⟩, hl'c⟩, hl'G0⟩
    show ENNReal.ofReal f ≤ ν (G0 ∩ {l'' | yCell y p₀ l'' = yCell y p₀ l'})
    have : yCell y p₀ l' = yCell y p₀ l := hl'c
    rw [this]
    exact hl.2
  have hfar' : ENNReal.ofReal (cnt1 K d p₀) *
      (ENNReal.ofReal (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') * ν' univ ^ 2) <
      ENNReal.ofReal (M₀ ^ 2 / 2) := by
    rw [hν', Measure.restrict_apply_univ]; exact hfar
  obtain ⟨κ, hκ⟩ := exists_heavy_slope_interval ν' hEgm (fun q hq => hq.2.1) hGm
    (fun q hq => hq.1) (z := fun l => (baseVal y β γ F t₀ ts l - g * H) / H +
        (ts - t₀) / H * (A 0 * y l 0 + A 1 * y l 1)) hkm hLm (yCell y p₀)
    (fun c => measurable_yCell h.measurable_y p₀ (measurableSet_singleton c))
    hp₀ hw' hV hf hm hM₀ hmodel hcount hcap hvar hfloor hmass
    (by unfold cnt1; positivity) (by unfold cap2; positivity) hbudget hfar'
  refine ⟨κ, hκ.trans ?_⟩
  rw [hν', Measure.restrict_apply (hGm.inter (measurableSet_le
    ((hkm.sub_const κ).abs) measurable_const))]
  exact measure_mono inter_subset_left

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
