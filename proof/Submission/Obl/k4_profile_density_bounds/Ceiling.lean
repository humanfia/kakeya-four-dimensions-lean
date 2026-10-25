import Mathlib
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_profile_density_bounds.Slices

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Part (3) of the density bounds: `F(r, u) ≥ 2u - 2`

Under the joint `(y(t), V)` ceiling `ν{y(t) ∈ S, V ∈ T} ≤ Λ N² |S| |T|`, the selected law of the
joint observation at depth `(r, u)` gives every cell `B × {h} × {v}` mass at most
`Λ N² a_u² |B|` (Fubini over time for the base, `|velocity bin| = a_u²`), hence every measurable
observation set `L` mass at most `Λ N² a_u² · reference L` (`Slices.lean`). A density `G` of the
law therefore leaves no mass on `{G ≥ λ}` once `λ > Λ N² a_u²`. Since `a_u ≤ 2 N^(-u)` and
`Λ` is subpolynomial, a typical density `N^(-F(r,u) ± τ)` with `F(r, u) < 2u - 2` would leave no
selected mass, contradicting the mass lower bound `1/K`.
-/

namespace Submission.Obl.k4_profile_density_bounds

/-- Assemble a base point from a time and a planar point. -/
def assemble (p : ℝ × Velocity) : Base := WithLp.toLp 2 ![p.1, p.2 0, p.2 1]

lemma measurePreserving_assemble :
    MeasurePreserving assemble ((volume : Measure ℝ).prod (volume : Measure Velocity))
      (volume : Measure Base) := by
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : Velocity → (Fin 2 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure Velocity))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin 2))
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have h3 := PiLp.volume_preserving_toLp (Fin 3)
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext p
  simp only [assemble, Function.comp_apply]
  congr 1
  funext i
  fin_cases i <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rfl

/-- The planar section of a base set at time `t`. -/
def timeSlice (B : Set Base) (t : ℝ) : Set Velocity :=
  {y | (WithLp.toLp 2 ![t, y 0, y 1] : Base) ∈ B}

lemma measurableSet_timeSlice {B : Set Base} (hB : MeasurableSet B) (t : ℝ) :
    MeasurableSet (timeSlice B t) := by
  have : Measurable (fun y : Velocity => (WithLp.toLp 2 ![t, y 0, y 1] : Base)) := by fun_prop
  exact this hB

lemma measurable_volume_timeSlice {B : Set Base} (hB : MeasurableSet B) :
    Measurable (fun t => volume (timeSlice B t)) :=
  measurable_measure_prodMk_left (measurePreserving_assemble.measurable hB)

/-- Fubini for the base: the volume of a measurable base set is the integral over time of the
areas of its planar sections. -/
lemma volume_eq_lintegral_timeSlice {B : Set Base} (hB : MeasurableSet B) :
    volume B = ∫⁻ t, volume (timeSlice B t) := by
  rw [← measurePreserving_assemble.measure_preimage hB.nullMeasurableSet,
    Measure.prod_apply (measurePreserving_assemble.measurable hB)]
  rfl

/-- The velocity bin `v` at width `a`. -/
def velBox (a : ℝ) (v : Fin 2 → ℤ) : Set Velocity := {V | ∀ j, ⌊V j / a⌋ = v j}

lemma velBox_eq {a : ℝ} (ha : 0 < a) (v : Fin 2 → ℤ) :
    velBox a v = (WithLp.ofLp : Velocity → (Fin 2 → ℝ)) ⁻¹'
      (Set.pi univ fun j => Ico ((v j : ℝ) * a) (((v j : ℝ) + 1) * a)) := by
  ext V
  simp only [velBox, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_imp_iff, mem_Ico,
    Int.floor_eq_iff, le_div_iff₀ ha, div_lt_iff₀ ha]

lemma measurableSet_velBox (a : ℝ) (v : Fin 2 → ℤ) : MeasurableSet (velBox a v) := by
  have : velBox a v = ⋂ j, (fun V : Velocity => ⌊V j / a⌋) ⁻¹' {v j} := by
    ext V; simp [velBox]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  have hm : Measurable (fun V : Velocity => ⌊V j / a⌋) := by fun_prop
  exact hm (measurableSet_singleton _)

lemma volume_velBox {a : ℝ} (ha : 0 < a) (v : Fin 2 → ℤ) :
    volume (velBox a v) = ENNReal.ofReal a ^ 2 := by
  rw [velBox_eq ha, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [Fin.prod_univ_two]
  rw [sq]
  congr 1 <;> ring_nf

/-- The planar point `y(t)` of a line at time `t`. -/
def planar (t : ℝ) (l : Line) : Velocity :=
  WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4]

/-- The joint `(y(t), V)` ceiling with constant `c`. -/
def JointCeiling (ν : Measure Line) (c : ℝ≥0∞) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ S T : Set Velocity,
    ν {l | planar t l ∈ S ∧ velocity l ∈ T} ≤ c * volume S * volume T

lemma base_mk (l : Line) (t : ℝ) :
    base (l, t) = (WithLp.toLp 2 ![t, planar t l 0, planar t l 1] : Base) := by
  simp [base, planar]

/-- Under the joint ceiling, the observation law gives each cell `B × {h} × {v}` mass at most
`c a_u² vol B`. -/
lemma map_observe_cell_le (ν : Measure Line) [SFinite ν] {E : Set State}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {c : ℝ≥0∞} (hJ : JointCeiling ν c) (N r u : ℝ)
    {B : Set Base} (hB : MeasurableSet B) (h : ℤ) (v : Fin 2 → ℤ) :
    Measure.map (observe N r u) (selected ν E) ((B ×ˢ {h}) ×ˢ {v}) ≤
      c * ENNReal.ofReal (width N u) ^ 2 * volume B := by
  have hcell : MeasurableSet ((B ×ˢ {h}) ×ˢ {v} : Set Observation) :=
    (hB.prod (measurableSet_singleton h)).prod (measurableSet_singleton v)
  rw [Measure.map_apply (measurable_observe N r u) hcell, selected,
    Measure.restrict_apply ((measurable_observe N r u) hcell)]
  set a := width N u with ha_def
  have ha : 0 < a := width_pos N u
  let S : Set State := {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ base p ∈ B ∧ velocity p.1 ∈ velBox a v}
  have hS : MeasurableSet S := by
    refine (measurableSet_Icc.preimage measurable_snd).inter
      ((hB.preimage measurable_base).inter ?_)
    exact (measurableSet_velBox a v).preimage (measurable_velocity.comp measurable_fst)
  have hsub : observe N r u ⁻¹' ((B ×ˢ {h}) ×ˢ {v}) ∩ E ⊆ S := by
    rintro p ⟨hp, hpE⟩
    simp only [mem_preimage, mem_prod, mem_singleton_iff, observe] at hp
    refine ⟨(hE hpE).2, hp.1.1, fun j => ?_⟩
    exact congrFun hp.2 j
  calc (ν.prod volume) (observe N r u ⁻¹' ((B ×ˢ {h}) ×ˢ {v}) ∩ E)
      ≤ (ν.prod volume) S := measure_mono hsub
    _ = ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' S) := Measure.prod_apply_symm hS
    _ ≤ ∫⁻ t, c * ENNReal.ofReal a ^ 2 * volume (timeSlice B t) := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ Icc (0 : ℝ) 1
        · have hset : (fun l => (l, t)) ⁻¹' S =
              {l | planar t l ∈ timeSlice B t ∧ velocity l ∈ velBox a v} := by
            ext l
            simp only [S, mem_preimage, mem_ofPred_eq, timeSlice, base_mk]
            exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
          rw [hset]
          calc ν {l | planar t l ∈ timeSlice B t ∧ velocity l ∈ velBox a v}
              ≤ c * volume (timeSlice B t) * volume (velBox a v) := hJ t ht _ _
            _ = c * ENNReal.ofReal a ^ 2 * volume (timeSlice B t) := by
                rw [volume_velBox ha]; ring
        · have hset : (fun l => (l, t)) ⁻¹' S = ∅ := by
            ext l
            simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
            exact fun h => ht h.1
          rw [hset, measure_empty]
          exact bot_le
    _ = c * ENNReal.ofReal a ^ 2 * volume B := by
        rw [lintegral_const_mul _ (measurable_volume_timeSlice hB),
          ← volume_eq_lintegral_timeSlice hB]


/-- Under the joint ceiling with constant `c`, if the observation law at depth `(r, u)` has
density `G` and `c a_u² < λ`, then the selected states whose observation has density `≥ λ`
carry no mass. -/
lemma selected_density_ge_eq_zero (ν : Measure Line) [IsProbabilityMeasure ν] {E : Set State}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {c : ℝ≥0∞} (hJ : JointCeiling ν c) (N r u : ℝ)
    {G : Observation → ℝ≥0∞} (hGm : Measurable G)
    (hG : Measure.map (observe N r u) (selected ν E) = reference.withDensity G)
    {lam : ℝ≥0∞} (hlam : c * ENNReal.ofReal (width N u) ^ 2 < lam) :
    selected ν E {p | lam ≤ G (observe N r u p)} = 0 := by
  set Q := Measure.map (observe N r u) (selected ν E) with hQ_def
  set c₀ := c * ENNReal.ofReal (width N u) ^ 2 with hc₀
  let L : Set Observation := {x | lam ≤ G x}
  have hL : MeasurableSet L := measurableSet_le measurable_const hGm
  have hQL : Q L = selected ν E {p | lam ≤ G (observe N r u p)} :=
    Measure.map_apply (measurable_observe N r u) hL
  have hup : Q L ≤ c₀ * reference L :=
    measure_le_mul_reference Q c₀ (fun B hB h v => map_observe_cell_le ν hE hJ N r u hB h v) hL
  have hlow : lam * reference L ≤ Q L := by
    rw [hG, withDensity_apply _ hL, ← setLIntegral_const]
    exact setLIntegral_mono hGm (fun x hx => hx)
  have hfin : Q L < ∞ := by
    calc Q L ≤ Q univ := measure_mono (subset_univ _)
      _ = selected ν E univ := Measure.map_apply (measurable_observe N r u) MeasurableSet.univ
      _ ≤ 1 := selected_mass_le_one ν E hE
      _ < ∞ := ENNReal.one_lt_top
  have hlam0 : lam ≠ 0 := (lt_of_le_of_lt bot_le hlam).ne'
  have hrefL : reference L = 0 := by
    by_contra hne
    have hrefFin : reference L ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.mul_top hlam0] at hlow
      exact absurd (lt_of_le_of_lt hlow hfin) (lt_irrefl _)
    have h1 : lam * reference L ≤ c₀ * reference L := hlow.trans hup
    exact absurd ((ENNReal.mul_le_mul_iff_left hne hrefFin).mp h1) (not_le.2 hlam)
  rw [← hQL]
  exact le_antisymm (hup.trans (by rw [hrefL, mul_zero])) bot_le

/-- Part (3) of the density bounds: under the joint `(y(t), V)` ceiling `Λ N²`, the homogeneous
profile satisfies `F(r, u) ≥ 2u - 2` on `[0,1] × [0,4]`. -/
theorem two_mul_sub_two_le_profile (N K Λ : ℕ → ℝ) (ν : ℕ → Measure Line) (E : ℕ → Set State)
    (F : ℝ → ℝ → ℝ)
    (hN2 : ∀ k, 2 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hK1 : ∀ k, 1 ≤ K k) (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Λ k ≤ N k ^ ε)
    (hprob : ∀ k, IsProbabilityMeasure (ν k))
    (hE : ∀ k, E k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hmass : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ selected (ν k) (E k) univ)
    (hJ : ∀ k, JointCeiling (ν k) (ENNReal.ofReal (Λ k * N k ^ 2)))
    (hdens : ∀ k (r u : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → ∃ G : Observation → ℝ≥0∞,
      Measurable G ∧
        Measure.map (observe (N k) r u) (selected (ν k) (E k)) = reference.withDensity G)
    (htyp : ∀ r u τ : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 0 < τ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in atTop, ∀ G : Observation → ℝ≥0∞, Measurable G →
        Measure.map (observe (N k) r u) (selected (ν k) (E k)) = reference.withDensity G →
        selected (ν k) (E k) {p | G (observe (N k) r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨
          ENNReal.ofReal (N k ^ (-F r u + τ)) < G (observe (N k) r u p)} ≤
          ENNReal.ofReal (N k ^ (-c))) :
    ∀ r u : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 2 * u - 2 ≤ F r u := by
  intro r u hr0 hr1 hu0 hu4
  by_contra hlt
  push Not at hlt
  set δ := 2 * u - 2 - F r u with hδ
  have hδpos : 0 < δ := by linarith
  obtain ⟨c, hc, hev⟩ := htyp r u (δ / 4) hr0 hr1 hu0 hu4 (by positivity)
  have hNev : ∀ᶠ k in atTop, 4 < N k ^ (δ / 2) :=
    ((tendsto_rpow_atTop (by positivity)).comp hNtop).eventually_gt_atTop 4
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    (hev.and ((hK (c / 2) (by positivity)).and ((hΛ (δ / 4) (by positivity)).and hNev))).exists
  have := hprob k
  obtain ⟨G, hGm, hG⟩ := hdens k r u hr0 hr1 hu0 hu4
  set n := N k with hn
  have hn1 : 1 < n := by linarith [hN2 k]
  have hn0 : 0 < n := by linarith
  set lam := ENNReal.ofReal (n ^ (-F r u - δ / 4)) with hlam_def
  -- the ceiling is below the typical density
  have hceil : ENNReal.ofReal (Λ k * n ^ 2) * ENNReal.ofReal (width n u) ^ 2 < lam := by
    have hw := (width_bounds hn0 u).2
    have hw0 := width_pos n u
    have hF : F r u = 2 * u - 2 - δ := by rw [hδ]; ring
    have hreal : n ^ (δ / 4) * n ^ 2 * width n u ^ 2 < n ^ (-F r u - δ / 4) := by
      calc n ^ (δ / 4) * n ^ 2 * width n u ^ 2
          ≤ n ^ (δ / 4) * n ^ 2 * (2 * n ^ (-u)) ^ 2 := by gcongr
        _ = 4 * n ^ (δ / 4 + 2 + -u + -u) := by
            rw [Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_two]
            ring
        _ < n ^ (δ / 2) * n ^ (δ / 4 + 2 + -u + -u) := by
            gcongr
        _ = n ^ (-F r u - δ / 4) := by
            rw [← Real.rpow_add hn0, hF]
            congr 1
            ring
    calc ENNReal.ofReal (Λ k * n ^ 2) * ENNReal.ofReal (width n u) ^ 2
        ≤ ENNReal.ofReal (n ^ (δ / 4) * n ^ 2) * ENNReal.ofReal (width n u) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (n ^ (δ / 4) * n ^ 2 * width n u ^ 2) := by
          rw [← ENNReal.ofReal_pow hw0.le, ← ENNReal.ofReal_mul (by positivity)]
      _ < lam := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal
  have hzero := selected_density_ge_eq_zero (ν k) (hE k) (hJ k) n r u hGm hG hceil
  have hsplit : selected (ν k) (E k) univ ≤ selected (ν k) (E k)
      {p | G (observe n r u p) < ENNReal.ofReal (n ^ (-F r u - δ / 4)) ∨
          ENNReal.ofReal (n ^ (-F r u + δ / 4)) < G (observe n r u p)} := by
    calc selected (ν k) (E k) univ
        ≤ selected (ν k) (E k) ({p | G (observe n r u p) < lam} ∪
            {p | lam ≤ G (observe n r u p)}) := by
          refine measure_mono fun p _ => ?_
          by_cases h : G (observe n r u p) < lam
          · exact Or.inl h
          · exact Or.inr (not_lt.1 h)
      _ ≤ selected (ν k) (E k) {p | G (observe n r u p) < lam} +
            selected (ν k) (E k) {p | lam ≤ G (observe n r u p)} := measure_union_le _ _
      _ = selected (ν k) (E k) {p | G (observe n r u p) < lam} := by rw [hzero, add_zero]
      _ ≤ _ := measure_mono fun p hp => Or.inl hp
  have hbound := (hmass k).trans (hsplit.trans (hk1 G hGm hG))
  -- but 1/K ≥ n^(-c/2) > n^(-c)
  have hKpos : 0 < K k := by linarith [hK1 k]
  have hlow : n ^ (-c) < (K k)⁻¹ := by
    calc n ^ (-c) < n ^ (-(c / 2)) := Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith)
      _ = (n ^ (c / 2))⁻¹ := Real.rpow_neg hn0.le _
      _ ≤ (K k)⁻¹ := inv_anti₀ hKpos hk2
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound
  linarith

end Submission.Obl.k4_profile_density_bounds
