import Submission.Obl.k4_raw_localized_native_systems.Window.ChartVelocity
import Submission.Obl.k4_raw_localized_native_systems.Pairing.CQ1Compare
import Submission.Obl.k4_raw_localized_native_systems.Pairing.OperatorNorm

/-!
# Good sets of the full-time charts and their weighted omission

A full-time chart `a` (unit normal `nC a`) is *compatible* with an earlier
witness chart `e` when both lie in the same world, the full-time normal is
within `θ` of the earlier minor normal up to sign, and the earlier major axis is
at least `lam`.  The good set of `a` is the raw support set: its incidences
that lie in the trimmed event `H e` of a compatible earlier witness.

Every full-time incidence lies in the event of an earlier witness of its world
(ancestry).  Outside the good set it therefore lies in the trimmed-away part of
that witness, or fails the terminal angular/typicality test, or pairs a
full-time label with a transverse earlier label (angular charging of the pinned
velocity, `transverse_pair_mass_le`), or lies in an earlier witness with a short
major axis (angular charging of the pinned centre velocity).  Summing with the
original world weights gives `good_set_omission`, with no factor of the number of
charts of either family.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

variable {p : Data} {k : ℕ}

/-- Compatibility of a full-time chart with an earlier witness chart. -/
def angleCompat (W : Atlas p k) {C : ℕ} (γC : Fin C → Fin (p.W k)) (nC : Fin C → Plane)
    (θ lam : ℝ) (a : Fin C) (e : Fin W.C) : Prop :=
  W.γ e = γC a ∧ min ‖nC a - minorNormal (W.Q e)‖ ‖nC a + minorNormal (W.Q e)‖ ≤ θ ∧
    lam ≤ ‖longCol (W.Q e)‖

theorem angleCompat_world {W : Atlas p k} {C : ℕ} {γC : Fin C → Fin (p.W k)}
    {nC : Fin C → Plane} {θ lam : ℝ} {a : Fin C} {e : Fin W.C}
    (h : angleCompat W γC nC θ lam a e) : W.γ e = γC a := h.1

/-- The selected law of a world has mass at most one. -/
theorem selected_univ_le_one (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) :
    selected p k γ Set.univ ≤ 1 := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hEs : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
  have : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
  unfold selected priorMass
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  calc ((p.ν k γ).prod volume) (p.E k γ) ≤
        ((p.ν k γ).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hEs
    _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp

theorem priorMass_eq_selected_of_subset (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {Z : Set Point} (hZ : Z ⊆ p.E k γ) : priorMass p k γ Z = selected p k γ Z := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hEm : MeasurableSet (p.E k γ) := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  rw [selected, Measure.restrict_apply' hEm, Set.inter_eq_left.mpr hZ]

/-! ### Earlier witnesses with a short major axis -/

/-- Velocity bins pinned by listed earlier witnesses with a short major axis. -/
def earlierShortBins (W : Atlas p k) (lst₁ : Observation → Finset (Fin W.C)) (lam w : ℝ)
    (o : Observation) : Finset (Fin 2 → ℤ) := by
  classical
  exact ((lst₁ o).filter (fun e => ‖longCol (W.Q e)‖ < lam)).biUnion
    fun e => nbhd (binOf w (W.u e))

theorem card_earlierShortBins_le (W : Atlas p k) (lst₁ : Observation → Finset (Fin W.C))
    (lam w : ℝ) (o : Observation) {m : ℕ} (hm : (lst₁ o).card ≤ m) :
    (earlierShortBins W lst₁ lam w o).card ≤ 9 * m := by
  classical
  unfold earlierShortBins
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ e ∈ (lst₁ o).filter (fun e => ‖longCol (W.Q e)‖ < lam), (nbhd (binOf w (W.u e))).card
      ≤ ∑ _e ∈ (lst₁ o).filter (fun e => ‖longCol (W.Q e)‖ < lam), 9 :=
        Finset.sum_le_sum fun e _ => card_nbhd_le _
    _ = 9 * ((lst₁ o).filter (fun e => ‖longCol (W.Q e)‖ < lam)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * m := by gcongr; exact (Finset.card_filter_le _ _).trans hm

theorem measurableSet_earlierShortBins (W : Atlas p k) (lst₁ : Observation → Finset (Fin W.C))
    (lam w : ℝ) (hmeas : ∀ e, MeasurableSet {o | e ∈ lst₁ o}) (z : Fin 2 → ℤ) :
    MeasurableSet {o | z ∈ earlierShortBins W lst₁ lam w o} := by
  classical
  have : {o | z ∈ earlierShortBins W lst₁ lam w o} =
      ⋃ e : Fin W.C, {o | (‖longCol (W.Q e)‖ < lam ∧ z ∈ nbhd (binOf w (W.u e))) ∧
        e ∈ lst₁ o} := by
    ext o
    simp only [earlierShortBins, Finset.mem_biUnion, Finset.mem_filter, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨e, ⟨he, hs⟩, hz⟩; exact ⟨e, ⟨hs, hz⟩, he⟩
    · rintro ⟨e, ⟨hs, hz⟩, he⟩; exact ⟨e, ⟨he, hs⟩, hz⟩
  rw [this]
  refine MeasurableSet.iUnion fun e => ?_
  by_cases h : ‖longCol (W.Q e)‖ < lam ∧ z ∈ nbhd (binOf w (W.u e))
  · have : {o | (‖longCol (W.Q e)‖ < lam ∧ z ∈ nbhd (binOf w (W.u e))) ∧ e ∈ lst₁ o} =
        {o | e ∈ lst₁ o} := by ext o; simp [h]
    rw [this]; exact hmeas e
  · have : {o | (‖longCol (W.Q e)‖ < lam ∧ z ∈ nbhd (binOf w (W.u e))) ∧ e ∈ lst₁ o} = ∅ := by
      ext o; simp [h]
    rw [this]; exact MeasurableSet.empty

/-- Velocities of an earlier witness are within `4 κ 2^T ‖longCol Q‖` of its centre velocity. -/
theorem WChart.velocity_near_centre {M D : ℕ} {κ r : ℝ} {W : Atlas p k} {e : Fin W.C}
    (hW : WChart p k W M D κ r e) {l : Line} (hl : l ∈ W.A e) :
    ‖v l - W.u e‖ ≤ 4 * κ * (2 : ℝ) ^ W.T * ‖longCol (W.Q e)‖ := by
  have heq : v l - W.u e = Matrix.toEuclideanLin (W.Q e)
      (Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (W.Q e) hW.det_ne _).symm
  rw [heq]
  refine (norm_toEuclideanLin_le_longCol _ _).trans ?_
  calc 2 * ‖longCol (W.Q e)‖ * ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)‖
      ≤ 2 * ‖longCol (W.Q e)‖ * (2 * κ * (2 : ℝ) ^ W.T) := by
        gcongr; exact hW.velocity_inverse hl
    _ = 4 * κ * (2 : ℝ) ^ W.T * ‖longCol (W.Q e)‖ := by ring

/-- **Earlier witnesses with a short major axis carry little angular-good mass.** -/
theorem earlier_short_mass_le (hp : Valid p) (W : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r₁ : ℝ} (hW : ∀ e, WChart p k W M D κ r₁ e) (hr₁ : 0 ≤ r₁) (hr₁L : r₁ ≤ p.L)
    (lst₁ : Observation → Finset (Fin W.C)) (κ₁ : ℕ) (hcard : ∀ o, (lst₁ o).card ≤ κ₁)
    (hmeas : ∀ e, MeasurableSet {o | e ∈ lst₁ o})
    (hknown : ∀ e, W.γ e = γ → ∀ z ∈ W.F e, e ∈ lst₁ (obs (p.B k γ) (δ (p.N k) r₁) z))
    {u τ lam : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hshort : 4 * κ * (2 : ℝ) ^ W.T * lam ≤ δ (p.N k) u) :
    selected p k γ {z | AngGood p k γ u τ z ∧
        ∃ e, W.γ e = γ ∧ z ∈ W.F e ∧ ‖longCol (W.Q e)‖ < lam} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κ₁ : ℕ) : ENNReal) := by
  classical
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  have hδu : 0 < δ (p.N k) u := by unfold δ; positivity
  set n := Submission.Lib.K4XInterface.depthIdx (p.N k) p.L -
    Submission.Lib.K4XInterface.depthIdx (p.N k) r₁ with hn
  set co := Submission.Lib.K4XInterface.coarsenObs n with hco
  have hcom : Measurable co := measurable_coarsenObs n
  set bins := fun o => earlierShortBins W lst₁ lam (δ (p.N k) u) (co o) with hbins
  have hsub : {z | AngGood p k γ u τ z ∧
        ∃ e, W.γ e = γ ∧ z ∈ W.F e ∧ ‖longCol (W.Q e)‖ < lam} ⊆
      {z | AngGood p k γ u τ z ∧ velBin (p.N k) u z ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) z)} := by
    rintro z ⟨hgood, e, hγ, hze, hsh⟩
    refine ⟨hgood, ?_⟩
    have hco_eq : obs (p.B k γ) (δ (p.N k) r₁) z = co (obs (p.B k γ) (δ (p.N k) p.L) z) :=
      Submission.Lib.K4XInterface.gobs_coarsen hN1 hr₁ hr₁L (p.B k γ) z
    have hle := hknown e hγ z hze
    rw [hco_eq] at hle
    simp only [hbins, earlierShortBins, Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨e, ⟨hle, hsh⟩, ?_⟩
    have hA : z.1 ∈ W.A e := ((hW e).sel hze).2.1
    have hnear := (hW e).velocity_near_centre hA
    have hκ : 0 ≤ κ := le_trans (norm_nonneg _) ((hW e).fit hA ((hW e).sel hze).2.2.1).1
    have hclose : ‖v z.1 - W.u e‖ ≤ δ (p.N k) u := by
      refine hnear.trans (le_trans ?_ hshort)
      gcongr
    exact binOf_mem_nbhd hδu hclose
  refine (measure_mono hsub).trans ?_
  have h := angular_listed_le hp k γ (τ := τ) hu huη bins (9 * κ₁)
    (fun w => hcom (measurableSet_earlierShortBins W lst₁ lam (δ (p.N k) u) hmeas w))
    (fun o => card_earlierShortBins_le W lst₁ lam (δ (p.N k) u) (co o) (hcard (co o)))
  refine h.trans ?_
  calc ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κ₁ : ℕ) : ENNReal) *
        selected p k γ Set.univ
      ≤ ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κ₁ : ℕ) : ENNReal) * 1 := by
        gcongr; exact selected_univ_le_one hp k γ
    _ = _ := mul_one _

/-! ### The good sets and their weighted omission -/

/-- The world restriction of a family of events. -/
def worldPart {ι : Type*} (w : ι → Fin (p.W k)) (F : ι → Set Point) (γ : Fin (p.W k))
    (i : ι) : Set Point :=
  if w i = γ then F i else ∅

theorem mem_worldPart {ι : Type*} {w : ι → Fin (p.W k)} {F : ι → Set Point} {γ : Fin (p.W k)}
    {i : ι} {z : Point} : z ∈ worldPart w F γ i ↔ w i = γ ∧ z ∈ F i := by
  unfold worldPart
  split_ifs with h <;> simp [h]

/-- The earlier normal speed of an incidence matches the minor-normal component of
the earlier centre velocity up to `minorWidth · 2κ 2^T`. -/
theorem WChart.minor_speed_le {M D : ℕ} {κ r : ℝ} {W : Atlas p k} {e : Fin W.C}
    (hW : WChart p k W M D κ r e) {l : Line} (hl : l ∈ W.A e) :
    |inner ℝ (minorNormal (W.Q e)) (v l) - inner ℝ (minorNormal (W.Q e)) (W.u e)| ≤
      minorWidth (W.Q e) * (2 * κ * (2 : ℝ) ^ W.T) := by
  have heq : v l - W.u e = Matrix.toEuclideanLin (W.Q e)
      (Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (W.Q e) hW.det_ne _).symm
  rw [← inner_sub_right, heq]
  refine (abs_inner_minorNormal_le hW.det_ne _).trans ?_
  exact mul_le_mul_of_nonneg_left (hW.velocity_inverse hl) (minorWidth_nonneg _)

set_option maxHeartbeats 1000000 in
/-- **Weighted omission of the good sets.**  The original-weighted mass of the
full-time events outside their good sets is at most the original-weighted
mass trimmed from the earlier witnesses, plus the original-weighted mass failing
the terminal angular/typicality test, plus `N^(-S u + 2τ) (9 κ_C κ₁ + 9 κ₁)`. -/
theorem good_set_omission (hp : Valid p) (W : Atlas p k) {M D : ℕ}
    {κ r₁ u τ θ lam ρ σ : ℝ}
    (hW : ∀ e, WChart p k W M D κ r₁ e) (hr₁ : 0 ≤ r₁) (hr₁L : r₁ ≤ p.L)
    (lst₁ : Fin (p.W k) → Observation → Finset (Fin W.C)) (κ₁ : ℕ)
    (hcard₁ : ∀ γ o, (lst₁ γ o).card ≤ κ₁) (hmeas₁ : ∀ γ e, MeasurableSet {o | e ∈ lst₁ γ o})
    (hknown₁ : ∀ e, ∀ z ∈ W.F e, e ∈ lst₁ (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) r₁) z))
    (H : Fin W.C → Set Point) (hH : ∀ e, MeasurableSet (H e)) (hHsub : ∀ e, H e ⊆ W.F e)
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (hFC : ∀ a, MeasurableSet (FC a)) (hFCE : ∀ a, FC a ⊆ p.E k (γC a))
    (hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (lstC : Fin (p.W k) → Observation → Finset (Fin C)) (κC : ℕ)
    (hcardC : ∀ γ o, (lstC γ o).card ≤ κC) (hmeasC : ∀ γ c, MeasurableSet {o | c ∈ lstC γ o})
    (hknownC : ∀ a, ∀ z ∈ FC a, a ∈ lstC (γC a) (obs (p.B k (γC a)) (δ (p.N k) p.L) z))
    (nC : Fin C → Plane) (spC : Fin C → ℝ) (hnC : ∀ a, ‖nC a‖ = 1)
    (hspC : ∀ a, ∀ z ∈ FC a, |inner ℝ (nC a) (v z.1) - spC a| ≤ ρ)
    (hanc : ∀ a, ∀ z ∈ FC a, ∃ e, W.γ e = γC a ∧ z ∈ W.F e)
    (hu : 0 < u) (huη : u ≤ p.η * p.L) (hθ : 0 < θ)
    (hσ : ∀ e, minorWidth (W.Q e) * (2 * κ * (2 : ℝ) ^ W.T) ≤ σ)
    (hpin : 4 * (ρ + σ) / θ ≤ δ (p.N k) u)
    (hshort : 4 * κ * (2 : ℝ) ^ W.T * lam ≤ δ (p.N k) u) :
    ∑ a, ENNReal.ofReal (p.ω k (γC a)) *
        priorMass p k (γC a) (FC a \ rawSupportSet W H (angleCompat W γC nC θ lam) FC a) ≤
      (∑ γ, ENNReal.ofReal (p.ω k γ) *
          priorMass p k γ (⋃ e ∈ Finset.univ.filter (fun e => W.γ e = γ), (W.F e \ H e))) +
      (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ {z | ¬ AngGood p k γ u τ z}) +
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) := by
  classical
  set Compat := angleCompat W γC nC θ lam
  set G := rawSupportSet W H Compat FC
  set c₀ := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ))
  have hG : ∀ a, MeasurableSet (G a) := fun a =>
    measurableSet_certSupport (rawAtlas W H) Compat hH hFC a
  -- the per-world bound
  have hworld : ∀ γ : Fin (p.W k),
      priorMass p k γ (⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), (FC a \ G a)) ≤
        priorMass p k γ (⋃ e ∈ Finset.univ.filter (fun e => W.γ e = γ), (W.F e \ H e)) +
          selected p k γ {z | ¬ AngGood p k γ u τ z} +
          c₀ * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) := by
    intro γ
    set X := ⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), (FC a \ G a) with hX
    set T₁ := ⋃ e ∈ Finset.univ.filter (fun e => W.γ e = γ), (W.F e \ H e) with hT₁
    set T₂ := {z | ¬ AngGood p k γ u τ z}
    set T₃ := {z | AngGood p k γ u τ z ∧ ∃ c e, z ∈ worldPart γC FC γ c ∧
      z ∈ worldPart W.γ W.F γ e ∧
      θ < min ‖nC c - minorNormal (W.Q e)‖ ‖nC c + minorNormal (W.Q e)‖}
    set T₄ := {z | AngGood p k γ u τ z ∧
      ∃ e, W.γ e = γ ∧ z ∈ W.F e ∧ ‖longCol (W.Q e)‖ < lam}
    have hXE : X ⊆ p.E k γ := by
      intro z hz
      simp only [hX, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨a, ha, hzFC, -⟩ := hz
      have := hFCE a hzFC
      rwa [ha] at this
    have hsub : X ⊆ T₁ ∪ T₂ ∪ T₃ ∪ T₄ := by
      intro z hz
      simp only [hX, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨a, ha, hzFC, hzG⟩ := hz
      obtain ⟨e, hγe, hzF⟩ := hanc a z hzFC
      by_cases hzH : z ∈ H e
      · by_cases hgood : AngGood p k γ u τ z
        · have hnc : ¬ Compat a e := by
            intro hc
            apply hzG
            refine ⟨hzFC, Set.mem_iUnion.mpr ⟨e, hc, hzH⟩⟩
          have hγ' : W.γ e = γ := hγe.trans ha
          by_cases hang : min ‖nC a - minorNormal (W.Q e)‖ ‖nC a + minorNormal (W.Q e)‖ ≤ θ
          · have hshortL : ‖longCol (W.Q e)‖ < lam := by
              by_contra hl
              exact hnc ⟨hγe, hang, not_lt.mp hl⟩
            exact Or.inr ⟨hgood, e, hγ', hzF, hshortL⟩
          · refine Or.inl (Or.inr ⟨hgood, a, e, mem_worldPart.mpr ⟨ha, hzFC⟩,
              mem_worldPart.mpr ⟨hγ', hzF⟩, not_le.mp hang⟩)
        · exact Or.inl (Or.inl (Or.inr hgood))
      · refine Or.inl (Or.inl (Or.inl ?_))
        simp only [hT₁, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hγe.trans ha, hzF, hzH⟩
    -- transverse pairs
    have h₃ : selected p k γ T₃ ≤ c₀ * ((9 * κC * κ₁ : ℕ) : ENNReal) := by
      refine transverse_pair_mass_le hp k γ hu huη nC spC (worldPart γC FC γ) (lstC γ) κC
        (hcardC γ) (hmeasC γ) (fun e => minorNormal (W.Q e))
        (fun e => inner ℝ (minorNormal (W.Q e)) (W.u e)) (worldPart W.γ W.F γ) (lst₁ γ) κ₁
        (hcard₁ γ) (hmeas₁ γ) hr₁ hr₁L ?_ ?_ hθ hpin hnC
        (fun e => norm_minorNormal (hW e).det_ne) ?_ ?_
      · intro c z hz
        obtain ⟨hcγ, hzc⟩ := mem_worldPart.mp hz
        have := hknownC c z hzc
        rwa [hcγ] at this
      · intro e z hz
        obtain ⟨heγ, hze⟩ := mem_worldPart.mp hz
        have := hknown₁ e z hze
        rwa [heγ] at this
      · intro c z hz
        exact hspC c z (mem_worldPart.mp hz).2
      · intro e z hz
        have hze := (mem_worldPart.mp hz).2
        exact ((hW e).minor_speed_le ((hW e).sel hze).2.1).trans (hσ e)
    -- short earlier major axes
    have h₄ : selected p k γ T₄ ≤ c₀ * ((9 * κ₁ : ℕ) : ENNReal) :=
      earlier_short_mass_le hp W γ hW hr₁ hr₁L (lst₁ γ) κ₁ (hcard₁ γ) (hmeas₁ γ)
        (fun e he z hz => by have := hknown₁ e z hz; rwa [he] at this) hu huη hshort
    have hT₁sel : selected p k γ T₁ ≤ priorMass p k γ T₁ := by
      rw [selected]; exact Measure.restrict_le_self _
    calc priorMass p k γ X = selected p k γ X := priorMass_eq_selected_of_subset hp k γ hXE
      _ ≤ selected p k γ (T₁ ∪ T₂ ∪ T₃ ∪ T₄) := measure_mono hsub
      _ ≤ selected p k γ T₁ + selected p k γ T₂ + selected p k γ T₃ + selected p k γ T₄ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ priorMass p k γ T₁ + selected p k γ T₂ + c₀ * ((9 * κC * κ₁ : ℕ) : ENNReal) +
          c₀ * ((9 * κ₁ : ℕ) : ENNReal) := by gcongr
      _ = priorMass p k γ T₁ + selected p k γ T₂ +
          c₀ * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) := by
          rw [add_assoc _ (c₀ * _), ← mul_add]
          push_cast
          ring
  -- group by worlds
  have hgroup : ∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (FC a \ G a) =
      ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) *
        priorMass p k γ (⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), (FC a \ G a)) := by
    rw [← Finset.sum_fiberwise Finset.univ γC]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [measure_biUnion_finset, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [ha]
    · intro a ha a' ha' hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ha'
      exact (hFCdisj a a' hne (ha.trans ha'.symm)).mono Set.diff_subset Set.diff_subset
    · exact fun a _ => (hFC a).diff (hG a)
  rw [hgroup]
  have hω1 : ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => valid_omega_nonneg hp k γ),
      valid_omega_sum hp k, ENNReal.ofReal_one]
  calc ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) *
        priorMass p k γ (⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), (FC a \ G a))
      ≤ ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) *
        (priorMass p k γ (⋃ e ∈ Finset.univ.filter (fun e => W.γ e = γ), (W.F e \ H e)) +
          selected p k γ {z | ¬ AngGood p k γ u τ z} +
          c₀ * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal)) :=
        Finset.sum_le_sum fun γ _ => by gcongr; exact hworld γ
    _ = (∑ γ, ENNReal.ofReal (p.ω k γ) *
          priorMass p k γ (⋃ e ∈ Finset.univ.filter (fun e => W.γ e = γ), (W.F e \ H e))) +
        (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ {z | ¬ AngGood p k γ u τ z}) +
        (∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ)) *
          (c₀ * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal)) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by rw [hω1, one_mul]

end
end Submission.Obl.k4_raw_localized_native_systems.Window
