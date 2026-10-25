import Submission.Obl.k4_scalar_candidate_original_return.Core.LayerMass
import Submission.Obl.k4_scalar_candidate_original_return.Core.Prune

/-!
# Residual tangent inputs

Removing a light set `Z` of incidences (weighted mass at most `1/(4H)`) and pruning light
planks over all layers leaves a valid scalar tangent input with slack `4 K H²`, whose planks
are sub-families of the original layers.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set

namespace PreparedData

noncomputable section

section Planks

variable (a : PreparedData)

/-- All planks of all layers at stage `k`. -/
abbrev PlankIdx (k : ℕ) : Type := Σ ℓ : Fin (a.ct k), Fin (a.ls k ℓ).n

/-- The world of a plank. -/
def plankWorld (k : ℕ) (p : a.PlankIdx k) : Fin (a.Wk k) := (a.ls k p.1).world p.2

/-- The incidence region of a plank. -/
def plankRegion (k : ℕ) (p : a.PlankIdx k) : Set Inc := a.plank k p.1 p.2

/-- The pruning floor `ν(A) / (4 K H² 2^T)` of a plank. -/
noncomputable def plankFloor (k : ℕ) (p : a.PlankIdx k) : ENNReal :=
  ENNReal.ofReal ((4 * a.rK k * a.H k ^ 2 * (2 : ℝ) ^ (a.ls k p.1).T)⁻¹) *
    ν (a.p k) (a.sm k) (a.plankWorld k p) ((a.ls k p.1).prior p.2)

/-- The common support, in world `g`, of a family of planks of all layers. -/
def resSupport (k : ℕ) (S : Finset (a.PlankIdx k)) (g : Fin (a.Wk k)) : Set Inc :=
  Prune.support (fun q : a.PlankIdx k => q.1) (a.plankWorld k) (a.plankRegion k) S g

end Planks

section Proofs

variable {a : PreparedData} (ha : a.Valid)
include ha

theorem plankRegion_measurable (k : ℕ) (p : a.PlankIdx k) :
    MeasurableSet (a.plankRegion k p) := by
  have h := ((ha.layer k p.1).2.2.1.2.2.1 p.2).1
  exact h.prod measurableSet_Icc

theorem resSupport_measurable (k : ℕ) (S : Finset (a.PlankIdx k)) (g : Fin (a.Wk k)) :
    MeasurableSet (a.resSupport k S g) := by
  classical
  unfold resSupport Prune.support
  exact MeasurableSet.iInter fun ℓ =>
    Finset.measurableSet_biUnion _ fun p _ => plankRegion_measurable ha k p

theorem rho_isFinite (k : ℕ) (g : Fin (a.Wk k)) : IsFiniteMeasure (a.ρ k g) := by
  obtain ⟨_, _, _, _, _, _, _, _, h9, _, _⟩ := ha.tangent_input
  obtain ⟨hν, _, _, hle, hsupp⟩ := (h9 k).2.2.1 g
  have := hν
  constructor
  calc a.ρ k g univ ≤ a.ρ k g (univ ×ˢ Icc (0 : ℝ) 1) + a.ρ k g (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
        measure_univ_le_add_compl _
    _ = a.ρ k g (univ ×ˢ Icc (0 : ℝ) 1) := by rw [hsupp, add_zero]
    _ ≤ (ENNReal.ofReal (a.rK k) • ((ν (a.p k) (a.sm k) g).prod volume))
          (univ ×ˢ Icc (0 : ℝ) 1) := Measure.le_iff'.1 hle _
    _ < ⊤ := by
      rw [Measure.smul_apply, Measure.prod_prod, measure_univ, Real.volume_Icc, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

theorem exists_residual_family (Z : (k : ℕ) → Fin (a.Wk k) → Set Inc) (k : ℕ) :
    ∃ S : Finset (a.PlankIdx k),
      (∀ p ∈ S, a.plankFloor k p ≤
        (((a.ρ k (a.plankWorld k p)).restrict (Z k (a.plankWorld k p))ᶜ).restrict
          (a.resSupport k S (a.plankWorld k p))) (a.plankRegion k p)) ∧
      ∀ g, ((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k Finset.univ g) ≤
        ((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k S g) +
          ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p := by
  have : ∀ g, IsFiniteMeasure ((a.ρ k g).restrict (Z k g)ᶜ) := fun g => by
    have := rho_isFinite ha k g
    infer_instance
  exact Prune.exists_pruned (fun q : a.PlankIdx k => q.1) (a.plankWorld k) (a.plankRegion k)
    (plankRegion_measurable ha k) (fun g => (a.ρ k g).restrict (Z k g)ᶜ) (a.plankFloor k)

/-- The support of the full family carries all of the original law. -/
theorem rho_resSupport_univ_compl (k : ℕ) (g : Fin (a.Wk k)) :
    a.ρ k g (a.resSupport k Finset.univ g)ᶜ = 0 := by
  classical
  have hsub : (a.resSupport k Finset.univ g)ᶜ ⊆
      ⋃ ℓ : Fin (a.ct k),
        (⋃ (i : Fin (a.ls k ℓ).n) (_ : (a.ls k ℓ).world i = g), a.plank k ℓ i)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff] at hz
    rw [resSupport, Prune.mem_support] at hz
    push Not at hz
    obtain ⟨ℓ, hℓ⟩ := hz
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists]
    refine ⟨ℓ, fun i hi hzi => ?_⟩
    exact hℓ ⟨ℓ, i⟩ (Finset.mem_univ _) rfl hi hzi
  exact measure_mono_null hsub (measure_iUnion_null fun ℓ => rho_compl_planks ha k ℓ g)

/-- The pruning floors of all layers sum, with the mixture weights, to at most `1/(4H)`. -/
theorem weighted_floor_le (k : ℕ) :
    ∑ g : Fin (a.Wk k), ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
        ∑ p ∈ Finset.univ.filter (fun p : a.PlankIdx k => a.plankWorld k p = g),
          a.plankFloor k p ≤
      ENNReal.ofReal ((4 * a.H k)⁻¹) := by
  classical
  obtain ⟨_, _, ⟨h3a, _⟩, _⟩ := ha.tangent_input
  have hH : 2 ≤ a.H k := (ha.bounds k).2.2.1
  have hct : (a.ct k : ℝ) ≤ a.H k := (ha.bounds k).2.2.2.2.2.2.2.2.2.1
  have hrK : 1 ≤ a.rK k := h3a k
  set K' : ℝ := 4 * a.rK k * a.H k ^ 2 with hK'
  have hK'pos : 0 < K' := by positivity
  -- regroup by planks
  have hregroup : ∑ g : Fin (a.Wk k), ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
        ∑ p ∈ Finset.univ.filter (fun p : a.PlankIdx k => a.plankWorld k p = g),
          a.plankFloor k p =
      ∑ p : a.PlankIdx k, ENNReal.ofReal (ω (a.p k) (a.sm k) (a.plankWorld k p)) *
        a.plankFloor k p := by
    rw [← Finset.sum_fiberwise Finset.univ (a.plankWorld k)
      (fun p => ENNReal.ofReal (ω (a.p k) (a.sm k) (a.plankWorld k p)) * a.plankFloor k p)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.1 hp).2]
  rw [hregroup, Fintype.sum_sigma]
  -- each layer contributes at most `1/K'`
  have hlayer : ∀ ℓ : Fin (a.ct k),
      ∑ i : Fin (a.ls k ℓ).n,
          ENNReal.ofReal (ω (a.p k) (a.sm k) (a.plankWorld k ⟨ℓ, i⟩)) *
            a.plankFloor k ⟨ℓ, i⟩ ≤ ENNReal.ofReal K'⁻¹ := by
    intro ℓ
    have hc : 0 ≤ (K' * (2 : ℝ) ^ (a.ls k ℓ).T)⁻¹ := by positivity
    have hrw : ∀ i : Fin (a.ls k ℓ).n,
        ENNReal.ofReal (ω (a.p k) (a.sm k) (a.plankWorld k ⟨ℓ, i⟩)) * a.plankFloor k ⟨ℓ, i⟩ =
          ENNReal.ofReal (K' * (2 : ℝ) ^ (a.ls k ℓ).T)⁻¹ *
            (ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
              ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)) := by
      intro i
      simp only [plankFloor, plankWorld, hK']
      ring
    rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.mul_sum]
    calc ENNReal.ofReal (K' * (2 : ℝ) ^ (a.ls k ℓ).T)⁻¹ *
          ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
            ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)
        ≤ ENNReal.ofReal (K' * (2 : ℝ) ^ (a.ls k ℓ).T)⁻¹ * (2 : ENNReal) ^ (a.ls k ℓ).T :=
          mul_le_mul_right (layer_weighted_prior_le ha k ℓ) _
      _ = ENNReal.ofReal K'⁻¹ := by
          rw [show (2 : ENNReal) ^ (a.ls k ℓ).T = ENNReal.ofReal ((2 : ℝ) ^ (a.ls k ℓ).T) by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul hc]
          congr 1
          field_simp
  calc ∑ ℓ : Fin (a.ct k), ∑ i : Fin (a.ls k ℓ).n,
          ENNReal.ofReal (ω (a.p k) (a.sm k) (a.plankWorld k ⟨ℓ, i⟩)) * a.plankFloor k ⟨ℓ, i⟩
      ≤ ∑ _ℓ : Fin (a.ct k), ENNReal.ofReal K'⁻¹ := Finset.sum_le_sum fun ℓ _ => hlayer ℓ
    _ = ENNReal.ofReal ((a.ct k : ℝ) * K'⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((4 * a.H k)⁻¹) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hK']
        have hH0 : 0 < a.H k := by linarith
        rw [mul_inv_le_iff₀ (by positivity)]
        calc (a.ct k : ℝ) ≤ a.H k := hct
          _ = (4 * a.H k)⁻¹ * (4 * a.H k ^ 2) := by field_simp
          _ ≤ (4 * a.H k)⁻¹ * (4 * a.rK k * a.H k ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [sq_nonneg (a.H k)]

/-- Total mass of the residual law. -/
theorem residual_mass (Z : (k : ℕ) → Fin (a.Wk k) → Set Inc)
    (hZ : ∀ k g, MeasurableSet (Z k g))
    (hZmass : ∀ k, ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g (Z k g) ≤
      ENNReal.ofReal ((4 * a.H k)⁻¹))
    (k : ℕ) (S : Finset (a.PlankIdx k))
    (hS : ∀ g, ((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k Finset.univ g) ≤
        ((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k S g) +
          ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p) :
    ENNReal.ofReal ((4 * a.rK k * a.H k ^ 2)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
        (((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k S g)) Set.univ := by
  classical
  obtain ⟨_, _, ⟨h3a, _⟩, _⟩ := ha.tangent_input
  have hH : 2 ≤ a.H k := (ha.bounds k).2.2.1
  have hrK : 1 ≤ a.rK k := h3a k
  -- pointwise decomposition of the original mass
  have hpt : ∀ g : Fin (a.Wk k), a.ρ k g univ ≤
      (((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k S g)) univ +
        ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p +
        a.ρ k g (Z k g) := by
    intro g
    have h0 := rho_resSupport_univ_compl ha k g
    calc a.ρ k g univ ≤ a.ρ k g (a.resSupport k Finset.univ g) +
          a.ρ k g (a.resSupport k Finset.univ g)ᶜ := measure_univ_le_add_compl _
      _ = a.ρ k g (a.resSupport k Finset.univ g) := by rw [h0, add_zero]
      _ ≤ a.ρ k g (a.resSupport k Finset.univ g ∩ (Z k g)ᶜ) +
          a.ρ k g (a.resSupport k Finset.univ g \ (Z k g)ᶜ) :=
            measure_le_inter_add_sdiff _ _ _
      _ ≤ ((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k Finset.univ g) + a.ρ k g (Z k g) := by
          rw [Measure.restrict_apply' (hZ k g).compl]
          gcongr
          intro z hz
          simpa using hz.2
      _ ≤ (((a.ρ k g).restrict (Z k g)ᶜ) (a.resSupport k S g) +
          ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p) +
          a.ρ k g (Z k g) := by gcongr; exact hS g
      _ = _ := by rw [Measure.restrict_apply_univ]
  set X := ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
      (((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k S g)) Set.univ with hX
  set b := ENNReal.ofReal ((4 * a.H k)⁻¹) with hb
  have hsum : ENNReal.ofReal (a.H k)⁻¹ ≤ X + (b + b) := by
    calc ENNReal.ofReal (a.H k)⁻¹ ≤ ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g univ :=
          ha.weighted_mass k
      _ ≤ ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
            ((((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k S g)) univ +
              ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p +
              a.ρ k g (Z k g)) := Finset.sum_le_sum fun g _ => mul_le_mul_right (hpt g) _
      _ = X + (∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
              ∑ p ∈ Finset.univ.filter (fun p => a.plankWorld k p = g), a.plankFloor k p +
            ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g (Z k g)) := by
          simp only [mul_add, Finset.sum_add_distrib, hX, add_assoc]
      _ ≤ X + (b + b) := by
          gcongr
          · exact weighted_floor_le ha k
          · exact hZmass k
  have hreal : ENNReal.ofReal (4 * a.rK k * a.H k ^ 2)⁻¹ + (b + b) ≤ ENNReal.ofReal (a.H k)⁻¹ := by
    have hH0 : 0 < a.H k := by linarith
    have h1 : (4 * a.rK k * a.H k ^ 2)⁻¹ ≤ (4 * a.H k)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [sq_nonneg (a.H k)])
    have h2 : (4 * a.H k)⁻¹ = 4⁻¹ * (a.H k)⁻¹ := mul_inv 4 (a.H k)
    have h3 : 0 ≤ (a.H k)⁻¹ := inv_nonneg.2 hH0.le
    rw [hb, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [h2] at h1 ⊢
    linarith
  have hbtop : b + b ≠ ⊤ := by simp [hb]
  exact (ENNReal.add_le_add_iff_right hbtop).1 (hreal.trans hsum)


theorem residual_input (Z : (k : ℕ) → Fin (a.Wk k) → Set Inc)
    (hZ : ∀ k g, MeasurableSet (Z k g))
    (hZmass : ∀ k, ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g (Z k g) ≤
      ENNReal.ofReal ((4 * a.H k)⁻¹)) :
    ∃ (ρ' : (k : ℕ) → Fin (a.Wk k) → Measure Inc) (n' : ℕ → ℝ → ℕ)
      (e : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin (a.ls k (a.nd k s)).n),
      (∀ k s, Function.Injective (e k s)) ∧
      (∀ k g, ρ' k g ≤ (a.ρ k g).restrict (Z k g)ᶜ) ∧
      TangentInput a.tangent (fun k => 4 * a.rK k * a.H k ^ 2) a.rd a.κ a.rS
        (fun k => a.Wk k) (fun k => ω (a.p k) (a.sm k)) (fun k => ν (a.p k) (a.sm k))
        ρ' a.π (fun k s => (a.ls k (a.nd k s)).T) n'
        (fun k s i => (a.ls k (a.nd k s)).world (e k s i))
        (fun k s i => (a.ls k (a.nd k s)).time (e k s i))
        (fun k s i => (a.ls k (a.nd k s)).prior (e k s i))
        (fun k s i => (a.ls k (a.nd k s)).u (e k s i))
        (fun k s i => (a.ls k (a.nd k s)).v (e k s i))
        (fun k s i => (a.ls k (a.nd k s)).poly (e k s i)) := by
  classical
  obtain ⟨h1, h2, ⟨h3a, h3b⟩, h4, h5, h6, h7, h8, h9, h10, h11⟩ := ha.tangent_input
  choose S hheavy hmassS using fun k => exists_residual_family ha Z k
  let fs : (k : ℕ) → (s : ℝ) → Finset (Fin (a.ls k (a.nd k s)).n) := fun k s =>
    Finset.univ.filter (fun i => (⟨a.nd k s, i⟩ : a.PlankIdx k) ∈ S k)
  have hN0 : ∀ k, 0 ≤ a.tangent k := fun k => by linarith [h1 k]
  have hrKpos : ∀ k, 0 < a.rK k := fun k => lt_of_lt_of_le one_pos (h3a k)
  have hrK_le : ∀ k, a.rK k ≤ 4 * a.rK k * a.H k ^ 2 := by
    intro k
    have hH : 2 ≤ a.H k := (ha.bounds k).2.2.1
    have h4H : 1 ≤ 4 * a.H k ^ 2 := by nlinarith
    calc a.rK k = a.rK k * 1 := (mul_one _).symm
      _ ≤ a.rK k * (4 * a.H k ^ 2) := mul_le_mul_of_nonneg_left h4H (hrKpos k).le
      _ = 4 * a.rK k * a.H k ^ 2 := by ring
  refine ⟨fun k g => ((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k (S k) g),
    fun k s => (fs k s).card, fun k s => (fs k s).orderEmbOfFin rfl,
    fun k s => ((fs k s).orderEmbOfFin rfl).injective, fun k g => Measure.restrict_le_self, ?_⟩
  have hρ'le : ∀ k g, ((a.ρ k g).restrict (Z k g)ᶜ).restrict (a.resSupport k (S k) g) ≤
      a.ρ k g := fun k g => Measure.restrict_le_self.trans Measure.restrict_le_self
  refine ⟨h1, h2, ⟨fun k => ?_, fun ε hε => ?_⟩, h4, h5, h6, h7, h8, fun k => ?_,
    fun R hR => ?_, fun R hR => ?_⟩
  · -- the slack is at least one
    exact (h3a k).trans (hrK_le k)
  · -- the slack is subpower
    have hNt : Tendsto (fun k => a.tangent k ^ (ε / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp h2
    filter_upwards [h3b (ε / 3) (by positivity), H_subpower ha (ε / 6) (by positivity),
      hNt.eventually_ge_atTop 4] with k hK hH h4'
    have hNpos : 0 < a.tangent k := by linarith [h1 k]
    have hH0 : 0 ≤ a.H k := by linarith [(ha.bounds k).2.2.1]
    have hHsq : a.H k ^ 2 ≤ a.tangent k ^ (ε / 3) := by
      calc a.H k ^ 2 ≤ (a.tangent k ^ (ε / 6)) ^ 2 := pow_le_pow_left₀ hH0 hH 2
        _ = a.tangent k ^ (ε / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
            norm_num
            ring_nf
    have hp : 0 ≤ a.tangent k ^ (ε / 3) := Real.rpow_nonneg hNpos.le _
    calc 4 * a.rK k * a.H k ^ 2 ≤
          a.tangent k ^ (ε / 3) * a.tangent k ^ (ε / 3) * a.tangent k ^ (ε / 3) := by
          apply mul_le_mul _ hHsq (by positivity) (by positivity)
          exact mul_le_mul h4' hK (hrKpos k).le hp
      _ = a.tangent k ^ ε := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          ring_nf
  · -- per-stage measure facts and total mass
    refine ⟨(h9 k).1, (h9 k).2.1, fun rg => ?_, ?_⟩
    · obtain ⟨hν, hπ, hae, hle, hsupp⟩ := (h9 k).2.2.1 rg
      refine ⟨hν, hπ, hae.mono fun l hl e => (hl e).trans (hrK_le k), ?_, ?_⟩
      · refine (hρ'le k rg).trans (hle.trans ?_)
        rw [Measure.le_iff']
        intro t
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact hrK_le k
      · exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 (hρ'le k rg) _).trans hsupp.le)
    · exact residual_mass ha Z hZ hZmass k (S k) (hmassS k)
  · -- non-concentration is inherited
    filter_upwards [h10 R hR] with k hk
    intro rg r s b hr1 hr2 hs1 hs2 hb1 hb2
    obtain ⟨hπ', hρ1, hρ2⟩ := hk rg r s b hr1 hr2 hs1 hs2 hb1 hb2
    refine ⟨fun c => (hπ' c).trans ?_, fun q c => ?_, fun q c e => ?_⟩
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _))
    · refine ((Measure.le_iff'.1 (hρ'le k rg) _).trans (hρ1 q c)).trans ?_
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _))
    · refine ((Measure.le_iff'.1 (hρ'le k rg) _).trans (hρ2 q c e)).trans ?_
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _))) _
  · -- planks are the heavy sub-families
    filter_upwards [h11 R hR] with k hk
    intro s hs1 hs2
    obtain ⟨hT1, hT2, hmeas, hdisj, hplank, hcover⟩ := hk s hs1 hs2
    have h2T : (0 : ℝ) < (2 : ℝ) ^ (a.ls k (a.nd k s)).T := by positivity
    have hmem : ∀ i : Fin (fs k s).card,
        (⟨a.nd k s, (fs k s).orderEmbOfFin rfl i⟩ : a.PlankIdx k) ∈ S k := by
      intro i
      exact (Finset.mem_filter.1 ((fs k s).orderEmbOfFin_mem rfl i)).2
    refine ⟨?_, ?_, fun i => hmeas _, ?_, fun i => ?_, fun rg => ?_⟩
    · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (hN0 k) _) (hrKpos k)
        (hrK_le k)).trans hT1
    · exact hT2.trans (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _))
    · intro i i' hne hγ hj
      exact hdisj _ _ (fun h => hne (((fs k s).orderEmbOfFin rfl).injective h)) hγ hj
    · obtain ⟨hνl, hνu, _, huv, hdeg, hF, hfit⟩ := hplank ((fs k s).orderEmbOfFin rfl i)
      refine ⟨?_, ?_, ?_, huv.trans (hrK_le k), hdeg,
        fun t ht w hw => (hF t ht w hw).trans (hrK_le k), fun l hl t ht => ⟨?_, ?_⟩⟩
      · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hνl
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (hN0 k) _)
          (mul_pos (hrKpos k) h2T) (mul_le_mul_of_nonneg_right (hrK_le k) h2T.le)
      · refine hνu.trans (ENNReal.ofReal_le_ofReal ?_)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _)) h2T.le
      · exact hheavy k _ (hmem i)
      · exact (hfit l hl t ht).1.trans (div_le_div_of_nonneg_right (hrK_le k) h2T.le)
      · exact (hfit l hl t ht).2.trans
          (mul_le_mul_of_nonneg_right (hrK_le k) (Real.rpow_nonneg (hN0 k) _))
    · -- coverage: the residual law lives on the support
      have hnull : (((a.ρ k rg).restrict (Z k rg)ᶜ).restrict (a.resSupport k (S k) rg))
          (a.resSupport k (S k) rg)ᶜ = 0 := by
        rw [Measure.restrict_apply (resSupport_measurable ha k (S k) rg).compl,
          Set.compl_inter_self, measure_empty]
      refine measure_mono_null ?_ hnull
      intro z hz hzsupp
      apply hz
      obtain ⟨q, hqS, hq1, hqw, hzq⟩ :=
        (Prune.mem_support _ _ _ _ _ z).1 hzsupp (a.nd k s)
      obtain ⟨ℓ', i'⟩ := q
      simp only at hq1
      subst hq1
      have hi' : i' ∈ (fs k s : Set (Fin (a.ls k (a.nd k s)).n)) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hqS⟩
      rw [← Finset.range_orderEmbOfFin (fs k s) rfl] at hi'
      obtain ⟨i, hi⟩ := hi'
      refine ⟨i, ?_, ?_, ?_⟩
      · rw [hi]; exact hqw
      · rw [hi]; exact hzq.1
      · rw [hi]; exact hzq.2

end Proofs

end

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
