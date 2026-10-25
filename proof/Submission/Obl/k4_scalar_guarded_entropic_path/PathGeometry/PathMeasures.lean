/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathMeasures.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementWitness
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic

/-! Common original-world incidence laws behind actual scalar atlas
normalizations. The original-world weights cancel only against the full
assigned-prior normalization; the selected masks remain restrictions of the
original incidence laws. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

abbrev State := (ℕ × ScalarCoeff) × ℝ

def worldMixture (p : Code) (k : ℕ) : Measure (Fin (W p k) × State) :=
  ∑ g, ENNReal.ofReal (ω p k g) • (mu p k g).map (fun z => (g, z))

variable {p q : Code} {r b h : ℝ}

def normalizer (w : RefinementWitness p q r b h) (k : ℕ) : ℝ :=
  ∑ i, ω p (w.sample k) (w.world k i) * w.toRefinementData.duration k *
    (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal

theorem normalizer_pos (w : RefinementWitness p q r b h) (k : ℕ) :
    0 < normalizer w k := (w.weights k).1

def originalSelected (w : RefinementWitness p q r b h) (k : ℕ) :
    Measure (Fin (W p (w.sample k)) × State) :=
  ∑ i, ENNReal.ofReal (ω p (w.sample k) (w.world k i)) •
    (((mu p (w.sample k) (w.world k i)).restrict (w.selected k i)).map
      (fun z => (w.world k i, z)))

def liftedMixture (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    Measure (Fin (W p (w.sample k)) × State) :=
  ∑ i, ENNReal.ofReal (ω q k i) •
    ((mu q k i).map (fun z => (w.world k i, (w.incidenceEquiv hp k i).symm z)))

/-- Recover the parent world and its original coordinates from a child world. -/
def pullbackMap (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    Fin (W q k) × State → Fin (W p (w.sample k)) × State :=
  fun z => (w.world k z.1, (w.incidenceEquiv hp k z.1).symm z.2)

theorem measurable_pullbackMap (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    Measurable (pullbackMap w hp k) := by
  apply measurable_from_prod_countable_right
  intro i
  change Measurable (fun z : State => (w.world k i, (w.incidenceEquiv hp k i).symm z))
  exact measurable_const.prodMk (w.incidenceEquiv hp k i).symm.measurable

theorem map_worldMixture_pullback (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    (worldMixture q k).map (pullbackMap w hp k) = liftedMixture w hp k := by
  unfold worldMixture liftedMixture
  rw [Measure.map_finset_sum' (measurable_pullbackMap w hp k).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_smul _ (measurable_pullbackMap w hp k).aemeasurable,
    Measure.map_map (measurable_pullbackMap w hp k)
      (show Measurable (fun z : State => (i, z)) from measurable_const.prodMk measurable_id)]
  rfl

theorem ofReal_weight_cancel (w₀ dt Z : ℝ) (a : ℝ≥0∞)
    (hw : 0 ≤ w₀) (hdt : 0 < dt) (hZ : 0 < Z) (ha₀ : a ≠ 0) (hatop : a ≠ ∞) :
    ENNReal.ofReal (w₀ * dt * a.toReal / Z) * (ENNReal.ofReal dt * a)⁻¹ =
      ENNReal.ofReal w₀ / ENNReal.ofReal Z := by
  have hdt₀ : ENNReal.ofReal dt ≠ 0 := (ENNReal.ofReal_pos.mpr hdt).ne'
  have hprod₀ : ENNReal.ofReal dt * a ≠ 0 := mul_ne_zero hdt₀ ha₀
  have hprodtop : ENNReal.ofReal dt * a ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hatop
  rw [ENNReal.ofReal_div_of_pos hZ,
    ENNReal.ofReal_mul (mul_nonneg hw hdt.le), ENNReal.ofReal_mul hw,
    ENNReal.ofReal_toReal hatop]
  calc
    _ = (ENNReal.ofReal w₀ / ENNReal.ofReal Z) *
        ((ENNReal.ofReal dt * a) * (ENNReal.ofReal dt * a)⁻¹) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hprod₀ hprodtop, mul_one]

/-- Undoing a child coordinate change cancels its entire within-world
normalization. The remaining factor is the original world weight divided by
the atlas's common normalizer. -/
theorem weighted_pullback_eq (w : RefinementWitness p q r b h) (hp : Exact p)
    (k : ℕ) (i : Fin (W q k)) :
    ENNReal.ofReal (ω q k i) •
        (mu q k i).map (fun z => (w.world k i, (w.incidenceEquiv hp k i).symm z)) =
      (ENNReal.ofReal (normalizer w k))⁻¹ •
        (ENNReal.ofReal (ω p (w.sample k) (w.world k i)) •
          ((mu p (w.sample k) (w.world k i)).restrict (w.selected k i)).map
            (fun z => (w.world k i, z))) := by
  have hmap : Measurable (fun z : State =>
      (w.world k i, (w.incidenceEquiv hp k i).symm z)) :=
    measurable_const.prodMk (w.incidenceEquiv hp k i).symm.measurable
  rw [w.incidence_eq hp k i, Measure.map_smul _ hmap.aemeasurable,
    Measure.map_map hmap (w.incidenceEquiv hp k i).measurable, smul_smul]
  have heq : (fun z : State => (w.world k i, (w.incidenceEquiv hp k i).symm z)) ∘
      (w.incidenceEquiv hp k i) = (fun z : State => (w.world k i, z)) := by
    funext z
    simp
  rw [heq, (w.weights k).2 i]
  change (ENNReal.ofReal (ω p (w.sample k) (w.world k i) * w.toRefinementData.duration k *
      (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal / normalizer w k) *
      (ENNReal.ofReal (w.toRefinementData.duration k) *
        ν p (w.sample k) (w.world k i) (w.assignment k i))⁻¹) • _ = _
  rw [ofReal_weight_cancel _ _ _ _ ((hp.2.1 (w.sample k)).2.1 (w.world k i))
    (w.duration_pos k) (normalizer_pos w k) (w.assignment_mass_pos k i).ne'
    (w.assignment_mass_ne_top hp k i), div_eq_mul_inv, smul_smul,
    mul_comm (ENNReal.ofReal (ω p (w.sample k) (w.world k i)))]

/-- The entire normalized child mixture, put in original coordinates, is
one rescaling of a common original-world retained path law. -/
theorem liftedMixture_eq (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    liftedMixture w hp k = (ENNReal.ofReal (normalizer w k))⁻¹ • originalSelected w k := by
  unfold liftedMixture originalSelected
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => weighted_pullback_eq w hp k i

/-- Every original world's selected chart pieces are almost everywhere
disjoint. Closed dyadic block boundaries are handled by the accepted atlas
intersection-null theorem. -/
theorem selected_restrictions_le (w : RefinementWitness p q r b h) (hp : Exact p)
    (k : ℕ) (g : Fin (W p (w.sample k))) :
    (∑ i ∈ Finset.univ.filter (fun i => w.world k i = g),
      (mu p (w.sample k) g).restrict (w.selected k i)) ≤ mu p (w.sample k) g := by
  classical
  let F := Finset.univ.filter (fun i => w.world k i = g)
  have hnull :=
    Submission.Obl.k4_scalar_true_atlas_terminal_lists.assigned_incidence_inter_null
      (p := p) hp (w.world k) (w.block k) (w.assignment k) (w.selected k)
      (w.charts k).2.2.2.2.1
      (fun i z hz => ((w.charts k).2.2.2.2.2.1 i hz).2)
  have hpair : Pairwise (fun i i' : F =>
      AEDisjoint (mu p (w.sample k) g) (w.selected k i.1) (w.selected k i'.1)) := by
    intro i i' hne
    have h₁ := (Finset.mem_filter.mp i.2).2
    have h₂ := (Finset.mem_filter.mp i'.2).2
    change mu p (w.sample k) g (w.selected k i.1 ∩ w.selected k i'.1) = 0
    simpa only [h₁, Submission.Obl.k4_scalar_true_atlas_terminal_lists.mu, mu,
      Submission.Obl.k4_scalar_true_atlas_terminal_lists.prior,
      Submission.Obl.k4_scalar_true_atlas_terminal_lists.event, ν, E] using
      hnull i.1 i'.1 (Subtype.coe_ne_coe.mpr hne) (h₁.trans h₂.symm)
  have hmeas (i : F) : NullMeasurableSet (w.selected k i.1) (mu p (w.sample k) g) :=
    ((w.charts k).2.2.2.1 i.1).2.nullMeasurableSet
  change (∑ i ∈ F, (mu p (w.sample k) g).restrict (w.selected k i)) ≤ _
  rw [← Finset.sum_attach]
  simp only [Finset.attach_eq_univ]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion_ae hpair hmeas]
  exact Measure.restrict_le_self

/-- The retained path is a submeasure of the original world mixture. In
particular later incidence omissions need no change of original priors. -/
theorem originalSelected_le (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    originalSelected w k ≤ worldMixture p (w.sample k) := by
  classical
  unfold originalSelected worldMixture
  calc
    _ = ∑ g, ∑ i ∈ Finset.univ.filter (fun i => w.world k i = g),
        ENNReal.ofReal (ω p (w.sample k) (w.world k i)) •
          (((mu p (w.sample k) (w.world k i)).restrict (w.selected k i)).map
            (fun z => (w.world k i, z))) :=
      (Finset.sum_fiberwise Finset.univ (w.world k) _).symm
    _ = ∑ g, ENNReal.ofReal (ω p (w.sample k) g) •
        Measure.map (fun z : State => (g, z))
          (∑ i ∈ Finset.univ.filter (fun i => w.world k i = g),
            (mu p (w.sample k) g).restrict (w.selected k i)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Measure.map_finset_sum
          (show Measurable (fun z : State => (g, z)) from
            measurable_const.prodMk measurable_id).aemeasurable,
        Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro g _
      apply Measure.le_iff.mpr
      intro S _hS
      exact mul_le_mul' le_rfl
        ((Measure.map_mono (selected_restrictions_le w hp k g)
          (measurable_const.prodMk measurable_id)) S)

/-- Multiplying by the genuine original assignment budget makes the pulled
back normalized mixture an original-law submeasure. -/
theorem unnormalized_pullback_eq (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    ENNReal.ofReal (normalizer w k) •
        (worldMixture q k).map (pullbackMap w hp k) = originalSelected w k := by
  rw [map_worldMixture_pullback, liftedMixture_eq, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (normalizer_pos w k)).ne'
      ENNReal.ofReal_ne_top, one_smul]

/-- The original-law domination survives every later sparse submeasure of
the normalized mixture. All reference weights and full priors stay fixed. -/
theorem submeasure_pullback_le (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ)
    (ρ : Measure (Fin (W q k) × State)) (hρ : ρ ≤ worldMixture q k) :
    ENNReal.ofReal (normalizer w k) • ρ.map (pullbackMap w hp k) ≤
      worldMixture p (w.sample k) := by
  calc
    _ ≤ ENNReal.ofReal (normalizer w k) •
        (worldMixture q k).map (pullbackMap w hp k) := by
      apply Measure.le_iff.mpr
      intro S _hS
      exact mul_le_mul' le_rfl
        ((Measure.map_mono hρ (measurable_pullbackMap w hp k)) S)
    _ = originalSelected w k := unnormalized_pullback_eq w hp k
    _ ≤ _ := originalSelected_le w hp k

/-- Two successive actual refinements realize a common original path law,
even after arbitrary final sparse restriction. Their actual assignment
budgets multiply before the incidence law is compared with the original. -/
theorem two_layer_submeasure_pullback_le {p q z : Code} {r₁ b₁ h₁ r₂ b₂ h₂ : ℝ}
    (w₁ : RefinementWitness p q r₁ b₁ h₁) (w₂ : RefinementWitness q z r₂ b₂ h₂)
    (hp : Exact p) (hq : Exact q) (k : ℕ)
    (ρ : Measure (Fin (W z k) × State)) (hρ : ρ ≤ worldMixture z k) :
    ENNReal.ofReal (normalizer w₁ (w₂.sample k) * normalizer w₂ k) •
        ρ.map ((pullbackMap w₁ hp (w₂.sample k)) ∘ (pullbackMap w₂ hq k)) ≤
      worldMixture p (w₁.sample (w₂.sample k)) := by
  have h₂ := submeasure_pullback_le w₂ hq k ρ hρ
  have h₁ := submeasure_pullback_le w₁ hp (w₂.sample k) _ h₂
  rw [Measure.map_smul _ (measurable_pullbackMap w₁ hp (w₂.sample k)).aemeasurable,
    Measure.map_map (measurable_pullbackMap w₁ hp (w₂.sample k))
      (measurable_pullbackMap w₂ hq k), smul_smul,
    ← ENNReal.ofReal_mul (normalizer_pos w₁ (w₂.sample k)).le] at h₁
  exact h₁

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
