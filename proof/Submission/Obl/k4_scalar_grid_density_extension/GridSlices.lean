import Submission.Obl.k4_scalar_grid_density_extension.Interface
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation

/-!
# Label slices of the scalar observations and comparisons between depths

The pure observation `obs N r` is the base point `(t, y)` together with the
label `⌊x / N ^ (-r)⌋`; the joint observation `aug N r u` adds the label
`⌊l₁ / N ^ (-u)⌋`. A density of the observation is a family of slice densities on
the base. Two depths are compared through the floor-compatibility relation.
The bins at different depths are not nested.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_grid_density_extension

open MeasureTheory Set
open scoped ENNReal

/-- The continuous part `(t, y)` of the observations. -/
abbrev basePoint (p : Incidence) : Base := ![p.2, y p.1 p.2]

/-- The hidden label at depth `r`. -/
abbrev hiddenLabel (N r : ℝ) (p : Incidence) : ℤ := ⌊x p.1 p.2 / N ^ (-r)⌋

/-- The velocity label at depth `u`. -/
abbrev velocityLabel (N u : ℝ) (p : Incidence) : ℤ := ⌊p.1.2 1 / N ^ (-u)⌋

theorem measurable_basePoint : Measurable basePoint := by
  unfold basePoint y
  fun_prop

theorem measurable_hiddenLabel (N r : ℝ) : Measurable (hiddenLabel N r) := by
  unfold hiddenLabel x
  fun_prop

theorem measurable_velocityLabel (N u : ℝ) : Measurable (velocityLabel N u) := by
  unfold velocityLabel
  fun_prop

theorem obs_eq (N r : ℝ) (p : Incidence) : obs N r p = (basePoint p, hiddenLabel N r p) := rfl

theorem measurable_obs_label (N r : ℝ) : Measurable (obs N r) :=
  measurable_basePoint.prodMk (measurable_hiddenLabel N r)

theorem measurable_aug_label (N r u : ℝ) : Measurable (aug N r u) :=
  (measurable_obs_label N r).prodMk (measurable_velocityLabel N u)

theorem aug_eq (N r u : ℝ) (p : Incidence) :
    aug N r u p = ((basePoint p, hiddenLabel N r p), velocityLabel N u p) := rfl

/-- Integrating over a singleton slice of a product with counting measure. -/
theorem setLIntegral_prod_singleton {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L]
    [MeasurableSingletonClass L] [Countable L]
    (ρ : Measure Z) [SFinite ρ] (g : Z × L → ℝ≥0∞) (hg : Measurable g)
    (S : Set Z) (a : L) :
    ∫⁻ q in S ×ˢ {a}, g q ∂(ρ.prod Measure.count) = ∫⁻ x in S, g (x, a) ∂ρ := by
  rw [← Measure.prod_restrict, Measure.restrict_singleton, Measure.count_singleton, one_smul,
    Measure.prod_dirac, lintegral_map hg measurable_prodMk_right]

/-- Slices of a pure observation density. -/
theorem obs_slice (μ : Measure Incidence) (N r : ℝ) (g : ObsSpace → ℝ≥0∞) (hg : Measurable g)
    (hmap : μ.map (obs N r) = reference.withDensity g) (a : ℤ) (S : Set Base)
    (hS : MeasurableSet S) :
    μ {p | hiddenLabel N r p = a ∧ basePoint p ∈ S} = ∫⁻ z in S, g (z, a) := by
  have hT : MeasurableSet (S ×ˢ ({a} : Set ℤ)) := hS.prod (measurableSet_singleton a)
  have hset : {p | hiddenLabel N r p = a ∧ basePoint p ∈ S} = obs N r ⁻¹' (S ×ˢ {a}) := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, obs_eq, mem_prod, mem_singleton_iff]
    exact and_comm
  rw [hset, ← Measure.map_apply (measurable_obs_label N r) hT, hmap, withDensity_apply _ hT]
  exact setLIntegral_prod_singleton _ g hg S a

/-- Slices of a joint observation density. -/
theorem aug_slice (μ : Measure Incidence) (N r u : ℝ) (G : JointSpace → ℝ≥0∞)
    (hG : Measurable G)
    (hmap : μ.map (aug N r u) = jointReference.withDensity G) (a : ℤ × ℤ) (S : Set Base)
    (hS : MeasurableSet S) :
    μ {p | (hiddenLabel N r p, velocityLabel N u p) = a ∧ basePoint p ∈ S} =
      ∫⁻ z in S, G ((z, a.1), a.2) := by
  have hT : MeasurableSet ((S ×ˢ ({a.1} : Set ℤ)) ×ˢ ({a.2} : Set ℤ)) :=
    (hS.prod (measurableSet_singleton _)).prod (measurableSet_singleton _)
  have hset : {p | (hiddenLabel N r p, velocityLabel N u p) = a ∧ basePoint p ∈ S} =
      aug N r u ⁻¹' ((S ×ˢ {a.1}) ×ˢ {a.2}) := by
    ext p
    obtain ⟨a₁, a₂⟩ := a
    simp only [mem_ofPred_eq, mem_preimage, aug_eq, mem_prod, mem_singleton_iff, Prod.mk.injEq]
    tauto
  rw [hset, ← Measure.map_apply (measurable_aug_label N r u) hT, hmap, withDensity_apply _ hT]
  rw [setLIntegral_prod_singleton reference G hG _ a.2]
  exact setLIntegral_prod_singleton _ (fun q => G (q, a.2))
    (hG.comp measurable_prodMk_right) S a.1

theorem width_pos {N : ℝ} (hN : 1 ≤ N) (r : ℝ) : 0 < N ^ (-r) :=
  Real.rpow_pos_of_pos (by linarith) _

theorem width_anti {N r r' : ℝ} (hN : 1 ≤ N) (hrr : r ≤ r') : N ^ (-r') ≤ N ^ (-r) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem width_ratio {N r r' : ℝ} (hN : 1 ≤ N) : N ^ (-r) / N ^ (-r') = N ^ (r' - r) := by
  rw [← Real.rpow_sub (by linarith)]
  congr 1
  ring

theorem hidden_compatible (N r r' : ℝ) (p : Incidence) :
    FloorCompatible (N ^ (-r)) (N ^ (-r')) (hiddenLabel N r p) (hiddenLabel N r' p) :=
  ⟨x p.1 p.2, rfl, rfl⟩

theorem velocity_compatible (N u u' : ℝ) (p : Incidence) :
    FloorCompatible (N ^ (-u)) (N ^ (-u')) (velocityLabel N u p) (velocityLabel N u' p) :=
  ⟨p.1.2 1, rfl, rfl⟩

open Classical in
/-- A fine label is compatible with at most two coarse labels. -/
theorem coarse_count_le {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (b : ℤ) :
    ∑' a, (if FloorCompatible w w' a b then (1 : ℝ≥0∞) else 0) ≤ 2 := by
  refine (tsum_ite_one_le_card _ _ (floorCompatible_coarse_mem hw' hww' b)).trans ?_
  exact_mod_cast Finset.card_le_two

open Classical in
/-- A coarse label is compatible with at most `w / w' + 2` fine labels. -/
theorem fine_count_le {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (a : ℤ) :
    ∑' b, (if FloorCompatible w w' a b then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (w / w' + 2) := by
  refine (tsum_ite_one_le_card _ _ (floorCompatible_fine_mem hw' hww' a)).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (card_fine_window_le hw' hww' a)

open Classical in
theorem pair_coarse_count_le {w w' v v' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w)
    (hv' : 0 < v') (hvv' : v' ≤ v) (b : ℤ × ℤ) :
    ∑' a, (if PairCompatible w w' v v' a b then (1 : ℝ≥0∞) else 0) ≤ 4 := by
  let F := ({⌊(b.1 : ℝ) * w' / w⌋, ⌊(b.1 : ℝ) * w' / w⌋ + 1} : Finset ℤ) ×ˢ
    ({⌊(b.2 : ℝ) * v' / v⌋, ⌊(b.2 : ℝ) * v' / v⌋ + 1} : Finset ℤ)
  refine (tsum_ite_one_le_card _ F ?_).trans ?_
  · intro a ha
    exact Finset.mem_product.mpr ⟨floorCompatible_coarse_mem hw' hww' b.1 a.1 ha.1,
      floorCompatible_coarse_mem hv' hvv' b.2 a.2 ha.2⟩
  · have h1 : ({⌊(b.1 : ℝ) * w' / w⌋, ⌊(b.1 : ℝ) * w' / w⌋ + 1} : Finset ℤ).card ≤ 2 :=
      Finset.card_le_two
    have h2 : ({⌊(b.2 : ℝ) * v' / v⌋, ⌊(b.2 : ℝ) * v' / v⌋ + 1} : Finset ℤ).card ≤ 2 :=
      Finset.card_le_two
    have : F.card ≤ 4 := by
      rw [Finset.card_product]
      calc _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
        _ = 4 := by norm_num
    exact_mod_cast this

open Classical in
theorem pair_fine_count_le {w w' v v' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w)
    (hv' : 0 < v') (hvv' : v' ≤ v) (a : ℤ × ℤ) :
    ∑' b, (if PairCompatible w w' v v' a b then (1 : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal ((w / w' + 2) * (v / v' + 2)) := by
  let F := Finset.Icc ⌊(a.1 : ℝ) * w / w'⌋ ⌊((a.1 : ℝ) + 1) * w / w'⌋ ×ˢ
    Finset.Icc ⌊(a.2 : ℝ) * v / v'⌋ ⌊((a.2 : ℝ) + 1) * v / v'⌋
  refine (tsum_ite_one_le_card _ F ?_).trans ?_
  · intro b hb
    exact Finset.mem_product.mpr ⟨floorCompatible_fine_mem hw' hww' a.1 b.1 hb.1,
      floorCompatible_fine_mem hv' hvv' a.2 b.2 hb.2⟩
  · rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.card_product]
    push_cast
    exact mul_le_mul (card_fine_window_le hw' hww' a.1) (card_fine_window_le hv' hvv' a.2)
      (by positivity) (by linarith [div_pos (hw'.trans_le hww') hw'])

/-- Pure observations: a coarser density falls below `ε` times a finer one only on
mass at most `2 ε`. -/
theorem pure_coarse_low_mass (μ : Measure Incidence) {N r r' : ℝ} (hN : 1 ≤ N)
    (hrr : r ≤ r') (g g' : ObsSpace → ℝ≥0∞) (hg : Measurable g) (hg' : Measurable g')
    (hmap : μ.map (obs N r) = reference.withDensity g)
    (hmap' : μ.map (obs N r') = reference.withDensity g') (ε : ℝ≥0∞) :
    μ {p | g (obs N r p) < ε * g' (obs N r' p)} ≤ ε * 2 * μ univ := by
  classical
  exact relation_low_density_mass μ volume basePoint (hiddenLabel N r) (hiddenLabel N r')
    (fun b => measurableSet_eq_fun (measurable_hiddenLabel N r') measurable_const)
    (fun z a => g (z, a)) (fun z b => g' (z, b))
    (fun a => hg.comp measurable_prodMk_right)
    (fun b => hg'.comp measurable_prodMk_right)
    (fun a S hS => obs_slice μ N r g hg hmap a S hS)
    (fun b S hS => obs_slice μ N r' g' hg' hmap' b S hS)
    (FloorCompatible (N ^ (-r)) (N ^ (-r')))
    (Filter.Eventually.of_forall (hidden_compatible N r r')) 2
    (coarse_count_le (width_pos hN r') (width_anti hN hrr)) ε

/-- Pure observations: a finer density falls below `ε` times a coarser one only on
mass at most `ε (N ^ (r' - r) + 2)`. -/
theorem pure_fine_low_mass (μ : Measure Incidence) {N r r' : ℝ} (hN : 1 ≤ N)
    (hrr : r ≤ r') (g g' : ObsSpace → ℝ≥0∞) (hg : Measurable g) (hg' : Measurable g')
    (hmap : μ.map (obs N r) = reference.withDensity g)
    (hmap' : μ.map (obs N r') = reference.withDensity g') (ε : ℝ≥0∞) :
    μ {p | g' (obs N r' p) < ε * g (obs N r p)} ≤
      ε * ENNReal.ofReal (N ^ (r' - r) + 2) * μ univ := by
  classical
  have h := relation_low_density_mass μ volume basePoint (hiddenLabel N r') (hiddenLabel N r)
    (fun b => measurableSet_eq_fun (measurable_hiddenLabel N r) measurable_const)
    (fun z a => g' (z, a)) (fun z b => g (z, b))
    (fun a => hg'.comp measurable_prodMk_right)
    (fun b => hg.comp measurable_prodMk_right)
    (fun a S hS => obs_slice μ N r' g' hg' hmap' a S hS)
    (fun b S hS => obs_slice μ N r g hg hmap b S hS)
    (fun a b => FloorCompatible (N ^ (-r)) (N ^ (-r')) b a)
    (Filter.Eventually.of_forall (fun p => hidden_compatible N r r' p))
    (ENNReal.ofReal (N ^ (r' - r) + 2))
    (fun b => by
      have := fine_count_le (width_pos hN r') (width_anti hN hrr) b
      rwa [width_ratio hN] at this) ε
  exact h

/-- Joint observations: a coarser density falls below `ε` times a finer one only on
mass at most `4 ε`. -/
theorem joint_coarse_low_mass (μ : Measure Incidence) {N r r' u u' : ℝ} (hN : 1 ≤ N)
    (hrr : r ≤ r') (huu : u ≤ u') (G G' : JointSpace → ℝ≥0∞)
    (hG : Measurable G) (hG' : Measurable G')
    (hmap : μ.map (aug N r u) = jointReference.withDensity G)
    (hmap' : μ.map (aug N r' u') = jointReference.withDensity G') (ε : ℝ≥0∞) :
    μ {p | G (aug N r u p) < ε * G' (aug N r' u' p)} ≤ ε * 4 * μ univ := by
  classical
  have h := relation_low_density_mass μ volume basePoint
    (fun p => (hiddenLabel N r p, velocityLabel N u p))
    (fun p => (hiddenLabel N r' p, velocityLabel N u' p))
    (fun b => measurableSet_eq_fun
      ((measurable_hiddenLabel N r').prodMk (measurable_velocityLabel N u')) measurable_const)
    (fun z a => G ((z, a.1), a.2)) (fun z b => G' ((z, b.1), b.2))
    (fun a => hG.comp (measurable_prodMk_right.prodMk measurable_const))
    (fun b => hG'.comp (measurable_prodMk_right.prodMk measurable_const))
    (fun a S hS => aug_slice μ N r u G hG hmap a S hS)
    (fun b S hS => aug_slice μ N r' u' G' hG' hmap' b S hS)
    (PairCompatible (N ^ (-r)) (N ^ (-r')) (N ^ (-u)) (N ^ (-u')))
    (Filter.Eventually.of_forall (fun p => ⟨hidden_compatible N r r' p,
      velocity_compatible N u u' p⟩)) 4
    (pair_coarse_count_le (width_pos hN r') (width_anti hN hrr) (width_pos hN u')
      (width_anti hN huu)) ε
  simpa only [aug_eq] using h

/-- Joint observations: a finer density falls below `ε` times a coarser one only on
mass at most `ε (N ^ (r' - r) + 2) (N ^ (u' - u) + 2)`. -/
theorem joint_fine_low_mass (μ : Measure Incidence) {N r r' u u' : ℝ} (hN : 1 ≤ N)
    (hrr : r ≤ r') (huu : u ≤ u') (G G' : JointSpace → ℝ≥0∞)
    (hG : Measurable G) (hG' : Measurable G')
    (hmap : μ.map (aug N r u) = jointReference.withDensity G)
    (hmap' : μ.map (aug N r' u') = jointReference.withDensity G') (ε : ℝ≥0∞) :
    μ {p | G' (aug N r' u' p) < ε * G (aug N r u p)} ≤
      ε * ENNReal.ofReal ((N ^ (r' - r) + 2) * (N ^ (u' - u) + 2)) * μ univ := by
  classical
  have h := relation_low_density_mass μ volume basePoint
    (fun p => (hiddenLabel N r' p, velocityLabel N u' p))
    (fun p => (hiddenLabel N r p, velocityLabel N u p))
    (fun b => measurableSet_eq_fun
      ((measurable_hiddenLabel N r).prodMk (measurable_velocityLabel N u)) measurable_const)
    (fun z a => G' ((z, a.1), a.2)) (fun z b => G ((z, b.1), b.2))
    (fun a => hG'.comp (measurable_prodMk_right.prodMk measurable_const))
    (fun b => hG.comp (measurable_prodMk_right.prodMk measurable_const))
    (fun a S hS => aug_slice μ N r' u' G' hG' hmap' a S hS)
    (fun b S hS => aug_slice μ N r u G hG hmap b S hS)
    (fun a b => PairCompatible (N ^ (-r)) (N ^ (-r')) (N ^ (-u)) (N ^ (-u')) b a)
    (Filter.Eventually.of_forall (fun p => ⟨hidden_compatible N r r' p,
      velocity_compatible N u u' p⟩))
    (ENNReal.ofReal ((N ^ (r' - r) + 2) * (N ^ (u' - u) + 2)))
    (fun b => by
      have := pair_fine_count_le (width_pos hN r') (width_anti hN hrr) (width_pos hN u')
        (width_anti hN huu) b
      rwa [width_ratio hN, width_ratio hN] at this) ε
  simpa only [aug_eq] using h

end Submission.Obl.k4_scalar_grid_density_extension
