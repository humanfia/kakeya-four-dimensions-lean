import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootReadouts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewAt

/-! Velocity changes on the literal path are affine. The slope of an
actual prefix is exactly its original dyadic duration divided by width. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace RefinementWitness

theorem velocity_pullback {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ)
    (u : Fin (W q k) × State) :
    u.2.1.2 1 = w.toRefinementData.duration k *
      ((pullbackMap w hp k u).2.1.2 1 - w.speed k u.1) / w.width k u.1 := by
  have heq := congrArg (fun x : State => x.1.2 1)
    ((w.incidenceEquiv hp k u.1).apply_symm_apply u.2)
  exact heq.symm

theorem velocity_difference_pullback {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ)
    (u v : Fin (W q k) × State) (hworld : u.1 = v.1) :
    u.2.1.2 1 - v.2.1.2 1 =
      (w.toRefinementData.duration k / w.width k u.1) *
        ((pullbackMap w hp k u).2.1.2 1 - (pullbackMap w hp k v).2.1.2 1) := by
  have hu := w.velocity_pullback hp k u
  have hv := w.velocity_pullback hp k v
  rw [← hworld] at hv
  rw [hu, hv]
  ring

end RefinementWitness

namespace PathNodes.TrueGridPath

def velocityAt {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → (k n : ℕ) →
      Fin (W (path.forget.finalFamily.problem i) k) × State → ℝ :=
  match path with
  | .nil _ _ => fun _ _ _ z => z.2.1.2 1
  | .cons r rs hs hr node tail => fun certs k n z =>
      match n with
      | 0 => (((TrueGridPath.cons r rs hs hr node tail).measuredChain i certs).pullback k z).2.1.2 1
      | n + 1 => tail.velocityAt i certs.2 k n z

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem velocityAt_zero (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State) :
    path.velocityAt i certs k 0 z = ((path.measuredChain i certs).pullback k z).2.1.2 1 := by
  cases path <;> rfl

theorem viewAt_velocity {root : Code} (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : TrueLiftChains.Chain root (source.problem i)) (k n : ℕ)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State) :
    ((path.viewAt i certs hl before n).suffixChain.pullback k z).2.1.2 1 =
      path.velocityAt i certs k n z := by
  induction path generalizing n with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih certs.2 hl.2 _ n z

theorem root_geometry_width_pos (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (d : Fin (path.rootGeometry i certs k j).count) :
    0 < (path.rootGeometry i certs k j).width d := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    revert d
    refine Fin.cases ?_ (fun j => ?_) j
    · intro d; exact certs.1.witness.width_pos _ d
    · intro d; exact mul_pos (certs.1.witness.width_pos _ _) (ih certs.2 j d)

/-- Same endpoint worlds have the same entire affine velocity change.
The ratio is the ACTUAL original root-row ratio, so a single full-width
bound controls every intermediate velocity decoder. -/
theorem root_velocity_difference (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (z z' : Fin (W (path.forget.finalFamily.problem i) k) × State)
    (hrow : path.rootRow i certs k j z.1 = path.rootRow i certs k j z'.1) :
    path.velocityAt i certs k (j.val + 1) z - path.velocityAt i certs k (j.val + 1) z' =
      (((2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ /
        (path.rootGeometry i certs k j).width (path.rootRow i certs k j z.1)) *
      (path.velocityAt i certs k 0 z - path.velocityAt i certs k 0 z') := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    revert hrow
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hrow
      change (tail.measuredChain i certs.2).world k z.1 =
        (tail.measuredChain i certs.2).world k z'.1 at hrow
      have hworld : ((tail.measuredChain i certs.2).pullback k z).1 =
          ((tail.measuredChain i certs.2).pullback k z').1 := by
        simpa only [RefinementChain.pullback_world] using hrow
      have hd := certs.1.witness.velocity_difference_pullback certs.1.parent_exact _ _ _ hworld
      change tail.velocityAt i certs.2 k 0 z - tail.velocityAt i certs.2 k 0 z' =
        (certs.1.witness.toRefinementData.duration ((tail.measuredChain i certs.2).sample k) /
          certs.1.witness.width ((tail.measuredChain i certs.2).sample k)
            ((tail.measuredChain i certs.2).world k z.1)) * _
      rw [tail.velocityAt_zero, tail.velocityAt_zero]
      simpa only [RefinementChain.pullback_world, velocityAt, measuredChain,
        forget, toLayerWitnesses, GridPath.toMeasuredChain,
        RefinementChain.pullback, Function.comp_apply] using hd
    · intro hrow
      change tail.rootRow i certs.2 k j z.1 = tail.rootRow i certs.2 k j z'.1 at hrow
      have hworld : ((tail.measuredChain i certs.2).pullback k z).1 =
          ((tail.measuredChain i certs.2).pullback k z').1 := by
        rw [RefinementChain.pullback_world, RefinementChain.pullback_world]
        rw [← tail.rootRow_world i certs.2 k j z.1,
          ← tail.rootRow_world i certs.2 k j z'.1, hrow]
      have hfirst := certs.1.witness.velocity_difference_pullback certs.1.parent_exact
        ((tail.measuredChain i certs.2).sample k) _ _ hworld
      have htail := ih certs.2 j z z' hrow
      change tail.velocityAt i certs.2 k (j.val + 1) z -
          tail.velocityAt i certs.2 k (j.val + 1) z' = _
      rw [htail, tail.velocityAt_zero, tail.velocityAt_zero, hfirst]
      change _ = (((2 : ℝ) ^ (certs.1.witness.T ((tail.measuredChain i certs.2).sample k) +
          (tail.rootGeometry i certs.2 k j).generation))⁻¹ /
          (certs.1.witness.width ((tail.measuredChain i certs.2).sample k)
            ((tail.rootGeometry i certs.2 k j).world (tail.rootRow i certs.2 k j z.1)) *
            (tail.rootGeometry i certs.2 k j).width (tail.rootRow i certs.2 k j z.1))) * _
      rw [tail.rootRow_world i certs.2 k j z.1, pow_add, mul_inv]
      rw [RefinementChain.pullback_world]
      change _ = _ *
        ((((TrueGridPath.cons r rs hstart hr node tail).measuredChain i certs).pullback k z).2.1.2 1 -
          (((TrueGridPath.cons r rs hstart hr node tail).measuredChain i certs).pullback k z').2.1.2 1)
      dsimp only [RefinementData.duration, measuredChain, forget, toLayerWitnesses,
        GridPath.toMeasuredChain, RefinementChain.pullback, Function.comp_apply]
      ring

theorem rootRow_eq_of_viewAt_world_eq {root : Code}
    (path : TrueGridPath ctx source start targets) (i : ℕ) (certs : path.Certificates i)
    (hl : path.forget.AllLayers i) (before : TrueLiftChains.Chain root (source.problem i))
    (k : ℕ) (j : Fin targets.length)
    (g g' : Fin (W (path.forget.finalFamily.problem i) k))
    (hworld : (path.viewAt i certs hl before (j.val + 1)).suffixChain.world k g =
      (path.viewAt i certs hl before (j.val + 1)).suffixChain.world k g') :
    path.rootRow i certs k j g = path.rootRow i certs k j g' := by
  apply Fin.ext
  rw [path.rootRow_history i certs k j g, path.rootRow_history i certs k j g']
  have hv := congrArg Fin.val hworld
  simpa only [path.viewAt_history i certs hl before (j.val + 1) k] using hv

/-- One original full-row width bound controls the affine slope of
the actual normalized velocity at that prefix. -/
theorem root_velocity_lipschitz (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (z z' : Fin (W (path.forget.finalFamily.problem i) k) × State)
    (hrow : path.rootRow i certs k j z.1 = path.rootRow i certs k j z'.1)
    {H : ℝ} (hH : 0 < H)
    (hwidth : (H * (2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ ≤
      (path.rootGeometry i certs k j).width (path.rootRow i certs k j z.1)) :
    |path.velocityAt i certs k (j.val + 1) z - path.velocityAt i certs k (j.val + 1) z'| ≤
      H * |path.velocityAt i certs k 0 z - path.velocityAt i certs k 0 z'| := by
  have hq : 0 < (2 : ℝ) ^ (path.rootGeometry i certs k j).generation := by positivity
  have hJ := path.root_geometry_width_pos i certs k j (path.rootRow i certs k j z.1)
  have hprod := (inv_le_iff_one_le_mul₀ (mul_pos hH hq)).mp hwidth
  have hratio : ((2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ /
      (path.rootGeometry i certs k j).width (path.rootRow i certs k j z.1) ≤ H := by
    apply (div_le_iff₀ hJ).mpr
    apply (inv_le_iff_one_le_mul₀ hq).mpr
    nlinarith only [hprod]
  rw [path.root_velocity_difference i certs k j z z' hrow, abs_mul,
    abs_of_nonneg (div_nonneg (inv_nonneg.mpr hq.le) hJ.le)]
  exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
