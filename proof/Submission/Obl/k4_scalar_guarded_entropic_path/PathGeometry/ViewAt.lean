import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathHistories
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SuffixReferences

/-! Numbered genuine parent views, extended constantly at the final
leaf. Their maps supply the measured information-window interface. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

namespace TrueLiftChains.Chain

theorem append_length {p q z : Code} (before : Chain p q) (after : Chain q z) :
    (before.append after).length = before.length + after.length := by
  induction before with
  | nil => simp [append, length]
  | cons a hL hr hh hrel tail ih =>
    simp only [append, length, ih]
    omega

end TrueLiftChains.Chain

namespace PathNodes.TrueGridPath

/-- The same finite family as `originalViews`, numbered from zero and
extended constantly at its last genuine exact parent. -/
def viewAt {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} {root : Code}
    (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → (hl : path.forget.AllLayers i) →
    Chain root (source.problem i) → ℕ →
      OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η :=
  match path with
  | .nil _ _ => fun certs hl before _ => originalView (.nil _ _) i certs hl before
  | .cons r rs hstart hr node tail => fun certs hl before n =>
      match n with
      | 0 => originalView (.cons r rs hstart hr node tail) i certs hl before
      | n + 1 => tail.viewAt i certs.2 hl.2
          (before.append (.cons certs.1 hl.1.remaining_length hl.1.depth_nonneg hl.1.known.1
            (fun s hs hsL => hl.1.remaining_profile s ⟨hs, hsL⟩)
            (.nil _ (tail.trueChain i certs.2 hl.2).source_exact))) n

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ} {root : Code}

theorem viewAt_min (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    path.viewAt i certs hl before n = path.viewAt i certs hl before (min n targets.length) := by
  induction path generalizing n with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have heq : min (n + 1) (rs.length + 1) = min n rs.length + 1 := by omega
      simp only [List.length_cons, heq]
      exact ih certs.2 hl.2 _ n

theorem viewAt_count (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    (path.viewAt i certs hl before n).count = targets.length - n := by
  induction path generalizing n with
  | nil => simp [viewAt, originalView]
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (tail.viewAt i certs.2 hl.2 _ n).count = _
      simpa only [List.length_cons, Nat.add_sub_add_right] using ih certs.2 hl.2 _ n

theorem viewAt_prefix_length (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    (path.viewAt i certs hl before n).prefixChain.length = before.length + min n targets.length := by
  induction path generalizing n with
  | nil => simp [viewAt, originalView]
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (tail.viewAt i certs.2 hl.2 _ n).prefixChain.length = _
      rw [ih, Chain.append_length]
      simp only [Chain.length]
      simp only [List.length_cons]
      omega

theorem viewAt_mem_originalViews (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    path.viewAt i certs hl before n ∈ path.originalViews i certs hl before := by
  induction path generalizing n with
  | nil => exact List.mem_singleton_self _
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => exact List.mem_cons_self
    | succ n => exact List.mem_cons_of_mem _ (ih certs.2 hl.2 _ n)

/-- Every possible window retains at least the length of the common
final exact problem. -/
theorem viewAt_final_length_le (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    L (path.forget.finalFamily.problem i) ≤ L (path.viewAt i certs hl before n).parent := by
  induction path generalizing n with
  | nil => exact le_rfl
  | @cons source start r rs hstart hr node tail ih =>
    cases n with
    | zero =>
      change L ((TrueGridPath.cons r rs hstart hr node tail).forget.finalFamily.problem i) ≤
        L (source.problem i)
      have hlen := ((TrueGridPath.cons r rs hstart hr node tail).trueChain i certs hl).remaining_length
      have hnonneg := ((TrueGridPath.cons r rs hstart hr node tail).trueChain i certs hl).depth_nonneg
      linarith
    | succ n => exact ih certs.2 hl.2 _ n

/-- One original root reference factor pays for every actual suffix
view, uniformly before the entropy window is selected. -/
theorem viewAt_referenceFactor_le (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k : ℕ) :
    (path.viewAt i certs hl before n).suffixChain.referenceFactor k ≤
      (path.measuredChain i certs).referenceFactor k := by
  induction path generalizing n with
  | nil => exact le_rfl
  | @cons source start r rs hstart hr node tail ih =>
    cases n with
    | zero => exact le_rfl
    | succ n =>
      change (tail.viewAt i certs.2 hl.2 _ n).suffixChain.referenceFactor k ≤ _
      exact (ih certs.2 hl.2 _ n).trans
        (RefinementChain.referenceFactor_tail_le certs.1.witness (source.angular i).1
          (tail.measuredChain i certs.2) (tail.forget.finalFamily.angular i).1 k)

/-- Every numbered view still uses the identical actual original source
sample of the full chosen true path. -/
theorem viewAt_rootSample (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k : ℕ) :
    (path.viewAt i certs hl before n).rootSample k =
      before.sample ((path.measuredChain i certs).sample k) :=
  path.originalViews_rootSample i certs hl before k _
    (path.viewAt_mem_originalViews i certs hl before n)

/-- The actual suffix world map is the nested finite history, including
the constant extension past the leaf. -/
theorem viewAt_history (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k : ℕ)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    ((path.viewAt i certs hl before n).suffixChain.world k g).val =
      (path.measuredChain i certs).history k n g := by
  induction path generalizing n with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => exact (RefinementChain.history_zero _ _ _).symm
    | succ n => exact ih certs.2 hl.2 _ n g

/-- The original world labels needed by `exists_window_info` are nested
pointwise, before choosing a residual or its finite atomization. -/
theorem viewAt_world_nested (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k : ℕ)
    (g g' : Fin (W (path.forget.finalFamily.problem i) k))
    (h : (path.viewAt i certs hl before (n + 1)).suffixChain.world k g =
      (path.viewAt i certs hl before (n + 1)).suffixChain.world k g') :
    (path.viewAt i certs hl before n).suffixChain.world k g =
      (path.viewAt i certs hl before n).suffixChain.world k g' := by
  apply Fin.ext
  have hn : (path.measuredChain i certs).history k (n + 1) g =
      (path.measuredChain i certs).history k (n + 1) g' := by
    simpa only [path.viewAt_history i certs hl before (n + 1) k] using congrArg Fin.val h
  simpa only [path.viewAt_history i certs hl before n k] using
    (path.measuredChain i certs).history_nested k n g g' hn

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
