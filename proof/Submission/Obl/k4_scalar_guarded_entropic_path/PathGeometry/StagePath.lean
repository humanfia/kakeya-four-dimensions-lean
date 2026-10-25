import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OuterStage

/-! An actual finite critical path with all outer controls fixed before
choosing any original inner sample, width loss or common residual. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Filter Set PathMeasures TrueLiftChains
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

structure StagePath (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (k : ℕ) (R δ : ℝ) where
  layout : StageLayout k R δ ctx.κ ctx.η
  path : TrueGridPath ctx source 0 layout.targets
  outer : ℕ
  certs : path.Certificates outer
  laws : path.forget.AllLayers outer
  final_length : (1 / 2 : ℝ) < L (path.forget.finalFamily.problem outer)
  controls : ∀ n : ℕ,
    ParentControl ctx (layout.scale * δ / 10000) (layout.scale * δ / 1000)
      (path.viewAt outer certs laws (.nil _ (source.angular outer).1) n).parent
  grids : ∀ n : ℕ,
    TrueGridPath.GridControl
      (path.viewAt outer certs laws (.nil _ (source.angular outer).1) n)
      ctx.κ (layout.scale * layout.mesh) 1 (layout.scale * δ / 10000)

theorem nonempty_stagePath {ctx : CriticalContext} (source : MaximizingFamily ctx)
    (hsource : source.length = 1) (hcalc : Calculus) (hκ : 0 < ctx.κ) (hη : 0 < ctx.η)
    (k : ℕ) {R δ : ℝ} (hR : 1 < R) (hδ : 0 < δ) :
    Nonempty (StagePath ctx source k R δ) := by
  obtain ⟨q⟩ := exists_stageLayout k hR hδ hκ hη
  obtain ⟨path⟩ := nonempty_trueGridPath hcalc ctx source 0 q.targets
    (by norm_num) q.targets_pairwise q.targets_mem
  have hscale := q.scale_pos
  have herror : 0 < q.scale * δ / 10000 := by positivity
  have hgain : 0 < q.scale * δ / 1000 := by positivity
  have hcert := path.eventually_certificates
  have hlaws := path.forget.eventually_allLayers
  have hlength := path.eventually_layout_final_length q hsource
  have hcontrol := path.eventually_viewAt_parentControl hcalc
    (q.scale * δ / 10000) (q.scale * δ / 1000) herror hgain
  have hgrid := path.eventually_viewAt_gridControl 1 (q.scale * q.mesh)
    (q.scale * δ / 10000) (by simpa only [sub_zero, one_mul] using hsource)
    q.targets_grid herror
  obtain ⟨i, hi, hl, hL, hc, hg⟩ :=
    (hcert.and (hlaws.and (hlength.and (hcontrol.and hgrid)))).exists
  obtain ⟨certs⟩ := hi
  exact ⟨
    { layout := q
      path := path
      outer := i
      certs := certs
      laws := hl
      final_length := hL
      controls := fun n => hc certs hl _ (.nil _ (source.angular i).1) n
      grids := fun n => hg certs hl _ (.nil _ (source.angular i).1) n }⟩

namespace StagePath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

def root (s : StagePath ctx source k R δ) : Code := source.problem s.outer
def final (s : StagePath ctx source k R δ) : Code := s.path.forget.finalFamily.problem s.outer

def view (s : StagePath ctx source k R δ) (n : ℕ) :
    OriginalView s.root s.final (ctx.D s.outer) ctx.S₀ ctx.η :=
  s.path.viewAt s.outer s.certs s.laws (.nil _ (source.angular s.outer).1) n

def views (s : StagePath ctx source k R δ) : Fin (s.layout.targets.length + 1) →
    OriginalView s.root s.final (ctx.D s.outer) ctx.S₀ ctx.η := fun a => s.view a.val

def candidate (s : StagePath ctx source k R δ) (a : Fin s.layout.L) :
    OriginalView s.root s.final (ctx.D s.outer) ctx.S₀ ctx.η := s.view (a.val + 1)

def candidateIndex (s : StagePath ctx source k R δ) (a : Fin s.layout.L) :
    Fin (s.layout.targets.length + 1) :=
  ⟨a.val + 1, by rw [s.layout.targets_length]; have ha := a.isLt; omega⟩

theorem views_candidateIndex (s : StagePath ctx source k R δ) (a : Fin s.layout.L) :
    s.views (s.candidateIndex a) = s.candidate a := rfl

theorem views_resolution (s : StagePath ctx source k R δ)
    (a : Fin (s.layout.targets.length + 1)) (j : ℕ) :
    N (s.views a).parent ((s.views a).suffixChain.sample j) = N s.final j :=
  ((s.views a).suffixChain.resolution j).symm

theorem views_resolution_code (s : StagePath ctx source k R δ)
    (a : Fin (s.layout.targets.length + 1)) (j : ℕ) :
    Code.N (s.views a).parent ((s.views a).suffixChain.sample j) = Code.N s.final j :=
  ((s.views a).suffixChain.resolution j).symm

theorem final_exact (s : StagePath ctx source k R δ) : Exact s.final :=
  (s.path.forget.finalFamily.angular s.outer).1

theorem view_length (s : StagePath ctx source k R δ) (n : ℕ) :
    (1 / 2 : ℝ) < L (s.view n).parent :=
  s.final_length.trans_le (s.path.viewAt_final_length_le s.outer s.certs s.laws _ n)

theorem view_count (s : StagePath ctx source k R δ) (n : ℕ) :
    (s.view n).count = s.layout.L + s.layout.C - n := by
  rw [view, s.path.viewAt_count, s.layout.targets_length]

theorem candidate_count (s : StagePath ctx source k R δ) (a : Fin s.layout.L) :
    s.layout.C ≤ (s.candidate a).count := by
  change s.layout.C ≤ (s.view (a.val + 1)).count
  rw [s.view_count]
  have ha := a.isLt
  omega

theorem view_positive_prefix (s : StagePath ctx source k R δ) {n : ℕ} (hn : 0 < n) :
    0 < (s.view n).prefixChain.length := by
  apply s.path.viewAt_positive_prefix s.outer s.certs s.laws _ hn
  rw [s.layout.targets_length]
  have hL := s.layout.L_pos
  omega

theorem view_absolute_profile (s : StagePath ctx source k R δ) {n : ℕ} (hn : 0 < n) :
    ∀ r, 0 ≤ r → r ≤ L (s.view n).parent →
      |f (s.view n).parent r - ctx.dstar * r| ≤ s.layout.scale * δ / 10000 :=
  (s.view n).absolute_profile_bound (s.controls n) (s.view_positive_prefix hn)

theorem views_referenceFactor (s : StagePath ctx source k R δ)
    (a : Fin (s.layout.targets.length + 1)) (j : ℕ) :
    (s.views a).suffixChain.referenceFactor j ≤ (s.path.measuredChain s.outer s.certs).referenceFactor j :=
  s.path.viewAt_referenceFactor_le s.outer s.certs s.laws _ a.val j

end StagePath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
