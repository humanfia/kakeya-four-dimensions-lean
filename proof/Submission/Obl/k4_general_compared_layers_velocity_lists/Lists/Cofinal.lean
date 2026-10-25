-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Cofinal; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Reindex
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.Interface
namespace Submission.Obl.k4_general_compared_layers_velocity_lists
open Filter
noncomputable section
namespace Parent
variable {α : Type} [MeasurableSpace α]
def ListFrame.fromReindex (p : Parent α) {τ : ℕ → ℕ} {k : ℕ} {r v m ε : ℝ}
    (f : (p.reindex τ).ListFrame k r v m ε) : p.ListFrame (τ k) r v m ε :=
  { f with }
/-- An original frame at the selected index is the same normalized frame
for the reindexed parent. -/
def ListFrame.toReindex (p : Parent α) {τ : ℕ → ℕ} {k : ℕ} {r v m ε : ℝ}
    (f : p.ListFrame (τ k) r v m ε) : (p.reindex τ).ListFrame k r v m ε :=
  { f with }

theorem DeepConfinement.reindex {p : Parent α} {τ : ℕ → ℕ}
    {r v m : ℝ} (hconf : p.DeepConfinement r v m) (hτ : Tendsto τ atTop atTop) :
    (p.reindex τ).DeepConfinement r v m := by
  obtain ⟨t, ε₀, htr, htU, hε₀, hc⟩ := hconf
  refine ⟨t, ε₀, htr, htU, hε₀, ?_⟩
  intro ε hε hεε₀
  filter_upwards [hτ.eventually (hc ε hε hεε₀)] with k hk
  intro f
  exact hk (ListFrame.fromReindex p f)
end Parent
end
end Submission.Obl.k4_general_compared_layers_velocity_lists
