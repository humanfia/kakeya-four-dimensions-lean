/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathNodes.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_linear_critical_extremizers.ConcreteProfiles
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NestedNodes

/-!
Actual target depths on a buffered scalar critical sequence. The
accepted critical-extremizer interfaces are imported from o133.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The buffered uniform profile estimate gives the error/tilt limit
needed for actual minimizer depths. -/
theorem profileError_div_buffer_tendsto (p : ℕ → Code) (dstar : ℝ) (buffer : ℕ → ℝ)
    (hp : ∀ i, Exact (p i)) (hL : ∀ i, L (p i) = 1)
    (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1) (hb : ∀ i, 0 < buffer i)
    (hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ r ∈ Icc (0 : ℝ) 1,
      |f (p i) r - f (p i) 0 - dstar * r| ≤ ε * buffer i) :
    Tendsto (fun i => profileError (p i) dstar / buffer i) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le
      (div_nonneg (profileError_bounds (hp i) (hL i) hstar₀ hstar₁).1 (hb i).le)
  · intro b hb₀
    filter_upwards [hscaled (b / 2) (half_pos hb₀)] with i hi
    have hsup : profileError (p i) dstar ≤ b / 2 * buffer i := by
      apply csSup_le
      · exact ⟨0, 0, by norm_num, by simp⟩
      · rintro z ⟨r, hr, rfl⟩
        exact hi r hr
    have := (div_le_iff₀ (hb i)).2 hsup
    linarith

/-- Every fixed interior target has actual nearby endpoints with a
terminal cap strictly inside the available density buffer. -/
theorem exists_actual_critical_nodes (p : ℕ → Code) (dstar r : ℝ) (buffer : ℕ → ℝ)
    (hp : ∀ i, Exact (p i)) (hL : ∀ i, L (p i) = 1)
    (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r < 1) (hb : ∀ i, 0 < buffer i)
    (hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      |f (p i) s - f (p i) 0 - dstar * s| ≤ ε * buffer i) :
    ∃ depth : ℕ → ℝ,
      (∀ i, depth i ∈ Icc 0 r) ∧ Tendsto depth atTop (𝓝 r) ∧
      (∀ᶠ i in atTop, 0 < depth i) ∧
      (∀ i s, s ∈ Icc 0 (depth i) →
        f (p i) (depth i) - f (p i) s ≤
          (dstar + buffer i / 2) * (depth i - s)) ∧
      (∀ i, dstar + buffer i / 2 < dstar + buffer i) := by
  let err := fun i => profileError (p i) dstar
  let ε := fun i => buffer i / 2
  have hε (i : ℕ) : 0 < ε i := half_pos (hb i)
  have hratio : Tendsto (fun i => err i / ε i) atTop (𝓝 0) := by
    have ht := (profileError_div_buffer_tendsto p dstar buffer hp hL hstar₀ hstar₁ hb hscaled).const_mul 2
    convert ht using 1
    · ext i
      dsimp only [err, ε]
      field_simp
    · norm_num
  have hcont (i : ℕ) : ContinuousOn (f (p i)) (Icc 0 r) := by
    apply (profile_lipschitzOn (L := (1 : ℝ)) ?_).continuousOn.mono
      (fun _ hs => ⟨hs.1, hs.2.trans hr₁.le⟩)
    intro x y hx hxy hy
    exact exact_profile_regular (hp i) x y hx hxy (by simpa only [hL i] using hy)
  obtain ⟨depth, hdepth, hcap, hlim⟩ := exists_tilted_nodes_tendsto
    (fun i => f (p i)) dstar r err ε hr₀.le hcont hε
    (fun i s hs => (profileError_bounds (hp i) (hL i) hstar₀ hstar₁).2 s
      ⟨hs.1, hs.2.trans hr₁.le⟩) hratio
  refine ⟨depth, hdepth, hlim, ?_, hcap, ?_⟩
  · exact tendsto_const_nhds.eventually_lt hlim hr₀
  · intro i
    linarith [hb i]

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
