-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/FiniteCriticalSelection.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/FiniteCriticalSelection.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalTerminal
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalFiniteCap
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteInterceptSelection
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.TraversalSurvival

/-! The finite critical-rate argument with actual regularity tests, original
mass units, and an explicit occupied-pair budget. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

set_option linter.unusedVariables false

noncomputable section

open Finset Classical Set MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- A complete finite critical selection estimate. The constant is uniform in
all finite state spaces and meshes. No retained law is renormalized. -/
theorem finite_critical_heavy_intercept_uniform :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Ω Sf Sc Ar Iv Pal Tc Bin Cell : Type*) [Fintype Ω] [DecidableEq Sf]
      [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
      [Fintype Tc] [DecidableEq Tc] [DecidableEq Bin] [DecidableEq Cell]
      (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e) (hP1 : ∑ e, X.P e = 1)
      (prior : Bool → Ar → ℝ) (π : Pal → ℝ) (vel : Pal → ℝ)
      (I : Tc → Set ℝ) (center : Tc → ℝ)
      (d δt δx K E A r R Kp H lam V c B : ℝ)
      (hd : 0 < d) (hδt : 0 ≤ δt) (hδx : 0 ≤ δx) (hK : 2 ≤ K)
      (hE : 0 ≤ E) (hA : 0 ≤ A) (hbudget : E + 2 * K * δt + 6 * K * δx ≤ A)
      (hR : 0 < R) (herror : criticalPredictionError K A 3 + r ≤ R)
      (hKp : 0 < Kp) (hH : 0 < H) (hlam : 0 < lam) (hV : 0 ≤ V) (hB : 0 < B)
      (hπ : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z ≤ 1)
      (hmeas : ∀ t, MeasurableSet (I t))
      (hdisj : Pairwise (fun t u => Disjoint (I t) (I u)))
      (hvol : ∀ t, volume (I t) = ENNReal.ofReal d)
      (hunit : ∀ t, I t ⊆ Set.Icc (0 : ℝ) 1)
      (hnear : ∀ t s, s ∈ I t → |s - center t| ≤ δt)
      (hmargin : (2 * K)⁻¹ + 2 * δt ≤ K⁻¹) (hjitter : 20 * K ^ 2 * δt ≤ R)
      (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
        prior κ a * (H * d))
      (hpalette : ∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
        condKey X.P X.fine e er) ≤ Kp * π z)
      (hinterval : ∀ v, (∑ z ∈ univ.filter (fun z => |vel z - v| ≤ K⁻¹), π z) ≤ V)
      (hheavy : (∑ e, X.P e * (if X.heavy prior lam e false then 0 else 1)) ≤ c)
      (hloss : Kp * V + 2 * H * (K⁻¹ + δt) / lam + c ≤ 1 / 6)
      (D : FiniteHorizontalGeometry X vel center K E δx δt)
      (bin : Ω → Bin) (cell : Ω → Cell) (u : Cell → Fin 3 → ℝ)
      (hfine : ∀ e er, X.fine e = X.fine er → bin e = bin er)
      (hline : ∀ er e', X.armKey false er = X.armKey false e' → bin er = bin e')
      (F : Finset (Bin × Cell)) (hcard : (F.card : ℝ) ≤ B)
      (hsupport : ∀ e, 0 < X.P e → (bin e, cell e) ∈ F)
      (hspatial : ∀ e, 0 < X.P e → ∀ i, |D.point e i - u (cell e) i| ≤ r),
      ∃ b : Bin,
        1 / (4 * C * K ^ 24 * R ^ 3 * (Kp * H / lam) ^ 3 * B) ≤
          ∑ e ∈ univ.filter (fun e => bin e = b), X.P e := by
  obtain ⟨C, hC, hcritical⟩ := critical_finite_traversal_cell_cap_uniform
  refine ⟨C, hC, ?_⟩
  intro Ω Sf Sc Ar Iv Pal Tc Bin Cell _ _ _ _ _ _ _ _ _ _ _
    X hP hP1 prior π vel I center d δt δx K E A r R Kp H lam V c B
    hd hδt hδx hK hE hA hbudget hR herror hKp hH hlam hV hB hπ hπ1
    hmeas hdisj hvol hunit hnear hmargin hjitter hcell hpalette hinterval hheavy hloss
    D bin cell u hfine hline F hcard hsupport hspatial
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  let Q := CriticalTracking D A K⁻¹
  let G : Ω → Ω → List (Pal × Tc) → ℝ := fun s e l => if Q s e l then 1 else 0
  let allowed : Ω → Ω → List (Pal × Tc) → Ω → Ω → Prop := fun _ _ l er e' =>
    criticalFreshSeparated vel K⁻¹ l (X.Z er) ∧ criticalTimeSeparated center K⁻¹ l (X.cell e')
  let a := Kp * V
  let b := 2 * H * (K⁻¹ + δt) / lam
  have ha : 0 ≤ a := mul_nonneg hKp.le hV
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hG : ∀ s e l, 0 ≤ G s e l := by
    intro s e l
    dsimp [G]
    split_ifs <;> norm_num
  have hsurvival := finiteTraversalValue_average_survival X hP hP1 prior lam a b c ha hb Q
    (fun _ _ l er => criticalFreshSeparated vel K⁻¹ l (X.Z er))
    (fun _ _ l _ e' => criticalTimeSeparated center K⁻¹ l (X.cell e')) G
    (by intro s e l hq; simp [G, hq])
    (by
      intro s e l er e' hq hf _ hz hl ht
      exact criticalTracking_step hP D A K⁻¹ hK1 hE hδx hδt hA hbudget
        s e er e' l hq hf hl hz ht)
    (by
      intro s e l _
      exact criticalFreshSeparated_failure_le X π vel Kp K⁻¹ V hKp.le hV
        hpalette hinterval e l)
    (by
      intro s e l er _ _ hh _
      exact criticalTimeSeparated_failure_le X hP prior I center lam H d δt K⁻¹
        hlam hH.le hd hδt (inv_nonneg.mpr hK0.le) hmeas hdisj hvol hnear hcell er hh l)
    (fun s hs => criticalTracking_start D A K⁻¹ s hs) hheavy 3
  have hmass : (1 / 2 : ℝ) ≤ ∑ s, X.P s * finiteTraversalValue X prior lam (allowed s) (G s) 3 s [] := by
    have hs : 1 - (3 : ℝ) * (a + b + c) ≤
        ∑ s, X.P s * finiteTraversalValue X prior lam (allowed s) (G s) 3 s [] := hsurvival
    have hloss' : a + b + c ≤ 1 / 6 := hloss
    linarith only [hs, hloss']
  let p := C * K ^ 24 * R ^ 3 * (Kp * H / lam) ^ 3
  have hp : 0 < p := by dsimp [p]; positivity
  have hcap (s : Ω) (t : Cell) (hpos : 0 < X.P s) :
      finiteTraversalValue X prior lam (allowed s)
        (fun x l => if cell x = t then G s x l else 0) 3 s [] ≤ p := by
    have hq0 : |D.point s 0| ≤ K :=
      (abs_le.mpr ⟨by linarith [(D.point_time s hpos).1], (D.point_time s hpos).2⟩).trans hK1
    exact hcritical Ω Sf Sc Ar Iv Pal Tc X hP prior π vel I center d δt K R Kp H lam
      hd hδt hK hR.le hKp.le hH.le hlam hπ hπ1 hmeas hdisj hvol hunit D.center_time hnear
      hmargin hjitter hcell hpalette (D.point s) (u t) hq0 (D.point_horizontal s hpos)
      (allowed s) (fun x l => if cell x = t then G s x l else 0)
      (criticalReferenceTest vel center (D.point s) K⁻¹ R (u t))
      (criticalReferenceTest_nonneg vel center (D.point s) K⁻¹ R (u t))
      (fun e l => criticalTracking_terminal_le_reference D A K⁻¹ r R herror cell u hspatial s e l t)
      (criticalReferenceTest_three_le vel center (D.point s) K R (u t) D.control_bound) s
  have hsupportG : ∀ s e l, 0 < G s e l → (bin e, cell e) ∈ F := by
    intro s e l hg
    have hq : Q s e l := by
      by_contra hn
      simp only [G, hn, ite_false, lt_self_iff_false] at hg
    exact hsupport e hq.1
  obtain ⟨x, hx⟩ := finite_traversal_heavy_intercept_of_positive_cap X hP prior lam allowed G hG
    bin cell hfine hline F 3 p B (1 / 2) hp hB (by norm_num) hcard hmass hsupportG hcap
  refine ⟨x, ?_⟩
  convert hx using 1
  dsimp [p]
  field_simp
  ring

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
