import Submission.Obl.k4_matching_abstract_switching_mixture.Covers

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Set MeasureTheory Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite
open Classical
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A deterministic cover and a successful finite experiment supply a single
separated control sequence with a quantitative endpoint-volume lower bound. -/
theorem PathCover.exists_control
    {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s t : Ω → ℝ}
    {m : ℕ} {K δ V rt L d lam q sb : ℝ} {a : Ω}
    (C : PathCover X s m K δ V a) (hK : 0 < K)
    (hP : ∀ e, 0 ≤ X.P e) (ha : 0 < X.P a)
    {g : Sf → Sc} (hcoarse : ∀ e, X.coarse e = g (X.fine e))
    (hival : ∀ x y, X.fine x = X.fine y → X.ival x = X.ival y)
    (π : Bool → Ar → ℝ) (hlam : 0 < lam) (hq : 0 ≤ q) (hsb : 0 ≤ sb)
    (hcell : ∀ c arm cell,
      fiberMass X.P (fun e => (X.arm e c, X.cell e)) (arm, cell) ≤ π c arm * (lam * q * d))
    (hfail : X.failBound π lam sb (m + 1) a ≤ 1 / 2)
    (hsep : ∀ n path er c, path.length + n + 1 ≤ m + 1 → X.heavy π lam er c →
      ∑ e, condKey X.P (X.armKey c) er e *
        (if separatedArrival t rt n path e then (0 : ℝ) else 1) ≤ sb)
    (I : Tc → Set ℝ) (hIm : ∀ c, MeasurableSet (I c))
    (hId : Pairwise (fun c c' => Disjoint (I c) (I c'))) (hd : 0 < d)
    (hIv : ∀ c, volume (I c) = ENNReal.ofReal d)
    (hshift : ∀ e f, s e - s f = t e - t f)
    (hunit : ∀ e, 0 < X.P e → X.ival e = X.ival a → ∀ y ∈ I (X.cell e), |y| ≤ 1)
    (hclose : ∀ e, 0 < X.P e → ∀ y ∈ I (X.cell e), |y - s e| ≤ d)
    (hdδ : d ≤ δ) (hmargin : L⁻¹ + 2 * d ≤ rt) :
    ∃ U : Fin (m + 1) → ℝ,
      (∀ p, |U p| ≤ K) ∧
      (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) ∧
      1 / 2 ≤ (Real.exp X.θ * q * (2 * K)) ^ (m + 1) *
        (volume (pullback L U (s a) C.T)).toReal := by
  let χ := adaptiveColor X K⁻¹
  let sep := separatedArrival t rt
  let Q := goodPath X t K⁻¹ rt
  let τ : Ω → List (Ω × Bool × Ω) → ℝ := fun _ _ => 1
  let τ' := pathTest X t K⁻¹ rt a
  let c : ℝ := Real.exp X.θ * ((lam * q * d) / lam)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hQ : ∀ n path er e', path.length + n + 1 ≤ m + 1 → Q a path →
      condKey X.P X.fine (curEvent a path) er ≠ 0 → X.good er →
      condKey X.P (X.armKey (χ a path er)) er e' ≠ 0 →
      X.heavy π lam er (χ a path er) → sep n path e' →
      Q a (path ++ [(er, χ a path er, e')]) := by
    intro n path er e' hlen hpath hf _ hk _ hs
    have hfe := condKey_key_eq (P := X.P) X.fine hf
    have hke := condKey_key_eq (P := X.P) (X.armKey (χ a path er)) hk
    have hmem : X.coarse er ∈ C.A := by
      have heq : X.coarse er = X.coarse (curEvent a path) := by
        rw [hcoarse, hcoarse, hfe]
      rw [heq]
      exact C.current_mem hpath.1 (by omega)
    apply goodPath_append X t K⁻¹ rt hpath er e' (χ a path er)
    · exact ⟨hfe, hke⟩
    · exact condKey_pos_of_ne hP X.fine hf
    · exact condKey_pos_of_ne hP (X.armKey (χ a path er)) hk
    · exact adaptiveColor_separated X K⁻¹ a path er
        (by simpa only [div_eq_mul_inv] using C.control_gap er hmem)
    · exact hs
  have hsuccess : 1 / 2 ≤ X.pathValue π lam χ sep Q τ (m + 1) a [] := by
    have h := X.one_sub_failBound_le_pathValue hP π lam hsb χ sep Q τ a (m + 1)
      (fun path hlen hpath => le_rfl) hQ hsep (m + 1) [] (by simp)
      (goodPath_nil X t K⁻¹ rt a) ha
    simp only [curEvent_nil] at h
    linarith
  have hdom : X.pathValue π lam χ sep Q τ (m + 1) a [] ≤
      X.freeBound c C.A τ' (m + 1) [] := by
    apply X.pathValue_le_freeBound hP hcoarse π hlam (by positivity) hcell χ sep Q τ a C.A τ'
      (pathTest_nonneg X t K⁻¹ rt a) (m + 1) ?_ ?_ (m + 1) [] (by simp)
      (goodPath_nil X t K⁻¹ rt a)
    · intro path hlen hpath
      change 1 ≤ pathTest X t K⁻¹ rt a (X.proj path)
      rw [pathTest_of_goodPath X t K⁻¹ rt a path hpath]
    · intro path hlen hpath
      exact C.current_mem hpath.1 (by omega)
  have hlow : 1 / 2 ≤ c ^ (m + 1) *
      ∑ cs : Fin (m + 1) → X.ctrlIdx C.A, (∏ p, X.idxWeight (cs p)) *
        timeSum τ' [] (fun p => X.idxCtrl (cs p)) := by
    rw [← X.freeBound_eq_sum c C.A τ' (m + 1) []]
    exact hsuccess.trans hdom
  let w : (Fin (m + 1) → X.ctrlIdx C.A) → ℝ := fun cs => ∏ p, X.idxWeight (cs p)
  let f : (Fin (m + 1) → X.ctrlIdx C.A) → ℝ :=
    fun cs => timeSum τ' [] (fun p => X.idxCtrl (cs p))
  have hw : ∀ cs, 0 ≤ w cs := fun cs => prod_nonneg fun p _ => X.condPal_nonneg hP _ _
  have hf : ∀ cs, 0 ≤ f cs := fun cs =>
    sum_nonneg fun ts _ => pathTest_nonneg X t K⁻¹ rt a _
  have hweight : ∑ cs, w cs ≤ (2 * K) ^ (m + 1) := by
    apply (X.sum_prod_idxWeight_le hP C.A (m + 1)).trans
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [C.card_bound]) _
  obtain ⟨cs, hpos, hlarge⟩ := exists_large_term w f hw hf (by norm_num : (0 : ℝ) < 1 / 2)
    (pow_nonneg hc _) (by positivity : 0 ≤ (2 * K) ^ (m + 1)) hweight hlow
  let U : Fin (m + 1) → ℝ := fun p => X.idxCtrl (cs p)
  obtain ⟨ts, l, hl, hproj⟩ := positive_timeSum_witness X t K⁻¹ rt a U hpos
  obtain ⟨hU, hUgap⟩ := C.projected_controls hl hproj
  have htime := C.timeSum_le I hIm hId hd hIv hival hshift hunit hclose hdδ hmargin U
  have hlarge' : 1 / 2 ≤ c ^ (m + 1) * (2 * K) ^ (m + 1) *
      ((volume (pullback L U (s a) C.T)).toReal / d ^ (m + 1)) :=
    hlarge.trans (mul_le_mul_of_nonneg_left htime (by positivity))
  have hceq : c = Real.exp X.θ * q * d := by
    dsimp [c]
    field_simp
  have heq : c ^ (m + 1) * (2 * K) ^ (m + 1) *
      ((volume (pullback L U (s a) C.T)).toReal / d ^ (m + 1)) =
      (Real.exp X.θ * q * (2 * K)) ^ (m + 1) *
        (volume (pullback L U (s a) C.T)).toReal := by
    rw [hceq, mul_pow, mul_pow]
    field_simp
    ring
  exact ⟨U, hU, hUgap, heq ▸ hlarge'⟩

end Submission.Obl.k4_matching_abstract_switching_mixture
