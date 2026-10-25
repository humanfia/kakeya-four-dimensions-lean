import Mathlib
import Submission.Lib.K4QuadraticSheets

/-!
# Real tests, their discriminant polynomials, and sheets along safe paths

Real quadratic tests `P : MvPolynomial (Fin 4) ℝ` act on `ℂ³ × ℂ` through
`P.map (algebraMap ℝ ℂ)`.  Their discriminant polynomial in the three base variables,
`discPoly P` (substitute `w = 0` in `P_w² - 2 P_ww P`), evaluates at every complex point to the
discriminant `qdisc` of the complexified test.  So a lower bound for `discPoly P` on the tube of a
broken segment, together with a Lipschitz bound for it there, gives an analytic simple sheet of the
complexified test on a thinner tube.
-/

namespace Submission.Lib.K4QuadraticSheetsReal

open Submission.Lib.K4QuadraticSheets

open MvPolynomial

/-- The discriminant polynomial of a real test in its three base variables. -/
noncomputable def discPoly (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) MvPolynomial.X)
    ((MvPolynomial.pderiv (3 : Fin 4) P) ^ 2 -
      2 * MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P) * P)

theorem eval_map_lastCases_subst (Q : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℂ) :
    MvPolynomial.eval z ((MvPolynomial.eval₂Hom MvPolynomial.C
      (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) MvPolynomial.X) Q).map (algebraMap ℝ ℂ)) =
    MvPolynomial.eval (Fin.snoc z 0 : Fin 4 → ℂ) (Q.map (algebraMap ℝ ℂ)) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  rw [MvPolynomial.coe_eval₂Hom]
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X, hp]
    congr 1
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last, Fin.snoc_last]
      simp
    · rw [Fin.lastCases_castSucc, Fin.snoc_castSucc]
      simp

theorem totalDegree_map_le' {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (P : MvPolynomial σ R) : (P.map φ).totalDegree ≤ P.totalDegree := by
  classical
  apply Finset.sup_mono
  exact MvPolynomial.support_map_subset φ P

theorem map_algebraMap_ne_zero {σ : Type*} {P : MvPolynomial σ ℝ} (hP : P ≠ 0) :
    P.map (algebraMap ℝ ℂ) ≠ 0 := by
  intro h
  apply hP
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  rw [h, map_zero]

/-- The discriminant polynomial evaluates to the discriminant of the complexified test. -/
theorem eval_map_discPoly {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) :
    MvPolynomial.eval z ((discPoly P).map (algebraMap ℝ ℂ)) =
      qdisc (P.map (algebraMap ℝ ℂ)) z := by
  have hP' : (P.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 := (totalDegree_map_le' _ P).trans hP
  rw [discPoly, eval_map_lastCases_subst]
  have h3 : (3 : Fin 4) = Fin.last 3 := rfl
  simp only [map_sub, map_mul, map_pow, map_ofNat, h3, ← MvPolynomial.pderiv_map]
  rw [eval_pderiv2_eq_qc _ hP']
  rfl

/-- A real test evaluated at a real point, complexified. -/
theorem eval_map_real {σ : Type*} (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (P.map (algebraMap ℝ ℂ)) = ((MvPolynomial.eval x P : ℝ) : ℂ) := by
  rw [MvPolynomial.eval_map]
  have h := MvPolynomial.eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ) x P
  rw [RingHom.comp_id] at h
  exact h.symm

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- **A simple sheet along a safe broken path.**  If the discriminant polynomial of a real test is
at least `m` on the `r`-tube of a broken segment in the unit ball, and `L`-Lipschitz there, then
on any thinner `r'`-tube with `2 L r' (1 + 2 / r) ^ 2 < m` the complexified test has an analytic
square root of its discriminant (and hence a simple analytic sheet). -/
theorem exists_sqrt_on_safe_path {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (a b c : E3) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) {r r' m L : ℝ}
    (hr : 0 < r) (hm : 0 < m) (hr' : 0 < r') (hr'r : r' ≤ r) (hL : 0 ≤ L)
    (hdisc : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      m ≤ ‖MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ))‖)
    (hLip : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ∀ z' ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ‖MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ)) -
        MvPolynomial.eval (fun i => z' i) ((discPoly P).map (algebraMap ℝ ℂ))‖ ≤ L * ‖z - z'‖)
    (hsmall : L * r' * (2 * (1 + 2 / r) ^ 2) < m) :
    ∃ S : E3 → ℂ,
      AnalyticOnNhd ℂ S (Metric.thickening r' (segment ℝ a b ∪ segment ℝ b c)) ∧
      ∀ z ∈ Metric.thickening r' (segment ℝ a b ∪ segment ℝ b c),
        S z ^ 2 = qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) ∧
        qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) ≠ 0 := by
  have hq : ∀ z : E3, MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ)) =
      qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) := fun z => eval_map_discPoly hP _
  have hdisc' : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      m ≤ ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j)‖ := fun z hz => by
    rw [← hq]; exact hdisc z hz
  have hLip' : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ∀ z' ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) -
        qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z' j)‖ ≤ L * ‖z - z'‖ := fun z hz z' hz' => by
    rw [← hq, ← hq]; exact hLip z hz z' hz'
  have hseg : ∀ (u v : E3), segment ℝ u v ⊆ segment ℝ a b ∪ segment ℝ b c →
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∃ S : E3 → ℂ, AnalyticOnNhd ℂ S (Metric.thickening r' (segment ℝ u v)) ∧
        ∀ z ∈ Metric.thickening r' (segment ℝ u v),
          S z ^ 2 = qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) ∧
            qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) ≠ 0 := by
    intro u v huv hu hv
    have hsub : ∀ ρ, Metric.thickening ρ (segment ℝ u v) ⊆
        Metric.thickening ρ (segment ℝ a b ∪ segment ℝ b c) :=
      fun ρ => Metric.thickening_subset_of_subset ρ huv
    have hnorm : ‖v - u‖ ≤ 2 := by
      calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    have hfac : 2 * (1 + ‖v - u‖ / r) ^ 2 ≤ 2 * (1 + 2 / r) ^ 2 := by
      have : ‖v - u‖ / r ≤ 2 / r := div_le_div_of_nonneg_right hnorm hr.le
      have h0 : 0 ≤ ‖v - u‖ / r := by positivity
      nlinarith
    have hpert : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : E3, dist z (u + s • (v - u)) < r' →
        ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) -
          qdisc (P.map (algebraMap ℝ ℂ)) (fun j => (u + s • (v - u)) j)‖ *
          (2 * (1 + ‖v - u‖ / r) ^ 2) < m := by
      intro s hs z hz
      have hpt : u + s • (v - u) ∈ segment ℝ u v := by
        rw [segment_eq_image']; exact ⟨s, hs, rfl⟩
      have h1 : u + s • (v - u) ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c) :=
        hsub r (Metric.self_subset_thickening hr _ hpt)
      have h2 : z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c) := by
        apply hsub r
        rw [Metric.mem_thickening_iff]
        exact ⟨_, hpt, lt_of_lt_of_le hz hr'r⟩
      have hlip := hLip' z h2 _ h1
      have hdist : ‖z - (u + s • (v - u))‖ < r' := by rw [← dist_eq_norm]; exact hz
      calc ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) -
            qdisc (P.map (algebraMap ℝ ℂ)) (fun j => (u + s • (v - u)) j)‖ *
            (2 * (1 + ‖v - u‖ / r) ^ 2)
          ≤ (L * r') * (2 * (1 + 2 / r) ^ 2) := by
            apply mul_le_mul _ hfac (by positivity) (by positivity)
            exact hlip.trans (mul_le_mul_of_nonneg_left hdist.le hL)
        _ < m := hsmall
    exact exists_sqrt_on_segment_tube' (P := P.map (algebraMap ℝ ℂ))
      ((totalDegree_map_le' _ P).trans hP) u v hr hm
      (fun z hz => hdisc' z (hsub r hz)) hpert
  obtain ⟨S₁, hS₁⟩ := hseg a b Set.subset_union_left ha hb
  obtain ⟨S₂, hS₂⟩ := hseg b c Set.subset_union_right hb hc
  exact exists_sqrt_on_broken_tube a b c hr' S₁ S₂ hS₁ hS₂

end Submission.Lib.K4QuadraticSheetsReal

namespace Submission.Lib.K4QuadraticSheetsReal

open Submission.Lib.K4QuadraticSheets

open MvPolynomial

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- A Lipschitz bound and a lower bound for the discriminant on a tube keep it within its own
size on the ball of radius `A⁻¹` around the end of the segment. -/
theorem qdisc_pert_end {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) (a b c : E3)
    {r m L A : ℝ} (hA : 0 < A) (hAr : A⁻¹ ≤ r)
    (hdisc : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      m ≤ ‖MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ))‖)
    (hLip : ∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ∀ z' ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
      ‖MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ)) -
        MvPolynomial.eval (fun i => z' i) ((discPoly P).map (algebraMap ℝ ℂ))‖ ≤ L * ‖z - z'‖)
    (hL : 0 ≤ L) (hsmall : L * A⁻¹ < m) :
    ∀ z ∈ Metric.ball c (A⁻¹),
      ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) -
        qdisc (P.map (algebraMap ℝ ℂ)) (fun j => c j)‖ <
          ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun j => c j)‖ := by
  intro z hz
  have hq : ∀ z : E3, MvPolynomial.eval (fun i => z i) ((discPoly P).map (algebraMap ℝ ℂ)) =
      qdisc (P.map (algebraMap ℝ ℂ)) (fun j => z j) := fun z => eval_map_discPoly hP _
  have hcT : c ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨c, Or.inr (right_mem_segment ℝ b c), by simpa using lt_of_lt_of_le (inv_pos.mpr hA) hAr⟩
  have hzT : z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨c, Or.inr (right_mem_segment ℝ b c), lt_of_lt_of_le (Metric.mem_ball.mp hz) hAr⟩
  have h1 := hLip z hzT c hcT
  have h2 := hdisc c hcT
  rw [hq, hq] at h1
  rw [hq] at h2
  have hzc : ‖z - c‖ < A⁻¹ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  calc _ ≤ L * ‖z - c‖ := h1
    _ ≤ L * A⁻¹ := mul_le_mul_of_nonneg_left hzc.le hL
    _ < m := hsmall
    _ ≤ _ := h2

/-- **Forward transport along a safe path, for real tests.**  For real source and witness tests
whose discriminant polynomials are at least `m` and `L`-Lipschitz on the `r`-tube of a broken
segment in the unit ball, local root branches agreeing to `V` near the start continue so that the
source's jets at the end are within `A ^ C * V` of those of a canonical witness branch there. -/
theorem anchor_forward_safe (hC : ContInput) (s : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : E3,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P P' : MvPolynomial (Fin 4) ℝ),
      P.totalDegree ≤ 2 → P ≠ 0 → P'.totalDegree ≤ 2 → P' ≠ 0 →
      ∀ r m L : ℝ, 0 < r → 0 < m → 0 ≤ L → A⁻¹ ≤ r →
      L * A⁻¹ * (2 * (1 + 2 / r) ^ 2) < m →
      (∀ R : MvPolynomial (Fin 4) ℝ, R = P ∨ R = P' →
        (∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
          m ≤ ‖MvPolynomial.eval (fun i => z i) ((discPoly R).map (algebraMap ℝ ℂ))‖) ∧
        (∀ z ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
          ∀ z' ∈ Metric.thickening r (segment ℝ a b ∪ segment ℝ b c),
          ‖MvPolynomial.eval (fun i => z i) ((discPoly R).map (algebraMap ℝ ℂ)) -
            MvPolynomial.eval (fun i => z' i) ((discPoly R).map (algebraMap ℝ ℂ))‖ ≤
              L * ‖z - z'‖)) →
      ∀ (f₀ f'₀ : E3 → ℂ),
      ContinuousOn f₀ (Metric.ball a (A⁻¹)) → ContinuousOn f'₀ (Metric.ball a (A⁻¹)) →
      (∀ z ∈ Metric.ball a (A⁻¹),
        eval (Fin.snoc (fun j : Fin 3 => z j) (f₀ z) : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ)) = 0 ∧
        eval (Fin.snoc (fun j : Fin 3 => z j) (f'₀ z) : Fin 4 → ℂ)
          (P'.map (algebraMap ℝ ℂ)) = 0) →
      ∀ V : ℝ, 0 ≤ V → (∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖f₀ z - f'₀ z‖ ≤ V) →
      ∃ f : E3 → ℂ, SimpleSheet (P.map (algebraMap ℝ ℂ)) f
          (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) ∧
        AnalyticOnNhd ℂ f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) ∧
        (∀ z ∈ Metric.ball a (A⁻¹), f z = f₀ z) ∧
        ∃ ε : Bool, ∀ j : ℕ, j ≤ q →
          ‖iteratedFDeriv ℂ j f c -
            iteratedFDeriv ℂ j (canonBranch (P'.map (algebraMap ℝ ℂ)) c ε) c‖ ≤ A ^ C * V := by
  obtain ⟨q, C, hsq, hC0, hmain⟩ := anchor_forward hC s
  refine ⟨q, C, hsq, hC0, ?_⟩
  intro A hA a b c ha hb hc P P' hP hP0 hP' hP'0 r m L hr hm hL hAr hsmall hRs f₀ f'₀ hf₀c hf'₀c
    hroots V hV hclose
  have hApos : 0 < A := by linarith
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hApos
  obtain ⟨hdP, hLP⟩ := hRs P (Or.inl rfl)
  obtain ⟨hdP', hLP'⟩ := hRs P' (Or.inr rfl)
  obtain ⟨S, hSa, hS⟩ := exists_sqrt_on_safe_path hP a b c ha hb hc hr hm hAinv hAr hL hdP hLP
    hsmall
  obtain ⟨S', hS'a, hS'⟩ := exists_sqrt_on_safe_path hP' a b c ha hb hc hr hm hAinv hAr hL hdP'
    hLP' hsmall
  have hfac : 1 ≤ 2 * (1 + 2 / r) ^ 2 := by
    have : 0 ≤ 2 / r := by positivity
    nlinarith
  have hsmall' : L * A⁻¹ < m := by
    have h0 : 0 ≤ L * A⁻¹ := by positivity
    nlinarith
  have hpert := qdisc_pert_end hP' a b c hApos hAr hdP' hLP' hL hsmall'
  exact hmain A hA a b c ha hb hc _ _ ((totalDegree_map_le' _ P).trans hP)
    (map_algebraMap_ne_zero hP0) ((totalDegree_map_le' _ P').trans hP')
    (map_algebraMap_ne_zero hP'0) S S' hSa hS hS'a hS' hpert f₀ f'₀ hf₀c hf'₀c hroots V hV hclose

end Submission.Lib.K4QuadraticSheetsReal

namespace Submission.Lib.K4QuadraticSheetsReal

open Submission.Lib.K4QuadraticSheets

open MvPolynomial

theorem snoc_ofReal (z : Fin 3 → ℝ) (w : ℝ) :
    (fun i => ((Fin.snoc z w : Fin 4 → ℝ) i : ℂ)) =
      (Fin.snoc (fun j => (z j : ℂ)) (w : ℂ) : Fin 4 → ℂ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- **A real test near a sheet.**  If a real point `(z, w)` lies within `η` of a (complex) sheet
value `fz` over the same base point, a real test and its hidden derivative at `(z, w)` are bounded
by their values on the sheet up to `η` times the derivative and the curvature. -/
theorem test_near_sheet {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) (z : Fin 3 → ℝ)
    (w : ℝ) (fz : ℂ) {η V₁ V₂ : ℝ} (hw : ‖(w : ℂ) - fz‖ ≤ η)
    (h₁ : ‖eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ))‖ ≤ V₁)
    (h₂ : ‖eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
      ((pderiv (Fin.last 3) P).map (algebraMap ℝ ℂ))‖ ≤ V₂) :
    |eval (Fin.snoc z w : Fin 4 → ℝ) P| ≤
        V₁ + η * V₂ + ‖qc (P.map (algebraMap ℝ ℂ))‖ / 2 * η ^ 2 ∧
      |eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (Fin.last 3) P)| ≤
        V₂ + ‖qc (P.map (algebraMap ℝ ℂ))‖ * η := by
  have hP' : (P.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 := (totalDegree_map_le' _ P).trans hP
  have hη : 0 ≤ η := (norm_nonneg _).trans hw
  set c := qc (P.map (algebraMap ℝ ℂ))
  have hval : ((eval (Fin.snoc z w : Fin 4 → ℝ) P : ℝ) : ℂ) =
      eval (Fin.snoc (fun j => (z j : ℂ)) (w : ℂ) : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ)) := by
    rw [← eval_map_real, snoc_ofReal]
  have hder : ((eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (Fin.last 3) P) : ℝ) : ℂ) =
      eval (Fin.snoc (fun j => (z j : ℂ)) (w : ℂ) : Fin 4 → ℂ)
        (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))) := by
    rw [MvPolynomial.pderiv_map, ← eval_map_real, snoc_ofReal]
  have hid := eval_snoc_sub_eval_snoc hP' (fun j => (z j : ℂ)) (w : ℂ) fz
  have hd1 : eval (Fin.snoc (fun j => (z j : ℂ)) (w : ℂ) : Fin 4 → ℂ)
        (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))) =
      eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
        (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))) + c * ((w : ℂ) - fz) := by
    rw [eval_snoc_pderiv _ hP', eval_snoc_pderiv _ hP']
    ring
  rw [← MvPolynomial.pderiv_map] at h₂
  constructor
  · rw [← Real.norm_eq_abs, ← Complex.norm_real, hval]
    have : eval (Fin.snoc (fun j => (z j : ℂ)) (w : ℂ) : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ)) =
        eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ)) +
          ((w : ℂ) - fz) * (eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
            (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))) + c / 2 * ((w : ℂ) - fz)) := by
      rw [← hid]; ring
    rw [this]
    calc _ ≤ ‖eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ) (P.map (algebraMap ℝ ℂ))‖ +
          ‖((w : ℂ) - fz) * (eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
            (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ))) + c / 2 * ((w : ℂ) - fz))‖ :=
          norm_add_le _ _
      _ ≤ V₁ + η * (V₂ + ‖c‖ / 2 * η) := by
          gcongr
          rw [norm_mul]
          apply mul_le_mul hw _ (norm_nonneg _) hη
          calc _ ≤ ‖eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
                (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ + ‖c / 2 * ((w : ℂ) - fz)‖ :=
                norm_add_le _ _
            _ ≤ V₂ + ‖c‖ / 2 * η := by
                gcongr
                rw [norm_mul, norm_div]
                simp only [Complex.norm_ofNat]
                exact mul_le_mul_of_nonneg_left hw (by positivity)
      _ = V₁ + η * V₂ + ‖c‖ / 2 * η ^ 2 := by ring
  · rw [← Real.norm_eq_abs, ← Complex.norm_real, hder, hd1]
    calc _ ≤ ‖eval (Fin.snoc (fun j => (z j : ℂ)) fz : Fin 4 → ℂ)
          (pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ + ‖c * ((w : ℂ) - fz)‖ :=
          norm_add_le _ _
      _ ≤ V₂ + ‖c‖ * η := by
          gcongr
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)

end Submission.Lib.K4QuadraticSheetsReal
